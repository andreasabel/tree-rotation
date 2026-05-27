{-# LANGUAGE DerivingStrategies #-}

module Main (main) where

import DFS qualified
import Full.Search qualified as FullSearch
import Game
  ( Board
  , LeafCount
  , MoveTrail
  , applyMoveTrail
  , parseMoveTrail
  , startBoard
  )
import MCTS qualified
import Options.Applicative
import Plot (printScorePlot)
import Random qualified
import Search qualified
import System.Exit (die)

-- | Output CSV file path.
type OutputPath = FilePath

-- | Command line options that control program execution.
data CommandLineOptions = CommandLineOptions
  { optionsVerbose :: !Bool
    -- ^ Print improving leaders when 'True'.
  , optionsOutputPath :: !OutputPath
    -- ^ CSV file used for winner output and plot input.
  , optionsStart :: !(Maybe LeafCount)
    -- ^ Optional starting value of @N@ for the infinite solving loop.
  , optionsInit :: !(Maybe String)
    -- ^ Optional single-tree move prefix applied before the search starts.
  , optionsPlot :: !Bool
    -- ^ Print an SVG plot from the CSV file instead of running the solver.
  , optionsFull :: !Bool
    -- ^ Run the multi-tree game when 'True'.
  , optionsSingleTreeSearch :: !SingleTreeSearchMode
    -- ^ Search algorithm used for the single-tree game.
  }

-- | Search algorithm available for the single-tree game.
data SingleTreeSearchMode
  = ExactSearch
  -- ^ Explore the full game graph exactly.
  | DfsSearch
  -- ^ Explore the game with plain depth-first search.
  | RandomSearch Random.SimulationCount
  -- ^ Sample many random games and keep the best.
  | MctsSearch MCTS.SimulationCount
  -- ^ Use Monte Carlo Tree Search to choose each move.
  deriving stock (Eq, Show)

-- | Parse command line options and either solve games or print a plot.
main :: IO ()
main = do
  options <- execParser commandLineParserInfo
  if optionsPlot options
    then printScorePlot (optionsOutputPath options)
    else do
      rejectIncompatibleOptions options
      mapM_ (runSingleGame options) [resolvedStart options ..]

-- | Run one game, print its winner, and append the result to CSV.
--
-- Precondition: the leaf count is non-negative.
-- Postcondition: exactly one CSV row for the finished game has been appended.
runSingleGame :: CommandLineOptions -> LeafCount -> IO ()
runSingleGame options leafCount = do
  if optionsFull options
    then do
      winner <-
        FullSearch.solveGame
          FullSearch.SearchOptions {FullSearch.searchVerbose = optionsVerbose options}
          leafCount
      putStrLn ("winner " <> FullSearch.formatWinnerSummary leafCount winner)
      FullSearch.appendWinnerCsv (optionsOutputPath options) leafCount winner
    else do
      winner <- solveSingleTreeGame options leafCount
      putStrLn ("winner " <> Search.formatWinnerSummary leafCount winner)
      Search.appendWinnerCsv (optionsOutputPath options) leafCount winner

-- | Solve one single-tree game instance with the configured search method.
solveSingleTreeGame :: CommandLineOptions -> LeafCount -> IO Search.Winner
solveSingleTreeGame options leafCount = do
  (initialBoard, initialMoves) <- resolveSingleTreeStart options leafCount
  case optionsSingleTreeSearch options of
    ExactSearch ->
      Search.solveFrom
        Search.SearchOptions {Search.searchVerbose = optionsVerbose options}
        leafCount
        initialBoard
        initialMoves
    DfsSearch ->
      DFS.solveFrom
        Search.SearchOptions {Search.searchVerbose = optionsVerbose options}
        leafCount
        initialBoard
        initialMoves
    RandomSearch sampleCount ->
      Random.solveFrom
        Search.SearchOptions {Search.searchVerbose = optionsVerbose options}
        sampleCount
        leafCount
        initialBoard
        initialMoves
    MctsSearch simulationCount ->
      MCTS.solveFrom
        Search.SearchOptions {Search.searchVerbose = optionsVerbose options}
        simulationCount
        leafCount
        initialBoard
        initialMoves

-- | Resolve the actual single-tree board and move trail used to start one run.
--
-- Postcondition: throws a user-facing error when the requested initial move
-- sequence is syntactically invalid or illegal for the chosen @N@.
resolveSingleTreeStart :: CommandLineOptions -> LeafCount -> IO (Board, MoveTrail)
resolveSingleTreeStart options leafCount =
  case optionsInit options of
    Nothing -> pure (startBoard leafCount, [])
    Just movesText ->
      case parseMoveTrail movesText of
        Nothing ->
          die ("Invalid --init move sequence: " <> show movesText)
        Just moveTrail ->
          case applyMoveTrail moveTrail (startBoard leafCount) of
            Nothing ->
              die
                ( "Illegal --init move sequence for N="
                    <> show leafCount
                    <> ": "
                    <> show movesText
                )
            Just initialBoard ->
              pure (initialBoard, moveTrail)

-- | Resolve the default starting value for the selected game mode.
resolvedStart :: CommandLineOptions -> LeafCount
resolvedStart options =
  case optionsStart options of
    Just leafCount -> leafCount
    Nothing
      | optionsFull options -> 3
      | otherwise -> 1

-- | Reject combinations that are not supported by the solver.
rejectIncompatibleOptions :: CommandLineOptions -> IO ()
rejectIncompatibleOptions options
  | optionsFull options
      && optionsSingleTreeSearch options /= ExactSearch =
      die "--dfs, --random, and --mcts are only available for the default game."
  | optionsFull options
      && optionsInit options /= Nothing =
      die "--init is only available for the single-tree game."
  | otherwise = pure ()

-- | Parser for all supported command line options.
commandLineParser :: Parser CommandLineOptions
commandLineParser =
  CommandLineOptions
    <$> switch
      ( long "verbose"
          <> help "Print each new highscore during the search, in addition to the final winner."
      )
    <*> strOption
      ( long "output"
          <> short 'o'
          <> metavar "FILE"
          <> value "score.csv"
          <> showDefault
          <> help "Append final winners to FILE, or read FILE when --plot is used."
      )
    <*> optional
      ( option auto
          ( long "start"
              <> metavar "N"
              <> help "Start solving at N. Defaults to 1, or 3 with --full."
          )
      )
    <*> optional
      ( strOption
          ( long "init"
              <> metavar "MOVES"
              <> help "Start the single-tree game search from the given move prefix."
          )
      )
    <*> switch
      ( long "plot"
          <> help "Read the CSV file and print an SVG plot of N versus high-score."
      )
    <*> switch
      ( long "full"
          <> help "Run the multi-tree game."
      )
    <*> singleTreeSearchParser

-- | Parser for the single-tree game search method.
singleTreeSearchParser :: Parser SingleTreeSearchMode
singleTreeSearchParser =
  dfsParser <|> randomParser <|> mctsParser <|> pure ExactSearch
  where
    dfsParser =
      flag'
        DfsSearch
        ( long "dfs"
            <> help "Use plain depth-first search."
        )
    randomParser =
      flag'
        (RandomSearch Random.defaultRandomGames)
        ( long "random"
            <> help
              (unwords ["Use repeated random playouts; defaults to", show Random.defaultRandomGames, "samples."])
        )
        <|> ( RandomSearch
                <$> option auto
                  ( long "random"
                      <> metavar "NNN"
                      <> help "Use repeated random playouts with NNN samples."
                  )
            )
    mctsParser =
      flag'
        (MctsSearch MCTS.defaultMctsSimulations)
        ( long "mcts"
            <> help
              ( unwords ["Use Monte Carlo Tree Search for the single-tree game; defaults to", show MCTS.defaultMctsSimulations, "simulations per move."])
        )
        <|> ( MctsSearch
                <$> option auto
                  ( long "mcts"
                      <> metavar "NNN"
                      <> help "Use Monte Carlo Tree Search with NNN simulations per move."
                  )
            )

-- | Parser metadata used by 'execParser'.
commandLineParserInfo :: ParserInfo CommandLineOptions
commandLineParserInfo =
  info
    (commandLineParser <**> helper)
    ( fullDesc
        <> progDesc
         "Compute puzzle highscores by breadth-first search; use --init for a single-tree move prefix, --dfs, --random, or --mcts for alternative search modes, use --full for the extended multi-tree game, or render a score plot."
    )
