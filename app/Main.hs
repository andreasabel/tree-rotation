{-# LANGUAGE DerivingStrategies #-}

module Main (main) where

import Full.Search qualified as FullSearch
import MCTS qualified
import Options.Applicative
import Plot (printScorePlot)
import Random qualified
import Search qualified

-- | Number of initial moves or leaves for one game, depending on the mode.
type LeafCount = Int

-- | Output CSV file path.
type OutputPath = FilePath

-- | Command line options that control program execution.
data CommandLineOptions = CommandLineOptions
  { optionsVerbose :: Bool
    -- ^ Print improving leaders when 'True'.
  , optionsOutputPath :: OutputPath
    -- ^ CSV file used for winner output and plot input.
  , optionsStart :: Maybe LeafCount
    -- ^ Optional starting value of @N@ for the infinite solving loop.
  , optionsPlot :: Bool
    -- ^ Print an SVG plot from the CSV file instead of running the solver.
  , optionsFull :: Bool
    -- ^ Run the original full game when 'True'.
  , optionsReducedSearch :: ReducedSearchMode
    -- ^ Search algorithm used for the reduced game.
  }

-- | Search algorithm available for the reduced default game.
data ReducedSearchMode
  = ExactSearch
  -- ^ Explore the full game graph exactly.
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
      winner <- solveReducedGame options leafCount
      putStrLn ("winner " <> Search.formatWinnerSummary leafCount winner)
      Search.appendWinnerCsv (optionsOutputPath options) leafCount winner

-- | Solve one reduced-game instance with the configured search method.
solveReducedGame :: CommandLineOptions -> LeafCount -> IO Search.Winner
solveReducedGame options leafCount =
  case optionsReducedSearch options of
    ExactSearch ->
      Search.solveGame
        Search.SearchOptions {Search.searchVerbose = optionsVerbose options}
        leafCount
    RandomSearch sampleCount ->
      Random.solveGame
        Search.SearchOptions {Search.searchVerbose = optionsVerbose options}
        sampleCount
        leafCount
    MctsSearch simulationCount ->
      MCTS.solveGame
        Search.SearchOptions {Search.searchVerbose = optionsVerbose options}
        simulationCount
        leafCount

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
      && optionsReducedSearch options /= ExactSearch =
      ioError
        ( userError
            "--random and --mcts are only available for the reduced default game."
        )
  | otherwise = pure ()

-- | Parser for all supported command line options.
commandLineParser :: Parser CommandLineOptions
commandLineParser =
  CommandLineOptions
    <$> switch
      ( long "verbose"
          <> help "Print each improving leader during the search."
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
    <*> switch
      ( long "plot"
          <> help "Read the CSV file and print an SVG plot of N versus high-score."
      )
    <*> switch
      ( long "full"
          <> help "Run the original full game with indexed board moves."
      )
    <*> reducedSearchParser

-- | Parser for the reduced-game search method.
reducedSearchParser :: Parser ReducedSearchMode
reducedSearchParser =
  randomParser <|> mctsParser <|> pure ExactSearch
  where
    randomParser =
      flag'
        (RandomSearch Random.defaultRandomGames)
        ( long "random"
            <> help
              "Use repeated random playouts for the reduced game; defaults to 100000 samples."
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
              "Use Monte Carlo Tree Search for the reduced game; defaults to 100000 simulations per move."
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
          "Compute puzzle highscores for the reduced game by default, use --random or --mcts for approximate reduced-game searches, use --full for the original game, or render a score plot."
    )
