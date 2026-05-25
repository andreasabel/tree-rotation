module Main (main) where

import Full.Search qualified as FullSearch
import Options.Applicative
import Plot (printScorePlot)
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
  }

-- | Parse command line options and either solve games or print a plot.
main :: IO ()
main = do
  options <- execParser commandLineParserInfo
  if optionsPlot options
    then printScorePlot (optionsOutputPath options)
    else mapM_ (runSingleGame options) [resolvedStart options ..]

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
      winner <-
        Search.solveGame
          Search.SearchOptions {Search.searchVerbose = optionsVerbose options}
          leafCount
      putStrLn ("winner " <> Search.formatWinnerSummary leafCount winner)
      Search.appendWinnerCsv (optionsOutputPath options) leafCount winner

-- | Resolve the default starting value for the selected game mode.
resolvedStart :: CommandLineOptions -> LeafCount
resolvedStart options =
  case optionsStart options of
    Just leafCount -> leafCount
    Nothing
      | optionsFull options -> 3
      | otherwise -> 1

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

-- | Parser metadata used by 'execParser'.
commandLineParserInfo :: ParserInfo CommandLineOptions
commandLineParserInfo =
  info
    (commandLineParser <**> helper)
    ( fullDesc
        <> progDesc
          "Compute puzzle highscores for the reduced game by default, use --full for the original game, or render a score plot."
    )
