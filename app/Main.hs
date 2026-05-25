module Main (main) where

import Game (LeafCount)
import Options.Applicative
import Plot (printScorePlot)
import Search
  ( SearchOptions (..)
  , appendWinnerCsv
  , formatWinnerSummary
  , solveGame
  )

-- | Output CSV file path.
type OutputPath = FilePath

-- | Command line options that control program execution.
data CommandLineOptions = CommandLineOptions
  { optionsVerbose :: Bool
    -- ^ Print improving leaders when 'True'.
  , optionsOutputPath :: OutputPath
    -- ^ CSV file used for winner output and plot input.
  , optionsStart :: LeafCount
    -- ^ Starting value of @N@ for the infinite solving loop.
  , optionsPlot :: Bool
    -- ^ Print an SVG plot from the CSV file instead of running the solver.
  }

-- | Parse command line options and either solve games or print a plot.
main :: IO ()
main = do
  options <- execParser commandLineParserInfo
  if optionsPlot options
    then printScorePlot (optionsOutputPath options)
    else mapM_ (runSingleGame options) [optionsStart options ..]

-- | Run one game, print its winner, and append the result to CSV.
--
-- Precondition: the leaf count is non-negative.
-- Postcondition: exactly one CSV row for the finished game has been appended.
runSingleGame :: CommandLineOptions -> LeafCount -> IO ()
runSingleGame options leafCount = do
  winner <- solveGame SearchOptions {searchVerbose = optionsVerbose options} leafCount
  putStrLn ("winner " <> formatWinnerSummary leafCount winner)
  appendWinnerCsv (optionsOutputPath options) leafCount winner

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
    <*> option auto
      ( long "start"
          <> metavar "N"
          <> value 3
          <> showDefault
          <> help "Start solving at N."
      )
    <*> switch
      ( long "plot"
          <> help "Read the CSV file and print an SVG plot of N versus high-score."
      )

-- | Parser metadata used by 'execParser'.
commandLineParserInfo :: ParserInfo CommandLineOptions
commandLineParserInfo =
  info
    (commandLineParser <**> helper)
    ( fullDesc
        <> progDesc
          "Compute puzzle highscores for N = start, start+1, ... until interrupted, or render a score plot."
    )
