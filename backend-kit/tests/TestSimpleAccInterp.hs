
module Main where
import Data.Array.Accelerate.BackendKit.ConsoleTester (makeMain)
import SimpleAccInterpConf (conf)

--------------------------------------------------------------------------------

main :: IO ()
main = makeMain conf
