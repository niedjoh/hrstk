module Test where

import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.Hspec (testSpecs)

import TypOpsSpec (typOpsSpecs)
import TermOpsSpec (termOpsSpecs)
import SubstOpsSpec (substOpsSpecs)
import MatchSpec (matchSpecs)
import UnifSpec (unifSpecs)
import EquationOpsSpec (equationOpsSpecs)
import RewritingSpec (rewritingSpecs)
import CriticalPairsSpec (criticalPairsSpecs)
import NCPOSpec (ncpoSpecs)
import StarCPOSpec (scpoSpecs)
import Properties (props)

main :: IO ()
main = do
  specs <- concat <$> mapM testSpecs [ typOpsSpecs
                                     , termOpsSpecs
                                     , substOpsSpecs
                                     , matchSpecs
                                     , unifSpecs
                                     , equationOpsSpecs
                                     , rewritingSpecs
                                     , criticalPairsSpecs
                                     , ncpoSpecs
                                     , scpoSpecs
                                     ]
  defaultMain $ testGroup "All Tests" [ testGroup "Specs" specs
                                      , testGroup "Properties" props]
