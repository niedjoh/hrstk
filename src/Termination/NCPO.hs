-- |a normalized version of CPO (Balnqui et al. LMCS 2015 <https://doi.org/10.2168/LMCS-11(4:3)2015>)
-- based on the method introduced in Jouannaud & Rubio's 2015 article <https://doi.org/10.1145/2699913>
module Termination.NCPO (
  module Termination.NCPO.Type,
  module Termination.NCPO.Ordering,
  module Termination.NCPO.Solver
) where

import Termination.NCPO.Type
import Termination.NCPO.Ordering
import Termination.NCPO.Solver
