module

-- Supply the command elaborator used by the library declaration probes.
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Retired split determinant comparison helper

The former restriction helper is true and was proved by substitution. Its only
caller now uses the naturality equation directly after converting linear maps to
equivalences. The historical local construction was already subsumed by
`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists`.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
-/

@[expose] public section
