## Worker report

The module `Sheaf.TraceFormula.GenericCMLocusField` states
`generic_cm_locus_field`. It binds a field `k`, a commutative `k`-algebra `A`,
and the finite-type instance. The first conjunct says the set of prime points
whose localization is Noetherian and whose local depth (coerced to
`WithBot ℕ∞`) equals `ringKrullDim` is open. The second conjunct says the same
set is dense. The final conjunct renders the equivalent formulation: for every
open nonempty `V : Set (PrimeSpectrum A)`, there is a prime `q ∈ V` satisfying
those two Cohen--Macaulay clauses.

The localization is Mathlib's `Localization.AtPrime q.asIdeal`, the local depth
is `IsLocalRing.depth (R := Localization.AtPrime q.asIdeal)
(Localization.AtPrime q.asIdeal)`, and the dimension is Mathlib's
`ringKrullDim (Localization.AtPrime q.asIdeal)`. The `IsNoetherianRing` clause
is explicit for each localization; no Noetherian instance is silently added.
The field and commutative-ring hypotheses are exactly the binders from the
node, and `[Algebra.FiniteType k A]` is the finite-type hypothesis.

Statement dependencies use `RingHom.FiniteType` from
`Mathlib.RingTheory.FiniteType`, `IsNoetherianRing` from
`Mathlib.RingTheory.Noetherian.Defs`, `Ideal.depth`/`IsLocalRing.depth` from
`Sheaf.RingTheory.Depth`, `ringKrullDim` from
`Mathlib.RingTheory.KrullDimension.Basic`, `AlgebraicGeometry.Spec` from
`Mathlib.AlgebraicGeometry.Scheme`, and `Localization.AtPrime` from
`Mathlib.RingTheory.Localization.AtPrime.Basic`. Proof-plan imports include
`Sheaf.AlgebraicGeometry.FibreCohenMacaulayLocus` (the general fibre
Cohen--Macaulay openness theorem) The downstream `Sheaf.TraceFormula.FlatLFPCMLocusFibreDense` module is omitted
from imports because it uses this theorem and importing it would create a cycle;
it remains a recorded proof dependency for the maintainer to add after this module
lands. The recorded Mathlib dependency declarations were read at their
source locations; the project depth declaration was read in full.

Edge cases checked include the zero algebra (the locus can be empty, while the
open and dense assertions have the usual topological meaning), dimension zero
localizations, and nonzero nilpotent maximal ideals such as
`k[ε]/(ε²)`: the statement only requires depth equal to dimension and does not
incorrectly require the maximal ideal to vanish. The empty-open case is
excluded by `V.Nonempty` exactly as in the equivalent formulation.

Searches for an existing declaration: `msearch.py ... leanfinder "dense open
Cohen Macaulay locus finite type algebra field"` returned only generic finite
 type/quasi-finite results and no locus theorem; `msearch.py ... loogle
"IsOpen Dense PrimeSpectrum depth ringKrullDim"` returned no match (and a
parser diagnostic for the non-function query); `rg` over `WeilConjectures/`
and `lean/Sheaf` found no declaration of this theorem; Mathlib grep for
`Cohen.?Macaulay|depth.*Krull|ringKrullDim` found only infrastructure. Thus a
new statement module is required. The module compiles cleanly with `scompile.py`.

## Second reading by Q132

I independently read the node and module. The field, commutative algebra,
algebra, and finite-type hypotheses all appear once. The open and dense clauses
use exactly the same displayed set, including both Noetherianity and the
`depth = ringKrullDim` condition. The final quantification ranges over every
open nonempty subset of `PrimeSpectrum A` and supplies a point in it with the
same two clauses, matching the node's equivalent formulation. No hypothesis or
edge case is omitted, and no additional structural assumption is introduced.
