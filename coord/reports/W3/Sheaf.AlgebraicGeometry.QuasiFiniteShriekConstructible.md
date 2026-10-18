## What changed

Proved both declarations of Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible,
with their signatures and public imports unchanged. The general proof factors h through
a finite finitely presented scheme, applies existing open-extension constructibility,
computes cohomology using the two exact functors, applies finite pushforward
constructibility, and compares compactifications. The closed-immersion consequence
uses Mathlib's quasi-finiteness-at-a-point and fibre singleton equivalence.

Added proof imports WeilConjectures.ConstructibleSheaf.OpenClosed,
Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison, and
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact.
Updated the existing node's proof, proof_deps and proof_origin to match.
The item is not a statement or step realizing its unit, so no unit route is bypassed.

The final single-file compile passed without warnings in 5.6 seconds.
Read the separated argument of Stacks more-etale.tex, lemma-qf-f-shriek-constructible
(0GK3), and the finite exactness argument of lemma-Rf-shriek-for-quasi-finite (0GKM).
No additional finite Tor or upper boundedness hypothesis is used. Empty sources,
empty strata and the zero coefficient ring are handled by the cited interfaces.

## Proved and sorry left

Closed 2 of 2 original holes:

- AlgebraicGeometry.Etale.constructibleCohomology_lowerShriek_of_quasiFinite.
- AlgebraicGeometry.Etale.constructibleCohomology_lowerShriek_of_isClosedImmersion.

Both belong to lem-weil-pbc-etale-quasifinite-shriek-constructible.
There are zero direct sorry holes left in the item and zero added anywhere.
This is a proof from existing declarations, not a decomposition. The factorization
and finite pushforward constructibility dependencies are still sorried in the base;
this delivery does not claim their transitive axioms are eliminated.

## No longer needed

Removed these original proof imports:

- WeilConjectures.SixFunctors.OpenClosed.Complex.
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk.
- Mathlib.AlgebraicGeometry.Sites.EtalePoint.
- Mathlib.AlgebraicGeometry.Morphisms.Finite.
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs.
- Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf.

The direct uses of lem-weil-pbc-extension-by-zero-unit-iso,
lem-weil-pbc-extension-by-zero-stalks, lemma-openclosed-stalk-upperstar,
lem-weil-pbc-sets-etale-iso-on-geometric-stalks and def-weil-constructible-subset
are unnecessary: the proved lem-fin-extension-by-zero supplies the entire open
stratification argument. They are removed from this node's proof dependencies.
The constructible-sheaf definition remains a statement dependency, while its
proof-dependency occurrence is replaced by the comparison theorem.
The removed module imports may remain transitively reachable through other modules;
no global module withdrawal is claimed. No other declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's open-stratification argument was already implemented in the source
library. Reusing it, together with the proved module-constructibility comparison,
avoids repeating a geometric-stalk proof. The existing exact-functor interfaces
also provide the bounded-below cohomology calculation in full.
No mathematical statement, definition or target was changed; no consumer adaptation
or change record is needed. No new nodes were created.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
