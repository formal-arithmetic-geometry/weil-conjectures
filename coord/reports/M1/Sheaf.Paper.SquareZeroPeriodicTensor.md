## What changed

Replaced both original theorem proof holes with complete proofs in the item module.
The scalar proof constructs the rank-one periodic projective resolution explicitly,
checks exactness using the annihilator hypothesis, and computes Tor and derived tensor
using zero differentials. Its axiom audit contains only propext, Classical.choice
and Quot.sound. The sheaf proof constructs an exact constant-module functor
at independent coefficient universes, identifies its algebra and unit objects by
sheafification, and compares the explicit K-flat model with the intrinsic tensor by
common quasi-isomorphism roofs. A sectionwise balanced tensor calculation and the proved
tensorRightPresentation comparison make the resulting differentials zero.
The total tensor is kept behind a private irreducible definition to avoid repeated
unfolding of total-complex constructions. The exact constant functor is made
irreducible after its construction API is proved, and the final scheme proof
shares the canonically typed cohomology-isomorphism proof with nonvanishing.
Local injectivity of the commutative-ring sheafification unit and joint surjectivity of pro-etale covers prove nonvanishing.

All added helpers are private. Broad sheafification instance registrations are
local; five additional proved instances have heads indexed by the private lift or
constant-functor constructions. The two original public theorem signatures, public
imports, and the complete squareZeroQuotientModule definition are unchanged. The
existing node's proof, proof_deps and proof_origin record the implemented route.
The change record coord/changes/square-zero-periodic-tensor-proof-environment.md
records the new proof-environment commands required by stage-3 preflight; there
are no downstream Lean importers and no consumer adaptations.

## Proved and sorry left

Proved the two original holed declarations:

- ModuleCat.square_zero_periodic_resolution_tensor
- AlgebraicGeometry.Scheme.square_zero_periodic_tensor

Holes closed: two, in the declarations listed above. Holes added: zero.
Sorries retained: none. No statements are split off. No axiom or hollow definition is added.
The complete current item, including deliver3.py's declaration probe, compiles
through lcompile.py in 36.1 seconds. A second module compiled in the same batch
(6.7 seconds) audits both public theorems: each uses exactly propext,
Classical.choice and Quot.sound; neither uses sorryAx. Both original theorem
signatures, all original public imports, and the complete
squareZeroQuotientModule definition were compared with the shared source and
are unchanged.

After earlier delivery compile timeouts, scalar tensor differentials were changed
to use the explicit periodicComplex_d_succ and periodicComplex_d_ne interfaces,
avoiding unfolding the whole periodic complex. Private tensor and constant-functor
APIs also prevent repeated unfolding in later proofs. No limit was changed and the
item remains a single module.

## No longer needed

The following original private proof imports and corresponding node dependencies
are not used by this route:

- WeilConjectures.Algebra.Homology.BoundedFlatKFlat /
  lem-pc-module-bounded-flat-kflat: the general bounded-flat criterion exposed by
  FlatModel applies directly to the scalar projective resolution.
- Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor /
  lem-pc-derived-tensor-second-factor-functor: the proved scalar FlatModel comparison
  computes tensor with a degree-zero object directly.
- Sheaf.CategoryTheory.FiniteTypeConstantExact /
  lem-weil-pbc-finite-type-constant-exact: its equality of site and coefficient
  universes does not fit; the exact constant functor is proved privately here.
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat /
  lem-pc-bounded-above-flat-kflat-site: use the existing independent-coefficient
  bounded-flat criterion instead.
- Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent /
  lem-weil-derived-tensor-resolution-independent: compare models directly using
  common roofs and the independent-coefficient K-flat tensor preservation lemma.
- Sheaf.CategoryTheory.SiteConstantModuleUnit /
  lem-sf-constant-module-unit-locally-bijective: use the commutative-ring unit and
  the canonical quotient-module construction directly.
- Mathlib.Algebra.Homology.BifunctorShift: no shift comparison is used.

The following unused finite-basis proof imports copied during development were
also removed:

- Mathlib.LinearAlgebra.FreeModule.Basic
- Mathlib.RingTheory.Finiteness.Defs
- Mathlib.Algebra.Category.ModuleCat.Products
- Mathlib.LinearAlgebra.Basis.Fin
- Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
- Mathlib.LinearAlgebra.FreeModule.Finite.Basic

The following redundant direct private imports are also removed. Their declarations
remain available through retained imports' public import closures; these removals do
not assert that their mathematics is unused:

- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
- Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
- Mathlib.Algebra.Homology.ShortComplex.ModuleCat
- Mathlib.Algebra.Homology.DerivedCategory.Fractions
- Mathlib.Algebra.Homology.BifunctorFlip
- Sheaf.CategoryTheory.RingedSiteModules
- Mathlib.CategoryTheory.Sites.LocallyBijective
- Mathlib.CategoryTheory.Sites.Equivalence
- Mathlib.Algebra.Category.Ring.Limits
- Mathlib.Algebra.Category.Ring.Colimits
- Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
- Mathlib.Algebra.Category.Ring.FilteredColimits
- Mathlib.Algebra.Module.ULift
- Mathlib.Algebra.Category.ModuleCat.Basic
- Mathlib.LinearAlgebra.Isomorphisms
- Mathlib.CategoryTheory.Sites.LocallyInjective
- WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

No module or declaration is withdrawn. These modules may remain needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

The original sheaf proof plan cited exactness and resolution-comparison lemmas with
universe restrictions that do not match the original independent-universe theorem.
The proof supplies the required universe-general glue privately while retaining
all statements and the canonical quotient module verbatim.

Earlier retained logs diagnosed unavailable compiled imports. After an initial
period of server-busy responses, the compiler became available and now checks
this session's proofs. Explicit universe arguments and local instances repair
the elaboration failures found in the retained candidate.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
