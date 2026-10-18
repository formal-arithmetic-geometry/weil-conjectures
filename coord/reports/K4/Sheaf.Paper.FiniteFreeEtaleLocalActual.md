## What changed

Proved `AlgebraicGeometry.finiteFree_etale_local_actual` with its exact original
signature and universes. The proof uses left fractions and Hom exactness into a
mapping-cone triangle for representatives; right fractions and Hom exactness out
of a mapping-cone triangle detect derived zero maps.

Added `Sheaf.Paper.FiniteFreeEtaleAcyclicHomotopy`, proving
`AlgebraicGeometry.finiteFree_etale_acyclic_homotopy` by finite descending induction.
The sole local input is the already proved
`Scheme.exists_finiteFreeConstant_local_lift`. Private helpers construct partial
homotopies, extend them one degree, and transport them through cover refinement
and the canonical inverse-image composition isomorphism. No arbitrary object is
chosen from an unproved existence theorem.

Replaced the old K-injective/internal-Hom route in the node and theorem docstring
with the source's shorter cone route (Stacks 08FP, 08FQ, 08FR). The unit's proper
base-change statement and realized proof steps are preserved. All proof imports
are non-public. Replaced the unused public `Sheaf.CategoryTheory.RingedSiteModules`
import with public `Mathlib.CategoryTheory.Sites.ConstantSheaf`, which the existing
signature actually uses. No existing statement or definition was changed. The public-import change is
recorded in `coord/changes/finite-free-etale-local-actual-public-imports.md`,
including the unchanged consumer compilation.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.finiteFree_etale_local_actual`
(node `lem-weil-pbc-finite-free-etale-local-actual`).

Also proved the new supporting theorem
`AlgebraicGeometry.finiteFree_etale_acyclic_homotopy`
(node `lem-weil-pbc-finite-free-etale-acyclic-homotopy`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered files: 0.
This is a proof, not a decomposition with new holes.

Validation: both final proof files compile cleanly on the server (9.4 s and
21.5 s), and `#print axioms` for each public theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The unchanged direct consumer
`Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy` also compiles (5.7 s)
against the sandbox modules and the reduced public imports. The existing theorem
signature was compared character for character with the repository original.
Temporary axiom-print commands and the unchanged consumer copy were removed
after these checks.

## No longer needed

The cone route avoids K-injective resolutions, bounded exact-term internal Hom,
and local bijectivity after sheafification. The helper uses Mathlib's
`HomComplex.Cochain` only to store graded families of ordinary sheaf morphisms;
it constructs their homotopy equation directly and uses no sheaf internal-Hom
comparison theorem. Removed these direct imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso`
- `Sheaf.Algebra.Homology.FiniteFreeInternalHomExactSequence`
- `Sheaf.Algebra.Homology.HomComplex`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.SiteRestrictionExact`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`

The following former proof dependencies are no longer needed for this proof:

- `def-pur-hom-complex` (`Sheaf.Algebra.Homology.HomComplex`).
- `def-pur-localized-ringed-site` (`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`).
- `def-weil-abstract-derived-category` (`Mathlib.Algebra.Homology.DerivedCategory.Basic`).
- `def-weil-pbc-constant-sheaf` (`Mathlib.CategoryTheory.Sites.ConstantSheaf`).
- `def-weil-size-convention`.
- `lem-pc-bounded-exact-term-hom-quasi-iso` (`Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso`).
- `lem-sc-finite-free-internal-hom-exact-sequence` (`Sheaf.Algebra.Homology.FiniteFreeInternalHomExactSequence`).
- `lem-weil-pbc-etale-site-localization-open` (`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`).
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-weil-pbc-module-sheaves-colimits-forgetful` (`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`).
- `lem-weil-pbc-site-module-presheaf-sheafification-exact`.
- `lem-weil-pbc-site-restriction-exact` (`WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`).
- `lem-weil-pbc-site-sheafification-iso-locally-bijective`.
- `prop-pur-kinjective-resolutions-exist` (`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`).

The constant-sheaf and abstract-derived-category notions remain statement
prerequisites and are used through the new theorem and proved APIs; removing them
from the old proof-dependency list does not withdraw these notions. Other listed
nodes may still be needed by independent parents: this delivery prunes this item's
edges, not their files. No existing module is withdrawn.

All six obsolete top-level `tool_uses` approvals were removed:
- `lem-pc-bounded-exact-term-hom-quasi-iso`
- `lem-sc-finite-free-internal-hom-exact-sequence`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-site-restriction-exact`
- `prop-pur-kinjective-resolutions-exist`

The new helper also omits the unused Grothendieck-abelian derived-category
existence imports. Its development imports of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence` and
`WeilConjectures.Mathlib.Algebra.Homology.HomologySequence` were also removed;
only the smaller proved `ShortComplex.HomologicalComplex` API is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan is mathematically valid, but unnecessarily goes through the
ring-sheaf module encoding and a K-injective/internal-Hom comparison. The proved
fixed-coefficient local lifting lemma already supplies the finite induction
needed by Stacks 08FP. Cone triangles then give both assertions without any of
the old unproved comparison statements. No disputed statement or definition
repair was necessary. Edge cases checked: zero ranks, zero source, an empty
support interval (a>b), empty base scheme, arbitrary commutative coefficient ring,
and unbounded target.

## New nodes

`lem-weil-pbc-finite-free-etale-acyclic-homotopy` is the finite-free constant case
of Stacks 08FP(1), with a completely proved new module
`lean/Sheaf/Paper/FiniteFreeEtaleAcyclicHomotopy.lean`. It is strictly smaller than
the assigned theorem: its target must be acyclic and it only asserts local
null-homotopy of an actual chain map. The main theorem combines it with fraction
and cone-triangle APIs. There are no split-off holes. No existing statement or definition changes; the
public-import change record is
`coord/changes/finite-free-etale-local-actual-public-imports.md`.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
