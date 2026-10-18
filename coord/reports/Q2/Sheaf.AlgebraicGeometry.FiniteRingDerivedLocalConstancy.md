## What changed

Replaced `AlgebraicGeometry.Etale.finiteRing_derived_local_constancy`'s single sorry
with a complete Lean combination of local finite models, a common fiber-product
cover, mapping-sheaf comparisons, finite-value descent, and connectedness. Its full
signature is unchanged. All new helper definitions have explicit constructions;
all private helper theorems are proved.

The local model proof constructs finite module trivializations on every etale slice
and applies the new mixed-universe site-model component. A direct application of
`CategoryTheory.exists_site_bounded_constant_model` requires an equivalence with
`AsSmall X.Etale`. That component is proved by explicit site and slice equivalences,
homology transport, a cover indexed by points, and derived constant-complex comparisons.
The original general-site module is held by P3 and is unchanged in this delivery.
Existing public signatures and public imports are unchanged. No forced adaptations
are delivered.

Added `Sheaf.RingTheory.FiniteRingDerivedHomFinite`, proving algebraic derived Hom
finiteness by a bounded-above finite free resolution and a finite chain-map count.
Added `Sheaf.AlgebraicGeometry.DerivedMappingPresheavesRestriction` and
`Sheaf.AlgebraicGeometry.FiniteRingConstantDerivedMappingSheaves` for the two
mapping comparisons. The presheaf restriction comparison is proved. The main file
proves sheafification compatibility using
Mathlib's `Functor.pushforwardContinuousSheafificationCompatibility` twice.

Validation: all five delivery modules compile through `lcompile.py`, and the final
`deliver3.py --no-push` passes compilation and stage-3 preflight. The delivery is
classified CODEX for the maintainer's independent review.

## Proved and sorry left

Closed the item's original hole:
`AlgebraicGeometry.Etale.finiteRing_derived_local_constancy`
(node `lem-weil-pbc-finite-ring-derived-local-constancy`), 1 of 1 syntactic holes.
This is a decomposition, not a sorry-free proof: one new intermediate hole remains.
The local finite module trivializations, degree-bound cleanup, bounded complex
models, and connected-stalk clause have complete proofs from named dependencies.
The mapping clauses are fully combined from the strictly smaller comparisons;
algebraic finiteness and finite-set descent are proved.

Proved `DerivedCategory.finite_derived_hom_of_bounded_finite`
(node `lem-weil-pbc-finite-ring-derived-hom-finite`) with no local sorry.

Added holes:

- `AlgebraicGeometry.Etale.finiteRing_constant_derived_mapping_sheaves`
  (`lem-weil-pbc-finite-ring-constant-derived-mapping-sheaves`): still needs the
  truncated finite-free resolution comparison, locally algebraic actual maps and
  homotopies, and sheafification of the resulting locally bijective constant map.
  The Isom clause then follows by the geometric-stalk invertibility test.

Proved `AlgebraicGeometry.Etale.etale_site_bounded_constant_models`
(`lem-weil-pbc-etale-site-bounded-constant-models`) with no local sorry, from the
original general-site theorem on `AsSmall X.Etale` and explicit equivalences.

Proved `AlgebraicGeometry.Etale.derived_mapping_presheaves_restriction`
(`lem-weil-pbc-derived-mapping-presheaves-restriction`) by exact-functor associativity
and naturality of conjugation, with no local sorry.

The original general-site module and its existing hole are unchanged. The item
has zero remaining holes. The delivery adds one hole, so this is a decomposition
with zero net hole change, not claimed as net progress. The three fully proved new components add no holes.

## No longer needed

Removed these direct proof imports from the item:

- `WeilConjectures.ConstructibleSheaf.Defs`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.Algebra.Homology.DerivedCategory.KProjective`
- `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Mathlib.Topology.Connected.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact`
- `Sheaf.AlgebraicGeometry.FiniteFreeConstantLocalLift`
- `Sheaf.RingTheory.FiniteConeFreeModel`
- `Sheaf.AlgebraicGeometry.ConnectiveSingleHom`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Sheaf.Paper.FiniteFreeEtaleLocalActual`
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Mathlib.RingTheory.Noetherian.Basic`

The constant-complex comparison retains the finite-cone free model, finite-free
local actual-map theorem, constant exactness, Hom triangle exactness, orthogonality,
constant morphism localization, and local sheafification-sections route. These
nodes are relocated to that component and are not claimed as pruned.

The item's explicit connective-single-Hom route is unused. Removed the obsolete
`lem-sc-connective-single-hom` tool approval. `Sheaf.AlgebraicGeometry.ConnectiveSingleHom`
and `Sheaf.AlgebraicGeometry.FiniteFreeConstantLocalLift` are not needed directly:
the first clause uses the existing general-site model theorem instead. The unit's
own statement and realized steps are unchanged.

A source-graph comparison also removes these modules from this item's import
closure: `WeilConjectures.ConstructibleSheaf.Biproduct`, `GenericConstancy`,
`KernelCokernel`, `Refinement`, `UniversalHomeomorphism`, and
`WeilConjectures.Topology.StratificationDense`, as well as the two Sheaf modules
above. They remain reachable through other targets, so no global module pruning
is claimed.

## Where the brief, the DAG or earlier work was wrong

The general-site theorem's `[SmallCategory C]` interface does not directly apply
to the small etale site, whose objects and morphisms live in different universes.
A compiling universe generalization was rejected by the delivery check because
P3 holds that module; its signature cannot be changed by this group. The delivery
therefore proves the equivalence-of-sites application in a new component and leaves
the shared theorem unchanged. The old main docstring described an independent
induction through connective-single-Hom; it now follows the site-model route.

Edge cases checked: an empty base has no geometric point and the connected clause
is vacuous; empty cover members are discarded in the connected proof; the Isom
value may be empty; zero complexes and empty support intervals are allowed; no
finite Tor-amplitude or connectedness hypothesis is added to the mapping clauses.

## New nodes

`lem-weil-pbc-finite-ring-derived-hom-finite`: proved algebraic finiteness needed
for finite local values. The finite-cone hypothesis is checked from finite terms.

`lem-weil-pbc-finite-ring-constant-derived-mapping-sheaves`: isolates only the
constant-input Hom/Isom comparison, which is independent of local model existence,
common-cover refinement, finite stalk descent, and connectedness.

`lem-weil-pbc-derived-mapping-presheaves-restriction`: isolates formal restriction
naturality for arbitrary derived objects and arbitrary commutative coefficients.
It does not assume finite local models or conclude finite local constancy.

`lem-weil-pbc-etale-site-bounded-constant-models`: isolates the construction of
bounded finite complex models from explicit covering trivializations of bounded
cohomology. It has no mapping-sheaf, algebraic finiteness or connectedness conclusion.
The general-site theorem is applied after transporting through `AsSmall`; all
formal site-equivalence glue is proved in this component. A blueprint
search for bounded constant models found no exact statement to attach instead.

Blueprint searches for derived Hom, constant complex Hom, and mapping restriction
found no blueprint statement equal to any new component. All four components
serve amplification-proper proof (c), TOW, through the assigned finite-ring lemma.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
