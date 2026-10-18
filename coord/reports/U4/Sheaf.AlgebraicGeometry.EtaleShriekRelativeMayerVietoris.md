## What changed

Proved `AlgebraicGeometry.Etale.exists_distinguished_relativeMayerVietoris` with
its original signature unchanged. The proof applies the triangulated candidate
for cX to an absolute open-cover triangle, then transports its vertices using
qcqs compactification composition and the identity proper-pushforward comparison.
Compactness of the intersection uses quasi-separatedness, with no Hausdorff assumption.

Added three proved support modules, each with one public theorem:

- `EtaleOpenCoverShriekNaturalSES`: specializes the existing generic adjunction-mate
  construction and counit identities, then proves short exactness using geometric stalks.
  Three private categorical lemmas give explicit splittings in the three stalk cases.
- `EtaleOpenCoverShriekComplexSES`: lifts the natural maps to cochain complexes and
  proves exactness degreewise, transporting through the evaluation biproduct comparison.
- `EtaleOpenCoverShriekTriangle`: applies the canonical short-exact-complex triangle,
  compares the exact induced functors, lifts the arrows through the full inclusion
  D⁺ → D, and reflects distinguishedness. It uses an arbitrary cochain representative;
  it does not require construction of a bounded-below representative.

All support imports used only in proofs are non-public. Updated the item's proof
and proof dependencies and supplied nodes for all three new public theorems.
No definition, existing statement, target, universe, or public signature was changed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Etale.exists_distinguished_relativeMayerVietoris`.
Added zero holes. All three new theorems are proved:

- `AlgebraicGeometry.Etale.exists_natural_shortExact_openCover_lowerShriek`
  (`lem-weil-pbc-etale-open-cover-shriek-natural-ses`).
- `AlgebraicGeometry.Etale.exists_shortExact_openCover_lowerShriek_complex`
  (`lem-weil-pbc-etale-open-cover-shriek-complex-ses`).
- `AlgebraicGeometry.Etale.exists_distinguished_openCover_lowerShriek`
  (`lem-weil-pbc-etale-open-cover-shriek-triangle`).

No `sorry` remains in any delivered module. All four repaired modules compile
through `lcompile.py --all`, with no warnings, in 5.6–7.1 seconds each. The delivery
dry run checks the full set before pushing. The existing qcqs composition theorem
is used as the declared dependency of the original plan; this delivery does not
claim to close its upstream holes. This is one item hole closed, not a decomposition.

## No longer needed

Removed the following direct proof imports from the item module:

- `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Mathlib.CategoryTheory.Sites.Point.Basic`.
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.

The old proof route's separate affine-cover criterion and qcqs permanence lemmas
are unnecessary: native compact-intersection and open-embedding instances supply
these facts. The constant-ring-module equivalence and scalar-forgetting detour
are unnecessary because the native geometric stalk APIs work directly with
ModuleCat-valued sheaves. The separately planned sheaf-SES declaration is replaced
by the fully proved natural sheaf sequence in this delivery. Separate K-injective
existence, direct-image left exactness, derived negative vanishing, and construction
of a triangulated right-derived functor are unnecessary here: the native chosen
compactification functor already has the needed triangulated instance.

The following old direct proof nodes are not required by this implemented route:

- `lem-weil-pbc-quasi-separated-affine-cover-criterion`.
- `lem-weil-pbc-qcqs-morphism-permanence`.
- `lem-weil-pbc-etale-constant-ring-module-equivalence`.
- `lem-weil-pbc-etale-open-cover-shriek-ses` (its canonical-map interface is absent;
  the natural sequence needed here is proved directly).
- `lem-weil-pbc-module-sheaves-grothendieck-abelian` as a separate obligation.
- `lem-weil-pbc-kinjective-functorial-existence`.
- `lem-weil-pbc-module-direct-image-left-exact`.
- `lem-pc-right-derived-functor-triangulated` as a separate construction.
- `lem-weil-pbc-derived-functor-negative-vanishing`.

The exact restriction/extension, complex-SES triangle, and exact-derived-functor
facts remain used through native APIs in the support proofs; they are not claimed
as pruned mathematics. Removed all four obsolete direct `tool_uses` entries from
the item node: coefficient-forgetting, module inverse-image exactness, module-sheaf
Grothendieck abelianness, and module direct-image left exactness. This prunes this
item's direct dependencies, without claiming that other consumers no longer need them.
The unit's own statements and proof steps are unchanged.

The repair also prunes the three duplicate private declarations
`AlgebraicGeometry.Etale.nestedMate`, `AlgebraicGeometry.Etale.nestedMate_app`,
and `AlgebraicGeometry.Etale.nestedTranspose_counit`. Their existing
`SheafOfModules` counterparts supply exactly the needed generic argument.

## Where the brief, the DAG or earlier work was wrong

The DAG record `lem-weil-pbc-etale-open-cover-shriek-ses` names
`Sheaf.Paper.EtaleOpenCoverShriekSES` and
`AlgebraicGeometry.etale_openCover_lowerShriek_shortExact`, but neither the module
file nor that declaration is available in the shared tree/compiler environment.
It therefore cannot supply the advertised proof dependency. The delivery proves
its needed sheaf-level content directly from native adjunction, stalk, and exactness
APIs, including naturality; no unproved replacement is introduced.

Repair of returned head `0bb050296f`: removed the duplicate private lemmas
`AlgebraicGeometry.Etale.nestedMate_app` and
`AlgebraicGeometry.Etale.nestedTranspose_counit`, and the copied private definition
`AlgebraicGeometry.Etale.nestedMate`. Added the proof-only import
`import all WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact`.
The natural sheaf sequence now directly uses `SheafOfModules.nestedMate`,
`SheafOfModules.nestedMate_app`, and `SheafOfModules.nestedTranspose_counit`.
Although the module's main open-cover theorem concerns Zariski module sheaves,
these three helpers quantify over arbitrary categories and adjunctions. The
previous report wrongly treated them as unavailable for small etale sheaves.
`import all` makes their private declarations available without changing the
source library. No source module, existing visibility, or public signature changes.
The natural-SES node's proof now records these actual reused declarations.
The source argument works for any commutative ring in the absolute support lemmas;
only the unchanged relative item retains its finite-ring assumption.

Edge cases checked in the proof: empty or coincident covering opens, empty X,
zero ring, characteristic two, and zero complexes. The stalk case distinction
uses only the cover and open membership, so includes all these cases.

## New nodes

`lem-weil-pbc-etale-open-cover-shriek-natural-ses` attaches the proved natural
sheaf-level sequence to `EtaleOpenCoverShriekNaturalSES.lean`. Its proof constructs
maps before specializing to a sheaf and checks the actual counit identities and
stalk sequences, rather than only their objects.

`lem-weil-pbc-etale-open-cover-shriek-complex-ses` attaches the proved degreewise
lifting to `EtaleOpenCoverShriekComplexSES.lean`.

`lem-weil-pbc-etale-open-cover-shriek-triangle` attaches the proved D⁺ triangle
to `EtaleOpenCoverShriekTriangle.lean`. This is the absolute intermediate step of
Tag 0GKK, before applying the relative compactification functor of Tag 0GKN.

There are no statement/definition change records or forced consumer adaptations.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
