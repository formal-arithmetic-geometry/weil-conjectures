## What changed

The signature of `AlgebraicGeometry.Scheme.finiteTensor_constructible_cohomology` is
unchanged. Its proof is now complete Lean from two strictly local intermediate
statements. The private `common_stratification` proves a finite-family refinement
by induction, using the actual fiber-product projections of `S.inter R`; the
empty family has one whole-scheme stratum. A disjoint sum tags the finite supports
of K and L. Finite support supplies upper bounds, exact restriction transports
them, and the local tensor statement supplies the required output on each stratum.
There is no assertion that the tensor is bounded below.

Four new modules and five nodes expose the missing interfaces. Two new modules
are proved. The coefficient-comparison node instead attaches the already proved
`AlgebraicGeometry.Scheme.constantComparison_isIso` in
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`. That module was unclaimed
when this repair began. Its existing proof and statement are unchanged; the theorem
is now public so that the new modules can import and use it. The duplicate
`ProEtaleConstantCoefficientComparison` module is removed from the delivery. It
never landed on the shared branch, so the delivery tool correctly requires its
omission rather than a `deleted.txt` entry for a nonexistent library file.
`ProEtaleConstantModulePullbackHomology` packages the existing identified-coefficient
pullback as the functor whose objects are the original constant-module restrictions,
proves its exactness instances, constructs the cohomology comparison, and proves
preservation of upper cohomological bounds.
`ProEtaleConstantModulePullbackComposition` proves composition for the actual
canonical module restrictions. It normalizes the coefficient direct-image maps
against constant-sheaf units, applies the module pushforward composition API,
and uses uniqueness of left adjoints. The main proof uses this comparison and
an explicit private isomorphism-invariance proof, including the stalk colimit
functor, to transport along both common-refinement projections.
The finite-local-constancy module also contains proved private Hom equivalences
for constant module presheaves and their simultaneous ring/module sheafification.
These expose the exact constant-model universal property. The private
`constantModulePullbackIso` now also proves preservation of the actual global
constant module construction, including its scalar action: the proof composes the
constant-module and inverse-image adjunctions and identifies terminal sections
using the canonical coefficient-unit formula. Localized-site compatibility and
the geometric stalk calculation remain open.
No existing definition was changed,
and no object is selected from an undetermined existence statement.

The other two modules state inverse-image stability of finite local constancy and
the restricted local tensor calculation. Each has one public named obligation,
a complete proof in words, sources, and a matching node. Their statements do not
assume constructibility or choose stratifications. The parent node's proof and
proof dependencies now follow the actual Lean proof.

## Proved and sorry left

This is a decomposition, not a completed proof of the original mathematical
obligation: one upper hole is closed and two lower holes are added (net -1).
The main item module has zero `sorry`; the delivery as a whole has exactly two.
No other original hole or definition is changed. The coefficient theorem receives
public visibility, with its original signature and proof unchanged.

Closed upper hole:

- `AlgebraicGeometry.Scheme.finiteTensor_constructible_cohomology`
  (`lem-pur-finite-tensor-constructible-cohomology`), by a complete proof from the
  two stated local interfaces and the proved restriction API.

Proved without additional holes:

- Reused existing `AlgebraicGeometry.Scheme.constantComparison_isIso`
  (`lem-pur-proetale-constant-coefficient-comparison`), now publicly accessible.
  Its proof already existed; this is not a newly proved result.
- `AlgebraicGeometry.Scheme.proEtaleConstantModulePullback_boundedAbove`, the three
  exactness/additivity instances, and
  `AlgebraicGeometry.Scheme.proEtaleConstantModulePullbackHomologyIso`
  (`lem-pur-proetale-constant-module-pullback-homology`).
- `AlgebraicGeometry.Scheme.proEtaleConstantModulePullback_comp`
  (`lem-pur-proetale-constant-module-pullback-composition`), including the actual
  coefficient-map normalization and module direct-image composition.
- The private `constantPresheafHomEquiv` and `constantModuleHomEquiv` constructions
  in the finite-local-constancy pullback module; they prove the actual constant
  module universal property rather than assuming a coefficient-category equivalence.
  Its private `constantModulePullbackIso` additionally proves the global
  constant-model pullback and checks the scalar action using the coefficient unit.
- The private isomorphism-invariance and iterated-restriction assembly lemmas,
  the private finite-family common-stratification lemma and the finite-support
  upper-bound argument in the item module.

Every remaining hole, both newly added:

- `AlgebraicGeometry.Scheme.proEtale_finiteLocalConstancy_pullback`
  (`lem-pur-proetale-finite-local-constancy-pullback`). Still needed: transport the
  actual module inverse image through localized sites (with their local coefficient
  identifications) and identify geometric stalks at the composite point. Global
  constant-model pullback, its scalar compatibility, canonical coefficient maps,
  and composition comparisons are already proved in this delivery.
  This is the ordinary finite-local-constancy pullback argument, independent of complexes and tensor.
- `AlgebraicGeometry.Scheme.proEtale_restrictedTensor_finiteLocalConstancy`
  (`lem-pur-proetale-restricted-tensor-finite-local-constancy`). Still needed: bridge
  the concrete pro-etale module local models to the covering-sieve finite-type
  predicate on the small site model, apply the already stated Tag 094H tensor
  lemma and canonical tensor pullback comparison, and transport the resulting
  cohomology and finite constant-model stalks back. Exact pullback, upper bounds,
  and its cohomology comparison are already proved in this delivery. This is a
  local assertion for bounded-above inputs, without constructible partitions.

The nonzero-degree hypotheses are sufficient: a zero cohomology sheaf restricts
to zero, whose constant zero model has finite stalks. The zero ring, empty base,
empty support and empty cover members cause no missing hypothesis. In particular,
modules over Z/4 may have infinitely many negative Tor groups, and no step assumes
otherwise. The actual hole count is zero in the item module and two in the four
new modules.
The adapted existing triangulation module also has zero holes. The withdrawn
coefficient-comparison module contributes no declaration and no hole.

## No longer needed

The returned duplicate module `Sheaf.Paper.ProEtaleConstantCoefficientComparison`
and all its private proof helpers are withdrawn. Homology now publicly imports
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` and uses its existing
`constantComparison_isIso`; the composition and finite-local-constancy proofs use
that same theorem. No duplicate alias theorem is retained.


Removed direct proof imports from the item module:

- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.LocallyConstantTensor`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`

The parent no longer directly proves valuation/DVR finiteness: it uses the
existing `Padic.finite_coefficientExtensionRing` theorem. Its former direct
proof dependencies `lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-locally-constant-tensor`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`def-weil-pbc-proetale-operations`, `def-weil-pbc-proetale-site`,
`def-weil-proetale-inverse-image`, `def-weil-sheaf-of-modules-category`,
`lem-weil-l-adic-extension-absolute-value`, and
`lem-weil-valued-dvr-finite-quotients` are replaced
by the actual local interfaces and concrete exactness API in the parent proof.
These generic tensor and inverse-image tools remain needed below those interfaces;
coefficient finiteness infrastructure remains transitively used. This delivery
claims no whole-library module has become unreachable. A fresh import-graph
comparison after the repair confirms that the following
modules and matching nodes leave this item's transitive import closure entirely
(they remain reachable elsewhere):

| Module | Node |
| --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage` | No current node attachment |
| `Sheaf.CategoryTheory.SitePullbackAbelianExact` | `lem-weil-pbc-site-pullback-abelian-exact` |
| `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying` | `lem-weil-pbc-site-pullback-abelian-underlying` |
| `WeilConjectures.CategoryTheory.SheafAbelianObjectsBijective` | `lem-weil-pbc-sheaf-abelian-objects-bijective` |
| `WeilConjectures.CategoryTheory.SheafAbelianObjectsInjective` | `lem-weil-pbc-sheaf-abelian-objects-bijective-injective` |
| `WeilConjectures.CategoryTheory.SheafAbelianObjectsSurjective` | `lem-weil-pbc-sheaf-abelian-objects-bijective-surjective` |
| `WeilConjectures.CategoryTheory.SheavesAbelianForward` | `lem-weil-pbc-sheaf-abelian-forward` |
| `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian` | `lem-weil-pbc-sheaf-algebraic-structures-abelian-component` |

The raw source import graph also drops the Mathlib leaves
`Mathlib.Algebra.Group.Ext` and `Mathlib.CategoryTheory.IsoCat`. This is a source
import-closure comparison, not a claim to have removed these Mathlib declarations.

The parent's obsolete six top-level `tool_uses` approvals are withdrawn; their
order is not changed.
The new nodes declare their own generic off-unit tool uses where required.

Common refinement needs only actual projections, not a range-subset factorization
or invariance under nilpotent thickenings. No such additional lemma or import is
introduced. The new helper statements import local-constancy/stalk or inverse-image
definitions directly, rather than importing constructibility unnecessarily.

## Where the brief, the DAG or earlier work was wrong

Several Lean attachments in the supplied DAG name files absent from this checkout:
`ProEtaleLocallyConstantSheafOfUniverses`, `ProEtaleConstantRingOperations`,
`ProEtaleModuleStalkFunctor`, and
`RingedTopoiCanonicalTensorPullbackOfUniverses`. Their actual current interfaces
are in `ProEtaleLocallyConstantSheaf`, `ProEtaleOperations` with its canonical
adjunction, `ProEtaleGeometricStalk`, and `RingedTopoiCanonicalTensorPullback`.
Those interfaces and their signatures, rather than the stale module names, were
read and used. No existing attachment is edited by this delivery.

The blueprint node `prop-weil-pbc-proetale-constant-ring-map` is the finite-ring
analogue of the proved coefficient comparison. It is not an identical statement
(the old result allows finite noncommutative rings; the new result allows arbitrary
commutative rings), so `same_as` remains empty.
Its recorded module `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` is absent;
its recorded interface uses a separately normalized function-valued finite-ring
presentation and also includes noncommutative rings. It therefore cannot be
applied to the literal `Scheme.proEtaleCoefficientInverseImageMap` here.
The existing theorem now reused proves invertibility of that literal canonical
map for every commutative ring and is needed to construct the canonical
restriction functor. It does not purport to
replace the old node's additional noncommutative statements.

The existing pullback-finite-locally-constant and constant-pullback nodes inspected
are for etale sheaves or fixed-module coefficient categories. The lfp immersion
transport interface likewise uses a different internal module encoding. None is
a theorem about these actual pro-etale ringed-module local models; hence the
remaining pullback interface is explicit, not an unreported coercion between
coefficient categories.

The source's printed fixed truncation cutoff must depend on upper bounds; the
already stated generic tensor theorem has the corrected formulation. This proof
uses upper bounds only and never asserts a bounded tensor or finite Tor dimension.
No target statement, unit statement, or unit proof step is bypassed or changed.

## New nodes

`lem-pur-proetale-constant-coefficient-comparison`: attaches the existing
`AlgebraicGeometry.Scheme.constantComparison_isIso` in
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`. Its unchanged proof identifies
the canonical map using the constant-sheaf adjunction. No new coefficient theorem
or duplicate proof remains.

`lem-pur-proetale-constant-module-pullback-homology`, module
`Sheaf.Paper.ProEtaleConstantModulePullbackHomology`: proved exact restriction,
its actual termwise cohomology comparison, and preservation of upper bounds.
It uses the preceding proved comparison and existing ringed-module exactness.

`lem-pur-proetale-constant-module-pullback-composition`, module
`Sheaf.Paper.ProEtaleConstantModulePullbackComposition`: proved composition of the
literal constant-module restrictions for arbitrary commutative rings. The main
finite-family induction uses this theorem; it is not an unused generalization.
The proof checks coefficient-map normalization and then applies the actual module
adjunctions. Its public statement asserts the existence of the constructed natural
isomorphism; no definition selects data from an existence theorem.

`lem-pur-proetale-finite-local-constancy-pullback`, module
`Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback`: remaining inverse-image lemma
used by both projections at each finite-refinement induction step. It has no
complexes, tensor, finite-degree support or constructible output conclusion.

`lem-pur-proetale-restricted-tensor-finite-local-constancy`, module
`Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy`: remaining local
bounded-above tensor calculation, which uses the existing generic tensor theorem
and canonical derived pullback comparison. It has no stratification and no global
constructibility hypothesis or conclusion; the main theorem supplies the genuine
finite common-stratification assembly around it.

All five nodes inherit the item's chapter/unit and blueprint ancestry, carry
verbatim Lean signatures and three kinds of recorded Mathlib searches. Existing
node edits are limited to proof, proof dependencies, proof origin and removal of
obsolete top-level tool approvals. The public-visibility repair is recorded in
`coord/changes/G2-public-constant-coefficient-comparison.md`. No forced adaptation
of another group's claimed module is needed, and no definition changes.

Repair of returned delivery: the two private helper theorems `rho_unit` and
`ring_direct` in `ProEtaleConstantModulePullbackComposition` duplicated word for
word the declarations in `ProEtaleFiniteLocalConstancyPullback`. The single
copies are now public there as
`proEtaleConstantModulePullback_rho_unit` and
`proEtaleConstantModulePullback_ring_direct`; composition imports that module and
rewrites its proof to use those declarations. The composition node records the
pullback module as a proof dependency. This removes the duplicate declarations
without changing the target theorem or any statement signature.

Repair of return at head `4768598866`: the existing theorem
`constantComparison_isIso` was private. This delivery exposes that single existing
proof in its original unclaimed module, removes the independently proved duplicate
module, updates every sandbox caller and the node attachment, and records the
consumer check in the change record. Both theorem statements mean literally the
same canonical coefficient map; there is no binder or universe distinction.

Verification: all six active sandbox modules compiled successfully through
`lcompile.py --all` (2.3–6.3 seconds per file). The existing coefficient proof
was compared against current shared sources: its only changes are its new
docstring and removal of `private`. All Lean lines are at most 100 characters.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
