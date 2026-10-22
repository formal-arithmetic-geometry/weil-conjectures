## What changed

Replace the proof hole in `AlgebraicGeometry.Scheme.finiteField_lisse_internalHom`
by the finite-free evaluation and exact-Hom argument. The existing public instance,
two public functor definitions, and target statement are unchanged.

Private helpers turn finite constant models into finite free charts and show that the
dual has finite constant models. The proved scalar evaluation and both naturality lemmas are reused from
`Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly`. A dual-basis calculation
proves the corresponding presheaf evaluation locally bijective, and sheafification
gives its natural sheaf isomorphism. Tensor-Hom
adjunction then proves exactness of Hom from a finite local system. The Hom-complex
projection formula, exactness and functorial K-injective resolution give the cohomology
comparison; product localization descends its naturality to arbitrary derived complexes.
The cohomology and dual-tensor comparisons are organized over an arbitrary coefficient
sheaf and an exact-source full subcategory before specializing to the constant ring.
The existing resolution-existence theorem supplies the replacement functor, augmentation
and their properties together.
The existing constructible-tensor helper proves constructibility, and additive Hom
preserves the vanishing outside the original interval.

The complete module compiles through `lcompile.py` in 52.2 seconds without warnings.
Its public declarations and public imports were compared with the current source: the
instance, both functor definitions and the theorem signature are unchanged. All new
helpers are private and proved. A second complete compile with `#print axioms` passes
in 53.7 seconds; it reports `propext`, `Classical.choice`, `Quot.sound` and inherited
`sorryAx` from existing dependencies. No new axiom or admitted helper is introduced. The categorical descent is proved over an arbitrary
abelian category; a proved equality for the mapped-complex functor handles the two
definitionally equal presentations of the sheaf category’s additive structure.

The proof-context commands and seven proved private instances are recorded in
`coord/changes/A5-finite-field-lisse-internal-hom-proof-context.md`. Preflight required
this record; the downstream scan reports zero current importers.

## Proved and sorry left

Original hole: `AlgebraicGeometry.Scheme.finiteField_lisse_internalHom` (one).
Closed: `AlgebraicGeometry.Scheme.finiteField_lisse_internalHom` (one of one).
Added: zero. Remaining in this module: zero. Split off: zero.
Every private helper is proved; no new residual statement or module is introduced.

## No longer needed

The following direct proof imports and their direct DAG dependencies are unnecessary
for this item's argument. They are absent from the proof's new import closure:

- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
  (`lem-sfb-proetale-object-inverse-image-restriction`).
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
  (`lem-weil-pbc-ringed-topoi-module-pullback-tensor`).
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
  (`lem-pur-site-restriction-module-adjunction-exact`).
- `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`
  (`lem-cbc-proetale-stalk-conservative`).
- `Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant`
  (`lem-exc-proetale-pullback-locally-constant`).

Exactness follows from evaluation and adjunction, and constructibility follows from the
proved finite-line module's general constructible-tensor helper. Thus the separate
slice-exactness, stalk-conservativity, and stratumwise pullback argument is unnecessary.

The direct imports `Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse`
(`lem-sf-proetale-lisse-finite-models`) and `Sheaf.Paper.ProEtaleFiniteModelStalks`
(`lem-weil-pbc-proetale-finite-model-stalks`) are also removed from this module.
Their modules remain transitively imported by `Sheaf.Paper.ProEtaleConstantModuleConstructibility`,
which the constructible-tensor helper uses. They are not withdrawn.

The obsolete approvals for these seven direct dependencies are removed from this
node’s `tool_uses` list. No library declaration, source module, or blueprint unit is deleted. No global
unreachability of these modules from the other targets is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing hypothesis was found. The original five-step mathematical
plan is valid. Its exactness and constructibility steps can use the adjunction and
existing constructible-tensor infrastructure, with fewer direct dependencies. The
recorded monoidal unit is definitionally the structure sheaf in the target, so the
existing bounded-evaluation module's scalar comparison applies directly.

The ordinary, uncompleted derived category and all naturality requirements are retained.
Empty sites, rank zero, zero complexes, and a single-degree interval need no exceptions.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
