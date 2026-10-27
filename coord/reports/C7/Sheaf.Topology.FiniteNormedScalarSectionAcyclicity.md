## What changed

Filled the proof of `Profinite.finiteNormedScalar_section_acyclicity` without changing
its statement, definitions, public imports, or existing consumers. The proof uses
finite-dimensional completeness, a finite-family scalar Cech input, a proved
profinite Cech-to-derived criterion, and an arbitrary-resolution module/abelian
comparison. The remaining two inputs are separate sourced theorem obligations.

The new `Sheaf.Topology.ProfiniteCechDerivedVanishing` is fully proved. Coherent
covering sieves contain finite effective epimorphic families; these reindex to
finite ordinals and are jointly surjective. Chosen-product and categorical Cech
complexes agree. The categorical finite Cech criterion then gives derived
vanishing at the actual coefficient universe `u + 1`. Its private comparison
helpers adapt Bin Wu's proved `SiteCechMathlibComparison` argument with independent
index and coefficient universes, preserving the shared source interface.

The augmentation's injectivity, exactness at degree zero, and its actual homology
map being an isomorphism are proved directly from the mapped kernel fork, without
using the module comparison in degree zero. Positive homology vanishing is
converted to exactness of each later differential pair. Empty index families are
handled directly: every cochain group, hence every homology group, is zero.

All edits are inside the item module and three new modules, with their DAG nodes.
No existing dependency module or source-library declaration was changed.

Validation: all four modules compiled cleanly through `lcompile.py`. The proved
Cech-to-derived module took 8.1 seconds and the final item compile took 5.7 seconds;
the two obligation modules took 2.9 and 3.2 seconds. All are below 60 seconds.

## Proved and sorry left

Closed the original hole in `Profinite.finiteNormedScalar_section_acyclicity`
(node `lem-sfb-finite-normed-scalar-section-acyclicity`). The item has zero holes.
Also proved `Profinite.isZero_rightDerived_eval_of_profinite_cech`
(node `lem-sfb-profinite-cech-derived-vanishing`) without any new sorry.
The private empty-family helper and every comparison helper are proved.

Added exactly two holes, each the whole proof of its named public theorem:

- `Profinite.finiteNormedScalar_cech_vanishing`
  (`lem-sfb-finite-normed-scalar-cech-vanishing`): transport the existing continuous
  primitive theorem to the finite-family complex for nonempty finite families,
  including the identification of the extending and spectral norm topologies.
- `Profinite.nonempty_internalModule_eval_homology_iso`
  (`lem-sfb-profinite-internal-module-evaluation-comparison`): transport arbitrary
  internal module resolutions and the existing ringed-site comparison through
  the sectionwise equivalence and the common-universe lifted site. Only positive
  degrees are required; no degree-zero normalization remains in this obligation.

This is a decomposition of one original hole into two strictly separate parts of
its argument, not a net hole reduction: one closed, two added, net minus one.
The first part has no derived functors or resolutions; the second is independent
of p-adic coefficients and Cech vanishing. The assembly and the entire intermediate
Cech-to-derived criterion are real Lean proofs. No sorry is inside a definition.

## No longer needed

- Removed the direct proof import
  `WeilConjectures.CategoryTheory.SiteCechVanishingCriterion` and the corresponding
  direct dependency `lem-weil-pbc-site-cech-vanishing-criterion`. The categorical
  finite Cech criterion is proved applicable in the new profinite bridge instead.
  Its obsolete approval was removed from the item's `tool_uses` list.
- `lem-sfb-profinite-free-hom-resolution-evaluation` and its module
  `Sheaf.CategoryTheory.ProfiniteFreeHomResolutionEvaluation` are unnecessary for
  this argument. The resolution is already given, and exactness and preservation
  of injectives follow from the sectionwise equivalence. No free parameter, internal
  Hom, or derived-Hom evaluation specification is used. Other parents may need it.
- Removed the direct imports of `Sheaf.Topology.NormedScalarProfiniteCechExact`
  and `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison` from the item.
  These are retained as inputs to the respective lower obligations; they are not
  claimed globally pruned. The module/abelian comparison approval is retained.
- The original size convention and sites/cohomology definitions remain statement
  dependencies. The proof uses actual profinite objects and coefficient universe
  `u + 1`; it does not need an additional small skeleton assumption.
- All existing public imports remain unchanged to preserve their reexports.
  No module is withdrawn and no source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG also described completeness as part of the analytic primitive
lemma, but its current Lean signature states the continuous primitive assertion
only. Completeness is proved separately using `FiniteDimensional.complete`.

The mathematical plan is sound, but two published Lean interfaces do not directly
fit its universe choices. `isZero_H'_of_siteCech_vanishing` expects a small category
with coefficient universe equal to its object and hom universe. Here `Profinite.{u}`
has objects in `Type (u + 1)`, arrows in `Type u`, and coefficient groups in
`Type (u + 1)`. The categorical finite criterion has the needed interface.

Also, `SiteCechComplex.mathlib_complex_iso_exists` ties the index universe to the
coefficient universe. Finite ordinals and the present coefficient groups have
different universes. A private generalization of its existing proof resolves this
without changing any published signature. The current module/abelian evaluation
comparison has a similar common-universe small-category restriction: its residual
site/equivalence transport is explicitly stated as the second lower obligation.

The item's inherited blueprint ancestor is null; its recorded chain is retained,
with the item prepended for each new node. The unit's realized route is preserved.

## New nodes

`lem-sfb-finite-normed-scalar-cech-vanishing` states the nonempty finite-family part
of original step 1, sourced to Bhatt--Scholze 4.3.9(2)--(4). Its docstring gives the
finite-ordinal reindexing, clopen tuple decomposition, differential comparison,
spectral-norm identification, and primitive transport. The empty family is proved
in the parent. This theorem remains sorry.

`lem-sfb-profinite-cech-derived-vanishing` is the proved universe-correct
application of Stacks 03F9 to the coherent profinite site. It uses the existing
categorical finite Cech criterion as a coefficient-independent tool and proves all
covering and comparison hypotheses. Its private helpers are proved.

`lem-sfb-profinite-internal-module-evaluation-comparison` states original step 3
for arbitrary internal rings, modules and resolutions, in positive degree only,
using Stacks 00YV and 03FD. Its proof plan retains the original sectionwise and
module/abelian comparison dependencies and makes the universe transport explicit.
This theorem remains sorry. Three search kinds are recorded for each new node.

No change record is necessary: existing statements, definitions and public
interfaces are unchanged.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
