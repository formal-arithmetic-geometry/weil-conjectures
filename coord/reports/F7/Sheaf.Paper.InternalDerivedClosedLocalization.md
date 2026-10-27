## What changed

Replaced the one hole in
`AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.internal_derived_closed_localization`
by an assembly proof. Existing theorem signatures are unchanged. The native restriction
functor and its monoidal instance now project from a concrete shared data package;
this reuses exactly the previous native functor and tensorator. The assigned module,
two statement modules and one data module are delivered. Private proof
helpers retain the native braiding literally. Symmetry follows by faithfulness and
the target symmetry, using the invertible comparison tensorator.

Proved the generic counit-to-transpose and counit-to-evaluation-transpose calculations,
including the unit comparison, associativity, and contravariant Hom naturality. Applied
these calculations both to the section equivalence and the actual native restriction
functor. Currying naturality and the canonical mate evaluation equation supply the native
restriction transpose identity directly. No evaluation-transpose coherence lemma
is imported for this calculation.

Proved the scalar conclusion by converting the ordinary scalar complexes into bounded
strict finite-free packages on each slice, applying the already proved strict perfect
evaluation calculation, detecting invertibility on the cover, and reflecting it through
the exact section equivalence. Rank zero handles the zero coefficient ring. The
base-change cover refines the sieve of objects mapping to the charts, so the argument
also applies to empty covers and requires no uniform bound.

The remaining two comparison results have distinct sources and statements: normalized
monoidal descent of the section equivalence, and invertibility of the actual native
derived restriction mate together with its Koszul braiding equation. They are strictly
parts of the assigned theorem. Neither contains the scalar conclusion or the generic
transpose and unit computations. The current existing section comparison supplies an
unnormalized closed model and does not supply the required strong monoidal core. The
existing `Sheaf.AlgebraicGeometry.ProEtaleDerivedRestrictionClosed` supplies restriction
of constant-coefficient sheaves; its objects are not internal modules over arbitrary
pulled-back condensed coefficient rings.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.internal_derived_closed_localization`
(node `lem-sfb-internal-derived-closed-localization`). No `sorry` remains in the assigned
module. The generic coherence and scalar-localization helpers are proved private lemmas.
The new `NativeDerivedRestrictionData` module has zero holes, including its canonical
isomorphism-criterion API.

Added exactly two holes, both named public theorems in separate modules:

- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.internal_section_monoidal_normalization`
  (`Sheaf.Paper.InternalSectionMonoidalNormalization`, node
  `lem-sfb-internal-section-monoidal-normalization`).
- `AlgebraicGeometry.ProEtale.CondensedRing.proetale_derived_restriction_closed`
  (`Sheaf.Paper.ProEtaleDerivedRestrictionClosed`, node
  `lem-sfb-proetale-derived-restriction-closed`).

This is a decomposition: one upper hole closed and two lower holes added, net minus
one hole, rather than a sorry-free proof of the entire dependency closure. No hole was
added to a definition or private lemma. No source-library declaration was changed.

## No longer needed

Removed the following direct proof imports from the assigned module:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.

The unused original public import
`Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` is also removed: every Hom
in the statement is the internal-module or ringed-site Hom, and no ordinary-module
specialization is used. There are no downstream importers of the assigned module.

The first two are unnecessary for native tensor triangulatedness, which is already
provided by the imported native `DerivedCategory.Monoidal.Shift` instances. The latter
four concern the comparison lemmas and are recorded where those lemmas need them;
they do not prove the assembly identities by themselves.

The assigned node no longer directly uses
`lem-weil-pbc-sheaf-tensor-closed`, `def-weil-size-convention`,
`lem-pe-internal-section-tensor-comparison`,
`lem-sfb-module-object-ringed-site-derived-comparison`, `lem-pc-kflat-resolution`,
`lem-weil-pbc-kflat-fixed-tensor-triangulated`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-proetale-weakly-etale-localization`,
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-weil-pbc-ringed-slice-evaluation-transpose`, and
`lem-sfb-ringed-derived-monoidal-comparisons`. Their surviving mathematical uses are
recorded in the two new comparison nodes or existing ringed perfect-duality proof.
The direct import of `Sheaf.CategoryTheory.EvaluationTransposeCoherence` is also
unnecessary: the generic restriction calculation is proved by currying naturality.
That node remains a supporting dependency of the new restriction-comparison statement.
Those supporting nodes and source modules are not withdrawn or claimed globally pruned.
Their obsolete direct tool approvals are removed from the assigned node in their original
order; the covering conservativity approval remains.

Four exploratory private Mathlib imports (`CategoryTheory.Monoidal.Closed.Basic`,
`CategoryTheory.Functor.Currying`, `CategoryTheory.Products.Basic` and
`CategoryTheory.Adjunction.Basic`) are also removed.
The optional derived-symmetry import is unnecessary: target symmetry and faithful
transport prove the double-swap identity of the already fixed native braiding directly.
The generic proofs take this equation explicitly, rather than creating another instance.

`lem-sfb-finite-free-dual-chain-comparison` and its module
`Sheaf.Paper.FiniteFreeDualChainComparison` are not used: the already proved normalized
ringed-site strict-perfect evaluation calculation suffices. The replacement retains the
unit's finite-free local models and covering-detection route. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan's comparison statements do not directly provide all the native
normalizations its conclusion requests: a `TensorComparison` is not a coherent strong
monoidal core, and an isomorphism on ringed-site slice Hom objects does not alone identify
the canonical internal-module pullback mate. The new statements isolate these missing
comparison results. They are not replacements for the generic transpose calculation or
for the scalar local-model argument, both of which are proved here.

The resumed sandbox's reference clock changed from start 1792758420 to
1792773480.604933. The interrupted attempt and resumed attempt did not start a delivery;
compile logs are retained in the sandbox scratchpad. The later compile result identifiers
include `7a4d2ccd9d8aa81432946f42` and `c14424d85c0c725561adb260`; no delivery
attempt preceded the resume. The first subsequent delivery attempt
(`scratchpad/delivery1.log`) pushed nothing because the main module exceeded 60 seconds.
The explicit restriction normalization above repairs that conversion cost.
No launcher metadata was modified.

## New nodes

`lem-sfb-internal-section-monoidal-normalization` records the coherent normalization of
section-action derived tensor and actual evaluation. It is stronger than the existential
section comparison alone because it fixes the representative tensorator, symmetry and
unit through a normalized ringed-site model. Its proof uses the existing section-tensor
comparison, resolving tensor descent, and evaluation-normalized derived Hom comparison.

`lem-sfb-proetale-derived-restriction-closed` records the canonical closed mate for actual
internal-module derived pullback, with the existing native tensorator and Koszul braiding.
It follows the slice restriction argument of Stacks 08JB with coefficient action
transport. It is distinct from the constant-coefficient sheaf restriction node
`lem-weil-proetale-derived-restriction-closed-monoidal`.

`def-sfb-native-derived-restriction-data` records a concrete pair of the native
restriction functor and its already specified monoidal structure. It adds no hole,
choice, or new tensor map. Its proved isomorphism-criterion API uses the existing
canonical natural isomorphism to exact termwise pullback. This avoids expanding the
geometric pullback when the proof compares independently inferred monoidal instances.
The data module is a definition repair. Explicitly generalizing the data and its
monoidal field reduced the restriction helper's measured kernel checking to 345 ms;
the original calculation took about 32 seconds. The full argument remains in its
assigned module. In the scalar proof the slice localization comparison is composed
through the explicit `restrictionComplexIso`, instead of relying on conversion of
identity scalar restriction. This reduced the scalar helper from about 28 seconds to
11 seconds, including a kernel check under one second. No scalar proof was split
into another module. The final reflection step reuses the already established
`ClosedTransport` formula rather than repeating its counit calculation.
The complete assigned module then compiled without warnings in 54.5 seconds
(`scratchpad/main117.log`, compile identifier `9d046202ef07db9f30731acf`).
After a second delivery compile exceeded the limit, the localization helper was
abstracted over its ringed site, while retaining the explicit normalization and shared
closed-transport proof. The resulting complete module compiled cleanly in 56.4 seconds
(`scratchpad/main118.log`, compile identifier `d0456019b02c4a59911f44e6`).

All three new nodes have three recorded Mathlib search kinds, sourced constructions
or proof steps, and verbatim Lean attachments. The representation changes are recorded
in `coord/changes/f7-derivedRestriction-native-data.md` and
`coord/changes/f7-restrictionMonoidal-native-data.md`. Downstream checks report no
external consumers of either definition. No forced consumer adaptation is required.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
