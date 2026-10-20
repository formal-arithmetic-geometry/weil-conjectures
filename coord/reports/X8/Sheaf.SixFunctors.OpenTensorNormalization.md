## What changed

`exists_normalized` now has a complete categorical proof from three separate geometric
subresults. It constructs the Cartesian site comparison (also for the vertical site),
the section-normalized direct-image square, and the four tensor models. Tensor models
come from the existing independent-universe descent theorem and the resolving-pair
whiskering theorem, with no new tensor-model existence assumption.

The proof derives the invertible ordinary units from the section equations, derives
invertibility of the units after exact localization on all derived objects, and obtains
full faithfulness. It constructs the inverse beta and gamma by adjunction transposition,
proves their naturality, proves invertibility from essential-image membership, and proves
both required restriction formulas by cancellation in the adjunction equations. The
support lemmas do not assume any normalization or any chosen beta/gamma isomorphism.

The existing public definitions and proved infrastructure move to
`OpenTensorNormalizationData`, publicly reexported by the original module. This allows
the new geometric statements to refer to these data without an import cycle.
`finite_compatibility` and the final theorem retain their original signatures and bodies.
The finite tensor pin uses the equivalent subtype representation with its original
comparison and two equations; typed tensor and complex aliases avoid repeated expansion;
see `coord/changes/open-tensor-normalization-data.md`. No source-library file changes.

Validation: all five delivery modules compile without warnings (data: 51.2 seconds;
main proof: 32.7 seconds), and all 19 modules returned by the downstream query compile
against the sandbox overlay without edits. The temporary unchanged consumer copies were
removed after the checks. The three original public theorem signatures are textually
unchanged, and all original public imports are retained by the reexported data module.
No forced adaptations were necessary. Separate `#print axioms` checks show that
`tensorModel_exists`, `derivedUnit_isIso`, and `restriction_of_adjunct` use only
`propext`, `Classical.choice`, and `Quot.sound`. As expected, `exists_normalized`
still reports `sorryAx` from the three documented geometric source results.
The delivery driver timed out while appending its all-declaration axiom probes to
the two large modules; their ordinary file checks passed. An independent import-only
audit then checked all 278 noninternal declarations of the five compiled modules in
16.8 seconds: no axioms beyond the three permitted ones and the documented `sorryAx`
dependencies. The temporary audit module was removed. The independent merge check
remains responsible for rerunning its probes. A fresh conservative consumer scan is
recorded in the change record in addition to the 19 compiled consumers.

## Proved and sorry left

Original holes: 2. Discharged original hole: `SheafOfModules.OpenTensorNormalization.exists_normalized`
(node `lem-sf-open-tensor-normalization`). Its proof is a decomposition, not a net hole
closure: it uses three new, strictly separate geometric results.

The categorical assembly, tensor-model existence, site square, direct-image section
formula, ordinary and derived unit invertibility, natural transposes, and normalization
identities are proved in the private helpers of the item module. None of these helpers
contains a hole.

Holes added: 3, all public named theorems in separate modules:

- `SheafOfModules.OpenTensorNormalization.normalizedOperations_exists`,
  `Sheaf.SixFunctors.OpenOperationModels`, node `lem-sf-open-operation-models`.
  This constructs only the operation presentations from the supplied tensor models and
  supplied right square. It does not assert the normalized conclusion.
- `SheafOfModules.OpenTensorNormalization.derivedPullback_openSupported`,
  `Sheaf.SixFunctors.OpenPullbackSupport`, node `lem-sf-open-pullback-support`.
  This asserts only essential-image membership of the pullback of an open extension.
- `SheafOfModules.OpenTensorNormalization.derivedTensor_openSupported`,
  `Sheaf.SixFunctors.OpenTensorSupport`, node `lem-sf-open-tensor-support`.
  This asserts only essential-image membership of a tensor with an open extension.

Original hole retained: `SheafOfModules.OpenTensorNormalization.finite_compatibility`
(node `lem-sf-open-tensor-normalization`). Total packet holes: 4. Original holes closed
minus new holes added: 1 - 3 = -2. No claim of comparator acceptance or net proof progress.
Every new hole has its source and full natural-language proof in the declaration docstring.

The new statements were checked on identity and empty opens, zero coefficients, and
arbitrary nonflat structural maps and coefficient transitions. Their conclusions are the
usual operation construction and support assertions on the ringed diagram site itself;
none replaces its derived category by the category of levelwise derived objects.

## No longer needed

No module is withdrawn and no unit route is bypassed. The proof no longer uses
`lem-sf-exact-functor-derived-triangulated`: exact localization of the chain-level unit
suffices, with no triangulated-functor construction. It also no longer uses
`lem-weil-pbc-proetale-subcanonical`: the explicit pullback comparison and sectionwise
pushforward comparison need no subcanonicity argument. Their obsolete `tool_uses`
entries are removed, preserving the order of the other approvals. These nodes can still
be required by other parents; this is pruning of this argument, not global withdrawal. The original public
imports are retained through the data module. The original anticipated private imports
are unnecessary for the data definitions and have been removed from that module:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`

The tensor-descent module is privately imported by the actual proof. Several of the
other modules remain planned dependencies of the three geometric source lemmas or
of finite compatibility; removing their unused data-module imports does not prune them
from those arguments or authorize their withdrawal. The parent node's proof dependencies
now follow the categorical assembly and the retained finite specialization step.

## Where the brief, the DAG or earlier work was wrong

The listed slice and ringed-pullback declarations do not directly construct the given
operation records: they use different slice/element-site presentations and, in several
cases, equal site-object and morphism universes. The existing pro-etale constant-coefficient
base-change result does not cover arbitrary ring sheaves or arbitrary vertical systems.
The missing interface work is stated explicitly in the three geometric source lemmas.
Stacks 06YY supplies derived pullback; open base change additionally uses localization
and the comparison of composite adjunctions, rather than following from that tag alone.

Profiling the finite tensor record exposed expensive kernel checking of its nested
comparison types. The original structure still timed out after adding the typed aliases;
the retained subtype version passed both standalone and whole-packet single-file checks. The representation repair keeps the exact total-complex comparison,
pure-summand equation and representative equation, rather than weakening any pin.

## New nodes

`def-sf-open-normalization-data` records the existing geometric, operation, assertion
and finite-comparison data in their new module. The existing exact-derived-adjunction
node's Lean attachment moves to that module; its definition is unchanged.

`lem-sf-open-operation-models` records the independent construction of open extensions,
module pullbacks and restriction comparisons with fixed tensor models and right square.

`lem-sf-open-pullback-support` records the base-change support subargument, without
choosing a normalized base-change arrow.

`lem-sf-open-tensor-support` records the derived projection-formula support subargument,
without choosing a normalized projection arrow.

The existing parent node records the actual new assembly and retains the unfinished
finite comparison argument. Change record: `coord/changes/open-tensor-normalization-data.md`.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
