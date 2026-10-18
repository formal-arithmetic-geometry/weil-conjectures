## What changed

Repaired the returned delivery by removing the duplicate private
`restrictSheafificationComparison` and `restrictSheafificationComparison_isIso`
proofs from `Sheaf.Paper.ConstantCoefficientLisseRestriction`. The comparison
definition and its isomorphism theorem are now exported from the existing
`Sheaf.Paper.ConstantCoefficientLocalModelsComparison` module, and the
restriction module imports and uses those declarations.

Replaced the proof of `SheafOfModules.locallyConstantFiniteTypeModules_reduction_pow`
with positive-natural-number induction using the single successor statement
`SheafOfModules.locallyConstantFiniteTypeModules_reduction_succ`, then proved the
nilpotent specialization through the bijective quotient map. The original signature
and all original public imports are unchanged.

Added `Sheaf.Paper.ConstantCoefficientScalarEquivalence`, whose public theorem
`SheafOfModules.locallyConstantFiniteTypeModules_of_scalarExtension_bijective` is
proved with no new holes. Its proof constructs the equivalence on module sheaves,
identifies ordinary and derived scalar extension with the inverse restriction
functor, transports homology and constant finite local models, and cancels the
coefficient equivalence. All supporting helpers are private and proved.

Factored out `Sheaf.Paper.ConstantCoefficientLisseRestriction` and proved
`SheafOfModules.locallyConstantFiniteTypeModules_restrictScalars_surjective`.
The coefficient-equivalence theorem applies it using the surjectivity of its
bijective map. The restriction result also supplies the quotient-map preservation
needed by the successor step. This avoids duplicating the sheafification and
finite-module transport argument.

Proved `SheafOfModules.exists_constantCoefficientRing_localModels_comparison` in
`Sheaf.Paper.ConstantCoefficientLocalModelsComparison`. It constructs the
canonical constant-ring isomorphism, proves its compatibility with sheafification
units, and compares finite constant local models. Proved
`SheafOfModules.locallyConstantFiniteTypeModules_of_distinguished` in
`Sheaf.Paper.ConstantCoefficientLisseTriangle` from that comparison, the existing
Serre theorem and triangulated closure of a cohomology property. Neither module
introduces a hole.

Added `Sheaf.Paper.NilpotentReductionStep` to isolate one filtration step of
Tag 094I. It assumes the reduction modulo J and the previous reduction modulo J^n,
and concludes only the successor reduction. It does not assert the induction over
all positive powers or the nilpotent specialization. The outer proof performs
those operations explicitly in Lean. Updated the existing node's proof route and
added nodes for the new statements. No existing statement or definition changes;
no change record is needed.

## Proved and sorry left

Closed the original occurrence in
`SheafOfModules.locallyConstantFiniteTypeModules_reduction_pow`.
The assigned module contains zero `sorry` occurrences.

Proved `SheafOfModules.locallyConstantFiniteTypeModules_of_scalarExtension_bijective`,
`SheafOfModules.locallyConstantFiniteTypeModules_restrictScalars_surjective`,
`SheafOfModules.exists_constantCoefficientRing_localModels_comparison`,
`SheafOfModules.locallyConstantFiniteTypeModules_of_distinguished`, and their
private helpers, without any new holes.

Added one hole:
`SheafOfModules.locallyConstantFiniteTypeModules_reduction_succ`
(`lem-weil-pbc-nilpotent-reduction-step`). It still needs the coefficient filtration
triangle, the balancing identification and boundedness needed for Tag 094H, and
the identification of the restricted derived coefficient objects. Triangle closure
and preservation of local models under quotient scalar restriction are now proved.
Its module imports the existing stated lemmas that supply these ingredients, and its
docstring and node contain the complete source argument.

Thus this is a decomposition: one original hole closed and one new, strictly
one-step hole added, for net zero holes closed. It is not reported as a complete
proof of the original mathematical assertion. The coefficient-isomorphism branch
is fully proved from the existing library declarations.

Validation: `lcompile.py --all` compiled all six final modules successfully.
The restriction and scalar-equivalence modules were previously checked without
warnings in 21.5 and 35.6 seconds; comparison compiled in 22.7 seconds. The final
triangle, successor and assigned modules compiled in 7.9, 5.0 and 4.1 seconds.
Only the named successor theorem retains its documented `sorry`. Edge cases checked mathematically: J=0, J=B,
n=1, the zero coefficient ring, empty covering sieves, and arbitrary derived-category
instances. The use of an ideal-indexed predicate in induction preserves those
instances when rewriting `J^1 = J`.

## No longer needed

Removed these proof-only imports from the assigned module, transferring the ones
needed for the single successor step to its new module:

- `Sheaf.Paper.CohomologyInWeakSerreSubcategory`
- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.BoundedFlatReplacement`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`
- `Sheaf.Paper.LocallyConstantTensor`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The former local sheafification-comparison helper and its isomorphism proof are
also no longer needed in the restriction module; they are imported from the
local-model comparison module, where the existing statement is shared.

The original proof dependencies for the filtration argument remain needed below
`lem-weil-pbc-nilpotent-reduction-step`; they are not globally pruned. The final
nilpotent identification uses the proved original, equal-universe
`derivedChangeOfRings` declaration and exact derived equivalences. No unit statement
or realized unit step is bypassed. An import-graph comparison shows that
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients` and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` are no longer in
this item's import closure. The equal-universe declarations suffice here, because
the site's object and morphism universes and the coefficient universe are all u.
Other target routes may still import the general versions. No module is withdrawn.
The original tool approvals are retained because their tools remain in the
successor argument.

The successor argument now forms its triangle directly over B/J^(n+1). This uses
the proved surjective-restriction theorem for the two outer terms and the proved
triangle-closure theorem over that quotient ring. It eliminates the separate
quotient-linear descent of B-module local models in the original proof plan.

## Where the brief, the DAG or earlier work was wrong

The Serre theorem uses constants sheafified in `RingCat`, whereas reduction uses
constants sheafified in `CommRingCat` followed by forgetting commutativity. These
are canonically isomorphic, not definitionally equal: a direct `rfl` test fails.
The new constant-module comparison and triangle-closure theorems resolve this
interface mismatch. No existing statement was found false.

The current `lem-pur-derived-change-of-rings` attachment names
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, whose file is absent in
the shared checkout. The existing, proved equal-universe
`SheafOfModules.derivedChangeOfRings` in `Sheaf.Algebra.Homology.DerivedChangeOfRings`
provides exactly the universal derived pair needed here. Similarly the equal-universe
`CochainComplex.exists_isKFlatResolution` supplies the K-flat resolution formulation
used by the existing Tag 094H theorem. The general independent-universe interfaces
are unnecessary for this item's stated universes; their shared node attachments
were not edited.

The compile service once returned no answer within its request timeout and asked
for a retry. The retry succeeded. No launcher script was changed or bypassed.

## New nodes

`lem-weil-pbc-nilpotent-reduction-step` records the one-step coefficient filtration
obligation, with the original Tag 094I proof dependencies, source and complete
argument. It is the sole new hole.

`lem-weil-pbc-constant-coefficient-scalar-equivalence` records the fully proved
reflection of finite local constant cohomology along bijective constant scalar
extension, without boundedness or Noetherianity assumptions. Its proof is independent
of nilpotent reduction and uses uniqueness of derived functors and explicit local
module transport. Three kinds of Mathlib search are recorded in each new node.

`lem-weil-pbc-constant-coefficient-lisse-restriction` records the fully proved
preservation of finite constant local models along a surjective coefficient map.
It uses the sheafification adjunction and finite generation in a scalar tower,
and is actually applied by the coefficient-equivalence proof.

`lem-weil-pbc-constant-coefficient-local-models-comparison` records the proved
comparison of the constant commutative-ring construction with ring-valued constant
sheaves, including their finite local models and compatibility with the units.

`lem-weil-pbc-constant-coefficient-lisse-triangle` records the proved closure of
finite locally constant cohomology under the middle term of distinguished triangles
for the constant coefficient ring used by scalar extension. Its proof transports
the existing Serre theorem across the comparison, rather than assuming the two
constant-ring constructions are definitionally equal.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
