## What changed

The item module proves `coefficient_colimit_formula` and
`qlbar_internalHom_coefficient_comparison` with their original signatures. The existing
auxiliary proofs and U4's already-landed `coefficient_comparison_roof` proof are retained.
They and the nine unchanged definitions move to
`Sheaf.Paper.QlbarInternalHomCoefficientData`, publicly re-exported by the item.
All nine definition bodies are byte-identical to current source; every existing
public declaration keeps its name, signature, attributes and visibility.

The new proved support module `Sheaf.Paper.StrictFiniteFreeInternalHomColimit`
contains the generic eleven-clause strict cocone formula, including its normalization
and naturality equations. This was extracted after profiling the full proof and
limiting unfolding of derived-category constructions. Its theorem is fully proved;
it introduces no hole and keeps every existing public declaration of the item.

Private proved helpers identify the prescribed coefficient cocone as a module colimit,
transport finite freeness through the section equivalence, and transport the strict
numerator and denominator along isomorphisms. The strict formula specializes
`filteredColimit_comparison`; `internalHom_filtered_continuity` and tensor-colimit
preservation supply its separate Hom postcomparison. The final proof chooses a K-flat
representative of K and a bounded-below representative of L, then uses the existing
normalized evaluation-roof equation and conservative scalar restriction. Exactness of
the chosen ordinary scalar model follows by transporting its right adjoint with the
roof's existing restriction isomorphism and using uniqueness of left adjoints. There is no
boundedness assumption on the internal Hom complex.

The new imports are private proof imports:
`Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit`,
`Sheaf.Paper.StrictFiniteFreeInternalHomColimit`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, and
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`.
Import-direction checks permit the new dependencies. The node's proof, proof dependencies and
proof origin now describe this argument. No public definition, target statement,
existing signature or source-library file is changed. The support extraction is
recorded in `coord/changes/qlbar-internal-hom-support-extraction.md`, with all five
downstream modules audited and the coefficient-module-cocone Lean attachment updated.

The generic K-flat resolution theorem is used only to choose a representative with a
quasi-isomorphism to a fixed complex: its derived object is fixed up to the very
isomorphism used downstream. No arbitrary coefficient object is chosen from mere
existence. The proof works for the identity finite-field stage, the empty site and zero
inputs; finite product/coproduct transport does not need a chosen compatible family of
bases.

## Proved and sorry left

The copied current item had two holes, after U4's roof proof had landed:

- Closed: `AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficient_colimit_formula`.
- Closed: `AlgebraicGeometry.ProEtale.QlbarInternalHom.qlbar_internalHom_coefficient_comparison`.

There are no remaining `sorry` declarations in the item and no holes added elsewhere.
This is a proof from existing dependency declarations, with zero split-off unproved obligations.
All three delivery modules compile without Lean errors or warnings. The final
item compile completed in 48.5 seconds after final redundant-import cleanup.
The unchanged `FiniteModelTopologyComparisonMaps` and `FiniteModelTopologyDerivedHom`
consumers compile; the latter completed in 34.8 seconds.
The unchanged `QlbarBoundedTensorColimit` type-checks but exceeded 60 seconds (95 seconds)
against this packet (a subsequent profile finished in 85.7 seconds). A separate control using only the published build and the unchanged
consumer also exceeded the limit (88 seconds), without any type errors. This timing
issue is already present in the baseline; the consumer is not adapted.
The delivery tool performs the final independent compile and preflight checks. The new support theorem
`AlgebraicGeometry.ProEtale.QlbarInternalHom.strictColimitFormula_of_finiteFree`
is proved, not a split-off obligation (node
`lem-sfb-strict-finite-free-hom-colimit-formula`).

## No longer needed

The proof does not use `lem-sfb-qlbar-tail-finite-free-algebra-presentation`
(`Sheaf.Paper.QlbarTailFiniteFreeAlgebraPresentation`): `fieldDiagram`,
`coefficientModules` and the already-proved canonical coefficient-complex colimit
supply exactly the filtered index, finite freeness and colimit required by the strict
comparison. The section equivalence on complexes and degree-zero evaluation preserve
that colimit.
Its proof-dependency edge is removed from this node. The separate public
`coefficientRingColimit` clause remains proved by the existing final-functor argument.
The theorem `lem-sfb-qlbar-tail-module-colimit` is also unused by this proof.
Its module remains publicly imported
because the existing statements use `qlbarTailStage` and `qlbarTailVertex`; those
definitions and their DAG attachment are retained. No declaration or module is
withdrawn. No inherited public import is removed. The generic continuity and total-bifunctor-colimit
proof imports are now used privately by the support module rather than directly by
the item; their mathematics is still needed. The direct proof imports of
`InternalSectionHomComparisonData`, `InternalSectionTensorComparison`,
`ModuleSheavesColimitsForgetful` and the Mathlib sheaf Grothendieck-axiom module
are removed from the item after the support extraction. The first two are already
publicly available through its remaining imports; the latter two are used by the
generic support module. No required mathematics is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The initial read overlapped U4's landing of the roof assembly; the actual copied and
compiled baseline already contains that proof. Consequently this delivery closes two
holes, not three. The former DAG step asking for the combined finite-free tail-algebra
presentation was stronger than this proof needs; the direct module-colimit route
preserves the node statement and the unit's restricted-Hom route.

The canonical coefficient-complex colimit, K-flat resolution, total-tensor colimit
preservation and independent-universe tensor-colimit lemmas are generic tools,
not alternate unit routes. No mathematical statement or definition-body repair and no forced adaptation
is needed. The change record documents the unchanged declaration move and re-export.

The previous attempt's instance failures were caused by changing the inherited
transparency setting before `scalarHomIso` and its restriction theorem. Restoring
the current library's setting makes that restriction argument compile cleanly.
The original complete packet still exceeded the per-file limit, so profiling led
to local opacity annotations for the derived-category constructions and extraction
of the proved generic strict-cocone assembly. A further profile showed that the
existing coefficient data and normalized roof must be checked separately; they
were moved unchanged to the public support module. The current remote brief
explicitly allows this split after improving the slow definitions. No launcher
tool was changed.

## New nodes

`lem-sfb-strict-finite-free-hom-colimit-formula` is a fully proved generic assembly
of the existing strict finite-free comparison and filtered-continuity results. It
retains the actual specified cocone, the separate Hom postcomparison, both vertex
quasi-isomorphisms, evaluation normalization and both naturality squares. It has
its own module, `Sheaf.Paper.StrictFiniteFreeInternalHomColimit`. This is a part of
the existing argument, with no new assumption, definition change, or sorry.

The unchanged declaration move is recorded in
`coord/changes/qlbar-internal-hom-support-extraction.md`; its existing definition
node is reattached to the support module, with its mathematical fields unchanged.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
