## What changed

Replaced the single postponed proof of
`AlgebraicGeometry.ProEtale.supported_finiteStage_topology_defect` by a complete
assembly argument from the existing common-field scalar models and finite-model
global Hom comparison, plus the general native global-internal-Hom detection lemma
in `Sheaf.Paper.GlobalInternalHomDetection`. The public supported-object construction,
the theorem signature, and all original public imports are unchanged.

The private helpers prove the right-adjoint uniqueness normalization of the actual
scalar unit, cancellation of the final scalar reassociation, natural transport of
shifted unit maps, and the signed shifted-triangle Hom exactness argument. The DAG
proof now records those actual operations.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.ProEtale.supported_finiteStage_topology_defect`
(node `lem-sfb-supported-finite-stage-topology-defect`).
Also proved the new, general declaration
`AlgebraicGeometry.ProEtale.FiniteModelTopologyHom.shiftedHom_bijective_of_globalInternalHom_isIso`
(node `lem-sfb-global-internal-hom-detection`) from derived adjunctions and tensor
shift compatibility. The original item has one hole closed out of one; zero holes
are added and zero remain in either delivered module. Existing named theorem
inputs retain their own proof obligations; none is duplicated or moved here.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Paper.ModuleRingedToposDerivedComparison`
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`
- `Sheaf.Paper.FiniteSubextensionsDirected`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
- `Sheaf.Paper.KFlatScalarComparisonNormalization`
- `Sheaf.Paper.CoefficientHeartLisseExtensionConstructible`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.Paper.ClosedSupportedScalarComparison`
- `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.Paper.AdicConstructibilityPredicateComparison`
- `Sheaf.Paper.ConstructibleInternalHomContinuity`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
- `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`

The item proof uses the common-field model node, finite-model global Hom
comparison node, the existing scalar-comparison definitions and tensor-Hom
adjunctions, the new global internal Hom detection node, and the triangle
exactness/triangulated-category APIs. In particular, it no longer directly performs
support/scalar coherence, field descent, internal-Hom continuity or coefficient
cohomology comparison: those remain the responsibility of the two existing model
and comparison inputs. Their transitive dependencies remain needed by those inputs;
no whole upstream module or public declaration is withdrawn.

The old direct proof dependencies
`lem-sfb-derived-internal-hom-sections-model` and
`lem-pur-sheaf-ring-derived-coefficient-adjunction` are replaced in the parent route
by the native detection lemma and the already defined scalar adjunction plus
Mathlib's right-adjoint uniqueness. The new generic lemma also avoids the
sections-model node: it proves the detection
statement using derived free/forgetful and constant-sheaf/global-sections
adjunctions, the tensor unit and tensor shift compatibility. Obsolete parent
`tool_uses` entries were deleted while preserving the order of
those retained. The removed approvals are:

- `lem-pd-module-ringed-topos-derived-comparison`
- `lem-sfb-internal-section-scalar-adjunction`
- `lem-sfb-subfield-flat`
- `lem-sfb-kflat-scalar-comparison-normalization`
- `lem-sfb-coefficient-heart-lisse-extension-constructible`
- `lem-sf-open-tensor-normalization`
- `lem-sfb-closed-supported-scalar-comparison`
- `lem-sfb-exact-open-closed-unbounded-calculus`
- `lem-sfb-successive-derived-quotient-normalization`
- `lem-sfb-dc-hom-preserves`
- `lem-sfb-constructible-internal-hom-continuity`
- `lem-sfb-qlbar-internal-hom-coefficient-comparison`
- `lem-sfb-derived-internal-hom-sections-model`
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`
- `lem-sfb-adic-constructibility-predicate-comparison`


## Where the brief, the DAG or earlier work was wrong

The section-module global Hom theorem does not directly identify the native
module-object functor `FiniteModelTopologyHom.sections`, which first forgets to
abelian sheaves and then derives global sections. The delivery proves the needed
native detection result directly, using those two
adjunctions, with no comparison to section-module global Hom required.

The older `QlbarInternalHom.scalarHomIso` and restriction-normalization statement
carry an unnecessary scalar-flatness binder for this application. The delivery
uses elementary uniqueness of right adjoints with the already available derived
tensor comparison instead, and imposes no flatness on C to B.

The restored item source and its DAG attachment have been preserved; no
quarantined archive or current source module is withdrawn. Empty supports,
zero-rank local systems and arbitrary integer shifts are retained by the exact
same public theorem statement.

## New nodes

`lem-sfb-global-internal-hom-detection` records Stacks Tag 08JA in the native
module-object/underlying-abelian-sections presentation, with its full natural
all-degree proof argument and searches. It is strictly a part of the original
argument and is proved independently of all finite-stage topology comparison
and support theory. No existing definitions or statement signatures changed, so
no change record or consumer adaptation is needed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
