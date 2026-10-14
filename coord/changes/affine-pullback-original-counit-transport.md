# AlgebraicGeometry.canonicalPullbackAdjunction_eq_original_transport

## Reason

Expose the precise relation between the composition-counit adjunction and the
original-counit adjunction, so that consumers can change presentation without
asserting equality of independently normalized adjunctions. This is a partial
class-2 repair and does not discharge the module's remaining REPAIR marker.

## Old

The following existing definition is retained verbatim:

```lean
def canonicalPullbackAdjunction {T S : Scheme.{u}} (g : T ⟶ S) :
    derivedPullback g ⊣ schemeDerivedDirectImage g :=
  Classical.choose (exists_schemeDerivedAdjunction g
    (hAdd := (Classical.choose exists_derivedPullbackComposition) g)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) g)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) g))
```

No transport theorem was previously exposed by this module.

## New

The existing definition is unchanged. Add these proved public equations:

```lean
theorem canonicalPullbackAdjunction_eq_original_transport {T S : Scheme.{u}} (g : T ⟶ S) : canonicalPullbackAdjunction g = (schemeHomOriginalPullbackAdjunction g).ofNatIsoLeft (schemeHomPullbackCounitIso g).symm

theorem canonicalPullbackAdjunction_unit_original {T S : Scheme.{u}} (g : T ⟶ S) (A : schemeDerivedCategory S) : (canonicalPullbackAdjunction g).unit.app A = (schemeHomOriginalPullbackAdjunction g).unit.app A ≫ (schemeDerivedDirectImage g).map ((schemeHomPullbackCounitIso g).inv.app A)

theorem canonicalPullbackAdjunction_counit_original {T S : Scheme.{u}} (g : T ⟶ S) (B : schemeDerivedCategory T) : (canonicalPullbackAdjunction g).counit.app B = (schemeHomPullbackCounitIso g).hom.app ((schemeDerivedDirectImage g).obj B) ≫ (schemeHomOriginalPullbackAdjunction g).counit.app B

theorem canonicalPullbackAdjunction_homEquiv_original {T S : Scheme.{u}} (g : T ⟶ S) (A : schemeDerivedCategory S) (B : schemeDerivedCategory T) (f : (derivedPullback g).obj A ⟶ B) : (canonicalPullbackAdjunction g).homEquiv A B f = (schemeHomOriginalPullbackAdjunction g).homEquiv A B ((schemeHomPullbackCounitIso g).inv.app A ≫ f)

theorem canonicalPullbackAdjunction_homEquiv_symm_original {T S : Scheme.{u}} (g : T ⟶ S) (A : schemeDerivedCategory S) (B : schemeDerivedCategory T) (f : A ⟶ (schemeDerivedDirectImage g).obj B) : ((canonicalPullbackAdjunction g).homEquiv A B).symm f = (schemeHomPullbackCounitIso g).hom.app A ≫ ((schemeHomOriginalPullbackAdjunction g).homEquiv A B).symm f
```

The comparison existence proof chooses the transported original adjunction and
uses the first equation to prove its equality to the required legacy adjunction.
It uses the same comparison, tensor and sections dependencies as before.

The new scheme transport theorem and its generic uniqueness theorem are in their
own modules and DAG nodes. The scheme transport module is a proof-only import of
the item. GlobalHomOriginalCounitNormalization is a public import because the
new equation signatures refer to its original adjunction and counit isomorphism.
Existing public definitions, hypotheses, universes and instance parameters are
unchanged; no target definition changes meaning and no target review is reopened
by this delivery. The definition-changing full counit repair remains open.

## Users

The table includes all 16 modules reported by
`tools/downstream.py Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap --uses
canonicalPullbackAdjunction`, and both new modules. The returned consumer is included unchanged below.
Transitive downstream modules receive no changed definition or signature.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelFactorization | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelMate | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | F2 | Uses the newly proved transport in its comparison proof; existing signatures and definitions retained. |
| Sheaf.AlgebraicGeometry.AffinePullbackSectionsModelUnit | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffinePullbackSectionsUnitUncancelled | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenComparisonMateIso | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization | unclaimed | Existing definition and signatures unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Returned build check e086dc9a4be846f5: the current baseline already contains overFunctor.{u} and compiles unchanged against the delivery overlay; no adaptation. |
| Sheaf.AlgebraicGeometry.OriginalCounitAdjunctionTransport | F2 (new) | Proves the scheme-level transport from normalized-adjunction uniqueness. |
| Sheaf.CategoryTheory.DerivedCategory.AdjunctionNormalization | F2 (new) | Generic normalization uniqueness; no existing users. |

## Status

landed 20261014T120308-L-2450025 2026-10-14 (merge of deliver/F2/Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap)
