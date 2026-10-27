# PointFiniteFreeSectionsTensorData

## Reason

Reviewer correction (cc review of 440ef0af932f, re-applied by the cc review of 0decb536bb64, 2026-10-25; the 440ef fix was lost only because its override file lacked the `.change` suffix): `PointFiniteFreeSectionsTensorData` is kept as the
original published structure, byte for byte (the delivery's replacement of it by an `abbrev` of
`PointFiniteFreeSectionsTensorCore` made the unchanged importer `Sheaf.Paper.PointDerivedSectionsTensorDescent`
fail with deterministic heartbeat timeouts at lines 345, 470 and 472 and a kernel error at 514 (reproduced again on head 0decb536bb64), which declare
`completedIntegralCoefficientSheafUnrestricted` locally irreducible). The proof builds the core record and copies its
29 fields into the original structure (`pointFiniteFreeData`); every field type agrees definitionally.

What other modules now see in addition (no existing signature or body changes):

- `PointFiniteFreeSectionsTensorCore` (structure over abstract coefficient data) and `pointFiniteFreeCoreEvaluation`;
- `PointFiniteFreeSectionsTensorCoreData`, the core specialized to the published completed constructions;
- two proved global `PreservesZeroMorphisms` instances, `pointRestriction_zero` and `pointEvaluation_zero`
  (Prop-valued; they keep elaboration from unfolding the completed functors).

The theorem statement `point_finite_free_sections_tensor` is verbatim unchanged.

## Delivery's original reason (superseded)

The original monolithic record repeats inverse-limit and completed change-of-rings constructions in every projection. Its type checks, public projection generation and artifact export approach the 60-second compile limit before the proof is added. Abstract these constructions as parameters of `PointFiniteFreeSectionsTensorCore`, and retain `PointFiniteFreeSectionsTensorData` as its specialization to exactly the original published constructions. (Superseded: the original structure is retained; the item with the original structure and the conversion compiles in about 34 s on the review server.)

## Old (unchanged, retained verbatim)

```lean
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The complete assertion: normalized coefficient identifications, a common global
basis, local tensor coordinates, the unique linear natural comparison, exactness,
and its unbounded termwise complex comparison. Each field is a clause of the node.
The inverse formulas fix every coordinate isomorphism, rather than postulating an
unrelated abstract isomorphism. The choice of basis is confined to these coordinates.
Source: Bhatt--Scholze 4.2.12 and 6.8.2(1), Stacks 03EK; DAG statement
(blueprint: lem-weil-point-finite-free-sections-tensor). -/
structure PointFiniteFreeSectionsTensorData where
  coefficientE : Padic.coefficientExtensionIntegers l E ≃+*
    (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
      (pointFiniteFreeFinal k)
  coefficientL : Padic.coefficientExtensionIntegers l L ≃+*
    (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k))).obj.obj
      (pointFiniteFreeFinal k)
  constantE : ∀ a, coefficientE a =
    integralScalarConstant l E (Spec (.of k)) (pointFiniteFreeFinal k) a
  constantL : ∀ a, coefficientL a =
    integralScalarConstant l L (Spec (.of k)) (pointFiniteFreeFinal k) a
  quotientE : ∀ n a,
    (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
      (pointFiniteFreeFinal k) (coefficientE a) =
        integralScalarFiniteConstant l E (Spec (.of k)) n (pointFiniteFreeFinal k) a
  quotientL : ∀ n a,
    (completedIntegralCommRingProjectionUnrestricted l L (Spec (.of k)) n).hom.app
      (pointFiniteFreeFinal k) (coefficientL a) =
        integralScalarFiniteConstant l L (Spec (.of k)) n (pointFiniteFreeFinal k) a
  coefficient_compatibility : ∀ a,
    (completedCoefficientMap l E L ι (Spec (.of k))).hom.app (pointFiniteFreeFinal k)
      (coefficientE a) = coefficientL (integralScalarIntegerInclusion l E L ι a)
  basis : Fin (completedScalarRelativeDegree l E L ι) → Padic.coefficientExtensionIntegers l L
  integral_basis : Function.Bijective
    (fun a : Fin (completedScalarRelativeDegree l E L ι) →
        Padic.coefficientExtensionIntegers l E ↦
      ∑ i, integralScalarIntegerInclusion l E L ι (a i) * basis i)
  sheafBasis :
    (pointFiniteFreeRestriction k l E L ι).obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k)))) ≅
      ∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))))
  sheafBasis_inverse : ∀ U x,
    sheafBasis.inv.val.app U x = ∑ i,
      (pointFiniteFreeRingMap k l E L ι).hom.app U
        ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
          SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))) i).val.app U x) *
        integralScalarConstant l L (Spec (.of k)) U (basis i)
  coordinates : ∀ F : integralTowerModules l E (Spec (.of k)),
    (pointFiniteFreeRestriction k l E L ι).obj
        ((completedOrdinaryScalarExtension l E L ι (Spec (.of k))).obj F) ≅
      ∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F)
  coordinates_tensor : ∀ (F : integralTowerModules l E (Spec (.of k))) U a n i,
    (Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app U
      ((coordinates F).hom.val.app U
        (completedScalarTensorSection l E L ι (Spec (.of k)) F U a n)) =
      ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))) i).val.app U
            (sheafBasis.hom.val.app U a)) • n
  coordinates_inverse : ∀ (F : integralTowerModules l E (Spec (.of k))) U x,
    (coordinates F).inv.val.app U x = ∑ i,
      completedScalarTensorSection l E L ι (Spec (.of k)) F U
        (integralScalarConstant l L (Spec (.of k)) U (basis i))
        ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app U x)
  comparison :
    pointFiniteFreeEvaluation k l E coefficientE ⋙ pointFiniteFreeModuleTensor.{t, u} l E L ι ≅
      completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
        pointFiniteFreeEvaluation k l L coefficientL
  comparison_tensor : ∀ (F : integralTowerModules l E (Spec (.of k))) a n,
    comparison.hom.app F
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E, integralScalarIntegerInclusion l E L ι] n) =
      completedScalarTensorSection l E L ι (Spec (.of k)) F (pointFiniteFreeFinal k)
        (coefficientL a) n
  comparison_coordinates : ∀ (F : integralTowerModules l E (Spec (.of k)))
    (n : Fin (completedScalarRelativeDegree l E L ι) →
      (pointFiniteFreeEvaluation k l E coefficientE).obj F) i,
    (Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app
        (pointFiniteFreeFinal k)
      ((coordinates F).hom.val.app (pointFiniteFreeFinal k)
        (comparison.hom.app F (∑ j,
          basis j ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion l E L ι] n j))) = n i
  comparison_inverse : ∀ (F : integralTowerModules l E (Spec (.of k))) x,
    comparison.inv.app F x = ∑ i,
      basis i ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        integralScalarIntegerInclusion l E L ι]
        (@id ((pointFiniteFreeEvaluation k l E coefficientE).obj F)
          ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app
            (pointFiniteFreeFinal k)
              ((coordinates F).hom.val.app (pointFiniteFreeFinal k) x)))
  comparison_unique : ∀ (F : integralTowerModules l E (Spec (.of k)))
    (f : ((pointFiniteFreeEvaluation k l E coefficientE ⋙
      pointFiniteFreeModuleTensor.{t, u} l E L ι).obj F) ⟶
      ((completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
        pointFiniteFreeEvaluation k l L coefficientL).obj F)),
    (∀ a n, f (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
      integralScalarIntegerInclusion l E L ι] n) =
        completedScalarTensorSection l E L ι (Spec (.of k)) F (pointFiniteFreeFinal k)
          (coefficientL a) n) → f = comparison.hom.app F
  sheaf_additive : (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).Additive
  sheaf_limits : PreservesFiniteLimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
  sheaf_colimits : PreservesFiniteColimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
  module_additive : (pointFiniteFreeModuleTensor.{t, u} l E L ι).Additive
  module_limits : PreservesFiniteLimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)
  module_colimits : PreservesFiniteColimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)
  restriction_detects_exactness : ∀ S : ShortComplex (integralTowerModules l L (Spec (.of k))),
    S.Exact ↔ (S.map (pointFiniteFreeRestriction k l E L ι)).Exact
  complexes :
    (pointFiniteFreeEvaluation k l E coefficientE ⋙
      pointFiniteFreeModuleTensor.{t, u} l E L ι).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
      pointFiniteFreeEvaluation k l L coefficientL).mapHomologicalComplex (ComplexShape.up ℤ)
  complexes_hom : ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) j,
    (complexes.hom.app K).f j = comparison.hom.app (K.X j)
  complexes_inv : ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) j,
    (complexes.inv.app K).f j = comparison.inv.app (K.X j)
```

## New (delivery's version, NOT landed: replaced by the original structure above plus the additions listed in Reason)

```lean
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max a w}]
  [HasSheafify J AddCommGrpCat.{max a w}]

/-- Evaluation followed by transport across a coefficient ring equivalence.
Source: Stacks 03EK (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeCoreEvaluation (R : Sheaf J CommRingCat.{w}) (one : Cᵒᵖ)
    {A : Type a} [CommRing A] (e : A ≃+* R.obj.obj one) :=
  SheafOfModules.evaluation.{max a w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) one ⋙
      ModuleCat.restrictScalars e.toRingHom

variable (A B : Type a) [CommRing A] [CommRing B]
  (R S : Sheaf J CommRingCat.{w}) (one : Cᵒᵖ)
  (f : A →+* B) (φ : R ⟶ S) (d : ℕ)

set_option hygiene false in
local notation "rR" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option hygiene false in
local notation "rS" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
set_option hygiene false in
local notation "ringMap" => (sheafCompose J (forget₂ CommRingCat RingCat)).map φ

variable (O : SheafOfModules.{max a w} rR ⥤ SheafOfModules.{max a w} rS) [O.Additive]
  (τ : ∀ (F : SheafOfModules.{max a w} rR) (U : Cᵒᵖ),
    S.obj.obj U → F.val.obj U → (O.obj F).val.obj U)
  (cE : ∀ U : Cᵒᵖ, A → R.obj.obj U) (cL : ∀ U : Cᵒᵖ, B → S.obj.obj U)
  (qE : (A ≃+* R.obj.obj one) → Prop) (qL : (B ≃+* S.obj.obj one) → Prop)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The explicit finite-basis sections comparison over abstract coefficient data.
Every field is a clause of the point comparison; using parameters keeps its public
projections independent of the representation of completed coefficient rings.
Source: Stacks 03EK (blueprint: lem-weil-point-finite-free-sections-tensor). -/
structure PointFiniteFreeSectionsTensorCore where
  coefficientE : A ≃+* R.obj.obj one
  coefficientL : B ≃+* S.obj.obj one
  constantE : ∀ a, coefficientE a = cE one a
  constantL : ∀ a, coefficientL a = cL one a
  quotientE : qE coefficientE
  quotientL : qL coefficientL
  coefficient_compatibility : ∀ a,
    φ.hom.app one
      (coefficientE a) = coefficientL (f a)
  basis : Fin d → B
  integral_basis : Function.Bijective
    (fun a : Fin d →
        A ↦
      ∑ i, f (a i) * basis i)
  sheafBasis :
    (SheafOfModules.restrictScalars ringMap).obj
        (SheafOfModules.unit rS) ≅
      ∏ᶜ (fun _ : Fin d ↦
        SheafOfModules.unit rR)
  sheafBasis_inverse : ∀ U x,
    sheafBasis.inv.val.app U x = ∑ i,
      φ.hom.app U
        ((Pi.π (fun _ : Fin d ↦
          SheafOfModules.unit
            rR) i).val.app U x) *
        cL U (basis i)
  coordinates : ∀ F : SheafOfModules.{max a w} rR,
    (SheafOfModules.restrictScalars ringMap).obj
        (O.obj F) ≅
      ∏ᶜ (fun _ : Fin d ↦ F)
  coordinates_tensor : ∀ (F : SheafOfModules.{max a w} rR) U a n i,
    (Pi.π (fun _ : Fin d ↦ F) i).val.app U
      ((coordinates F).hom.val.app U
        (τ F U a n)) =
      ((Pi.π (fun _ : Fin d ↦
        SheafOfModules.unit rR) i).val.app U
            (sheafBasis.hom.val.app U a)) • n
  coordinates_inverse : ∀ (F : SheafOfModules.{max a w} rR) U x,
    (coordinates F).inv.val.app U x = ∑ i,
      τ F U
        (cL U (basis i))
        ((Pi.π (fun _ : Fin d ↦ F) i).val.app U x)
  comparison :
    pointFiniteFreeCoreEvaluation R one coefficientE ⋙ ModuleCat.extendScalars.{a, a, max a w} f ≅
      O ⋙
        pointFiniteFreeCoreEvaluation S one coefficientL
  comparison_tensor : ∀ (F : SheafOfModules.{max a w} rR) a n,
    comparison.hom.app F
      (a ⊗ₜ[A,f] n) =
      τ F one
        (coefficientL a) n
  comparison_coordinates : ∀ (F : SheafOfModules.{max a w} rR)
    (n : Fin d →
      (pointFiniteFreeCoreEvaluation R one coefficientE).obj F) i,
    (Pi.π (fun _ : Fin d ↦ F) i).val.app
        one
      ((coordinates F).hom.val.app one
        (comparison.hom.app F (∑ j,
          basis j ⊗ₜ[A,f] n j))) = n i
  comparison_inverse : ∀ (F : SheafOfModules.{max a w} rR) x,
    comparison.inv.app F x = ∑ i,
      basis i ⊗ₜ[A,f]
        (@id ((pointFiniteFreeCoreEvaluation R one coefficientE).obj F)
          ((Pi.π (fun _ : Fin d ↦ F) i).val.app
            one
              ((coordinates F).hom.val.app one x)))
  comparison_unique : ∀ (F : SheafOfModules.{max a w} rR)
    (g : ((pointFiniteFreeCoreEvaluation R one coefficientE ⋙
      ModuleCat.extendScalars.{a, a, max a w} f).obj F) ⟶
      ((O ⋙
        pointFiniteFreeCoreEvaluation S one coefficientL).obj F)),
    (∀ a n, g (a ⊗ₜ[A,f] n) =
        τ F one
          (coefficientL a) n) → g = comparison.hom.app F
  sheaf_additive : O.Additive
  sheaf_limits : PreservesFiniteLimits
    O
  sheaf_colimits : PreservesFiniteColimits
    O
  module_additive : (ModuleCat.extendScalars.{a, a, max a w} f).Additive
  module_limits : PreservesFiniteLimits (ModuleCat.extendScalars.{a, a, max a w} f)
  module_colimits : PreservesFiniteColimits (ModuleCat.extendScalars.{a, a, max a w} f)
  restriction_detects_exactness : ∀ K : ShortComplex (SheafOfModules.{max a w} rS),
    K.Exact ↔ (K.map (SheafOfModules.restrictScalars ringMap)).Exact
  complexes :
    (pointFiniteFreeCoreEvaluation R one coefficientE ⋙
      ModuleCat.extendScalars.{a, a, max a w} f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (O ⋙
      pointFiniteFreeCoreEvaluation S one coefficientL).mapHomologicalComplex (ComplexShape.up ℤ)
  complexes_hom : ∀ (K : CochainComplex (SheafOfModules.{max a w} rR) ℤ) j,
    (complexes.hom.app K).f j = comparison.hom.app (K.X j)
  complexes_inv : ∀ (K : CochainComplex (SheafOfModules.{max a w} rR) ℤ) j,
    (complexes.inv.app K).f j = comparison.inv.app (K.X j)



end WeilConjectures
end

@[expose] public noncomputable section
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The complete point comparison for the published completed coefficient constructions.
The core record spells out the original normalized coefficients, basis, coordinates,
canonical tensor comparison, exactness and unbounded-complex clauses verbatim.
Source: Bhatt--Scholze 4.2.12 and 6.8.2(1); Stacks 03EK
(blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev PointFiniteFreeSectionsTensorData :=
  PointFiniteFreeSectionsTensorCore.{u, max u (t + 1), t, t + 1}
    (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l L)
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))
    (completedIntegralCommRingSheafUnrestricted l L (Spec (.of k)))
    (pointFiniteFreeFinal k) (integralScalarIntegerInclusion l E L ι)
    (completedCoefficientMap l E L ι (Spec (.of k)))
    (completedScalarRelativeDegree l E L ι)
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
    (completedScalarTensorSection l E L ι (Spec (.of k)))
    (integralScalarConstant l E (Spec (.of k)))
    (integralScalarConstant l L (Spec (.of k)))
    (fun e : Padic.coefficientExtensionIntegers l E ≃+*
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))).obj.obj
          (pointFiniteFreeFinal k) ↦ ∀ n a,
      (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
        (pointFiniteFreeFinal k) (e a) =
          integralScalarFiniteConstant l E (Spec (.of k)) n (pointFiniteFreeFinal k) a)
    (fun e : Padic.coefficientExtensionIntegers l L ≃+*
        (completedIntegralCommRingSheafUnrestricted l L (Spec (.of k))).obj.obj
          (pointFiniteFreeFinal k) ↦ ∀ n a,
      (completedIntegralCommRingProjectionUnrestricted l L (Spec (.of k)) n).hom.app
        (pointFiniteFreeFinal k) (e a) =
          integralScalarFiniteConstant l L (Spec (.of k)) n (pointFiniteFreeFinal k) a)



end WeilConjectures
end

noncomputable section
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] limit
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointFiniteFreeSectionsTensor | H7 | Proof builds the core record and converts it into the unchanged structure. |
| Sheaf.Paper.PointDerivedSectionsTensorDescent | no local claim record | Unchanged; compiles against the corrected item (review 0decb: 23.4 s). |
| Sheaf.Paper.PointDerivedTensorTowerCoherence | H6 | Unchanged; compiles against the corrected item (review 0decb: 49.6 s). |
| Sheaf.Paper.PointRestrictionOrdinaryTensorSquare | no local claim record | Unchanged; compiles against the corrected item (review 0decb: 7.9 s). |
| Sheaf.Paper.CompletedModelSectionsTransport | no local claim record | Unchanged; compiles against the corrected item (review 0decb: 41.7 s). |

## Status

landed 20261024T224923-L-1831152 2026-10-24 (merge of deliver/H7/Sheaf.Paper.PointFiniteFreeSectionsTensor)
