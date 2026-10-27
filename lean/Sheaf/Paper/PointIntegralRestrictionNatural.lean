/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.TraceFormula.PointTransportComposition
import all Sheaf.Paper.PointAutomorphismRestrictionNatural
import Sheaf.Paper.IntegralComparisonRealizationModels

/-! # Natural restriction on integral point sections

The restriction construction is isolated so its completed coefficient action is
checked once, before termwise passage to coefficient systems or complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PointIntegralRestrictionNatural
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

local instance powerHomIsIso (r : ℕ) : IsIso ((pointFrobeniusAut D) ^ r).hom :=
  Iso.isIso_hom _

private theorem integralConstantToCompletion_eq :
    integralConstantToCompletionOfUniverses l E (Spec (.of D.k)) =
      integralConstantToCompletion l E (Spec (.of D.k)) := by
  apply limit.hom_ext
  intro n
  simp only [integralConstantToCompletionOfUniverses, integralConstantToCompletion,
    limit.lift_π]
  rfl

private theorem restrictionArrow_eq (r : ℕ) :
    pointRestrictionArrow ((pointFrobeniusAut D) ^ r).hom = pointPowerRestriction D r := by
  apply (ProEt.forget (Spec (.of D.k))).map_injective
  simp only [pointPowerRestriction, Functor.map_preimage]
  rfl

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private theorem integralScalarRestriction (r : ℕ)
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :
    (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))).obj.map
        (pointPowerRestriction D r).op (pointIntegralSectionMap l E D.k a) =
      (inv (inverseImageCompletedCoefficientMap l E ((pointFrobeniusAut D) ^ r).hom)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (pointIntegralSectionMap l E D.k a) := by
  have h := congrArg
    ((inv (pointRestrictionCoefficientMap l E ((pointFrobeniusAut D) ^ r).hom none)).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    (scalar_normalization l E ((pointFrobeniusAut D) ^ r).hom none a)
  dsimp only [isoSectionwiseInverseImage,
    Functor.sheafPushforwardContinuous_obj_obj_obj] at h
  simpa only [← RingCat.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, IsIso.hom_inv_id,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, RingCat.id_apply,
    pointRestrictionRing, pointRestrictionCoefficientMap, pointRestrictionScalarAt,
    integralConstantToCompletion_eq, restrictionArrow_eq D r,
    pointIntegralSectionMap, pointConstantSectionMap, isoSectionwiseInverseImage,
    Functor.sheafPushforwardContinuous_obj_obj_obj, proEtaleIsoPostcompose,
    MorphismProperty.Over.map, Category.id_comp] using! h

private theorem integralSigmaTerm_smul (r : ℕ)
    (M : integralTowerModules l E (Spec (.of D.k)))
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (x : (pointIntegralSections l E D.k).obj M) :
    M.val.map (pointPowerRestriction D r).op (a • x) =
      a • (show (pointIntegralSections l E D.k).obj
        ((inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom).obj M) from
          M.val.map (pointPowerRestriction D r).op x) := by
  exact (M.val.map_smul (pointPowerRestriction D r).op (pointIntegralSectionMap l E D.k a) x).trans
    (congrArg (fun b ↦ b • M.val.map (pointPowerRestriction D r).op x)
      (integralScalarRestriction D l E r a))

attribute [local irreducible] pointIntegralSectionMap

private def integralSigmaTerm (r : ℕ)
    (M : integralTowerModules l E (Spec (.of D.k))) :
    (pointIntegralSections l E D.k).obj M ⟶
      (pointIntegralSections l E D.k).obj
        ((inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom).obj M) :=
  ModuleCat.ofHom
    (X := (pointIntegralSections l E D.k).obj M)
    (Y := (pointIntegralSections l E D.k).obj
      ((inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom).obj M))
    { toFun := fun x ↦ M.val.map (pointPowerRestriction D r).op x
      map_add' := fun x y ↦ (M.val.map (pointPowerRestriction D r).op).hom.map_add x y
      map_smul' := fun a x ↦ integralSigmaTerm_smul D l E r M a x }


/-- Restriction at a Frobenius power is a unique natural linear map on point sections.
Source: blueprint prerequisite steps 1--3 and point-automorphism scalar normalization.
(blueprint: lem-trf-point-integral-restriction-natural)
Proof: the two constant-to-completion coefficient maps agree after every quotient
projection, hence agree by the limit universal property. The coefficient square
then makes ordinary section restriction linear for the transported completed action.
Naturality of a module morphism gives naturality of these restrictions. The formula
on every section determines every component, so module and natural-transformation
extensionality give uniqueness. This includes the zeroth power and the zero module. -/
theorem existsUnique (r : ℕ) :
    ∃! sigma : pointIntegralSections l E D.k ⟶
        inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom ⋙
          pointIntegralSections l E D.k,
      ∀ (M : integralTowerModules l E (Spec (.of D.k)))
        (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        sigma.app M x = M.val.map (pointPowerRestriction D r).op x := by
  let sigma : pointIntegralSections l E D.k ⟶
      inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom ⋙
        pointIntegralSections l E D.k :=
    { app M := integralSigmaTerm D l E r M
      naturality := by
        intro M N f
        ext x
        exact (PresheafOfModules.naturality_apply f.val
          (pointPowerRestriction D r).op x).symm }
  refine ⟨sigma, fun _ _ ↦ rfl, ?_⟩
  intro sigma' h
  apply NatTrans.ext
  funext M
  ext x
  exact h M x

private def sigmaTower (r : ℕ) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointIntegralSections l E D.k) ⟶
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom) ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointIntegralSections l E D.k) := by
  let sigma := (existsUnique D l E r).exists.choose
  exact
    { app M :=
        { app n := sigma.app (M.obj n)
          naturality := by
            intro n m f
            exact sigma.naturality (M.map f) }
      naturality := by
        intro M N f
        apply NatTrans.ext
        funext n
        exact sigma.naturality (f.app n) }

private theorem sigmaTower_app (r : ℕ)
    (M : ℕᵒᵖ ⥤ integralTowerModules l E (Spec (.of D.k))) (n : ℕᵒᵖ)
    (x : (M.obj n).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    (((sigmaTower D l E r).app M).app n) x =
      (M.obj n).val.map (pointPowerRestriction D r).op x :=
  (existsUnique D l E r).exists.choose_spec (M.obj n) x

private theorem cast_map {A A' B B' : Type (u + 1)} (hA : A = A') (hB : B = B')
    (f : A → B) (g : A' → B') (h : HEq f g) (x : A') :
    f (cast hA.symm x) = cast hB.symm (g x) := by
  cases hA
  cases hB
  exact congrFun (eq_of_heq h) x

private theorem restriction_cast (M : coefficientSequenceModules l E (Spec (.of D.k))) (n : ℕ)
      {U V : (Spec (.of D.k)).ProEt} (f : U ⟶ V)
      (x : M.val.obj (op (n, V))) :
      (((coefficientSequenceRestriction l E (Spec (.of D.k))).obj M).obj (op n)).val.map f.op
          (integralComparisonRestrictedSection l E (Spec (.of D.k)) M n (op V) x) =
        integralComparisonRestrictedSection l E (Spec (.of D.k)) M n (op U)
          (M.val.map (Prod.mkHom (𝟙 n) f).op x) := by
  have h : HEq
      (fun y ↦ ((((coefficientSequenceRestriction l E (Spec (.of D.k))).obj M).obj
        (op n)).val.map f.op).hom y)
      (fun y : M.val.obj (op (n, V)) ↦ M.val.map (Prod.mkHom (𝟙 n) f).op y) := by
    unfold coefficientSequenceRestriction
    rw [(coefficientSequenceRestriction_exists l E (Spec (.of D.k))).exists.choose_spec.1 M n]
    rfl
  exact cast_map
    (integralComparisonRestrictedSectionType l E (Spec (.of D.k)) M n (op V))
    (integralComparisonRestrictedSectionType l E (Spec (.of D.k)) M n (op U)) _ _ h x

end WeilConjectures.PointIntegralRestrictionNatural
