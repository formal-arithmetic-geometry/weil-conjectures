/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.Paper.FiniteClopenDerivedDecomposition
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.CategoryTheory.StrictRoosModel
import all Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Canonical integral restriction on an open subscheme

Source: Stacks Project, Tags 08TC and 07KC, definition-derived-limit and lemma-products;
Bhatt--Scholze, Definitions 3.4.10 and 3.5.2; blueprint section-invariant argument
(blueprint: def-pur-clopen-integral-restriction).

The restriction below is ordinary exact restriction of completed-ring modules.
It does not complete an arbitrary unbounded complex after restricting it.

The definitions are factored out of `ClopenRoosIntegralDescent` so the augmented
reduction comparison can use them without importing its own consumer. The completed
coefficient map is fixed uniquely by its finite quotient projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
namespace PurityFiniteSetting

/-- The scheme site has its native small model.
Source: the definition of the small pro-étale site
(blueprint: def-pur-clopen-integral-restriction). -/
instance (priority := 4000) clopenIntegralSiteSmall (Y : Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{u} _

/-- Restriction of a constant ring is normalized by the constant presheaf unit.
Source: Stacks 00XZ and 03CO (blueprint: def-pur-clopen-integral-restriction). -/
def clopenConstantMap {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (A : CommRingCat.{u + 1}) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj A ⟶
      clopenRingRestriction j
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv _ _).symm
      (Functor.whiskerLeft (clopenSiteInclusion j).op
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance clopenSiteInclusionCocontinuous {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : (clopenSiteInclusion j).IsCocontinuous
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)

private theorem clopenConstantMap_eq {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{u + 1}) :
    clopenConstantMap j A =
      ((clopenSiteInclusion j).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).hom.app
          ((Functor.const X.ProEtᵒᵖ).obj A) := by
  have : (clopenSiteInclusion j).IsCocontinuous
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  apply Sheaf.hom_ext
  simp only [Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom]
  rfl

private instance clopenConstantMapIsIso {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{u + 1}) : IsIso (clopenConstantMap j A) := by
  rw [clopenConstantMap_eq]
  infer_instance

attribute [local irreducible] Scheme.ProEt.constantComparison clopenConstantMap

/-- The completed coefficient comparison is uniquely fixed by every quotient projection.
Source: Stacks 03CO, 08TC; Bhatt--Scholze 3.5.2
(blueprint: def-pur-clopen-integral-restriction).
Proof: restriction is precomposition, hence preserves sectionwise inverse limits.
The constant-sheaf unit maps are isomorphisms after localization at the open.
Their naturality in quotient reduction gives a cone; its unique limit lift is f.
The inverse limit of the inverse finite comparisons is its inverse. Jointly monic
limit projections give uniqueness, including on the empty scheme. -/
theorem clopenCompletionMap_existsUnique {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    ∃! f : completedIntegralCommRingSheafUnrestricted l E Y ⟶
        clopenRingRestriction j (completedIntegralCommRingSheafUnrestricted l E X),
      IsIso f ∧ ∀ n : ℕ,
        f ≫ ((clopenSiteInclusion j).sheafPushforwardContinuous CommRingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (completedIntegralCommRingProjectionUnrestricted l E X n) =
          completedIntegralCommRingProjectionUnrestricted l E Y n ≫
            clopenConstantMap j (CommRingCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let R := Scheme.ProEt.clopenRingRestriction.{u, u + 1} j
  let V := sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let finite (n : ℕ) := Scheme.ProEt.constantComparison.{u, u} j
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  have hn (n : ℕ) : R.map (integralCoefficientSheafTransition l E X n) ≫
      (finite n).hom = (finite (n + 1)).hom ≫ integralCoefficientSheafTransition l E Y n := by
    exact Scheme.ProEt.constantComparison_naturality j _
  let α : integralCoefficientSheafSystem l E X ⋙ R ⟶
      integralCoefficientSheafSystem l E Y :=
    NatTrans.ofOpSequence (fun n ↦ (finite n).hom) (by
      intro n
      simpa only [Functor.comp_map, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using hn n)
  have (n : ℕᵒᵖ) : IsIso (α.app n) := inferInstanceAs (IsIso (finite n.unop).hom)
  have : IsIso α := NatIso.isIso_of_isIso_app _
  have : PreservesLimitsOfShape ℕᵒᵖ R :=
    Scheme.ProEt.ringRestriction_preservesLimits.{u, u} j
  let c := preservesLimitIso R (integralCoefficientSheafSystem l E X) ≪≫
    HasLimit.isoOfNatIso (asIso α)
  have hc (n : ℕ) :
      R.map (limit.π (integralCoefficientSheafSystem l E X) (op n)) ≫ (finite n).hom =
        c.hom ≫ limit.π (integralCoefficientSheafSystem l E Y) (op n) := by
    simp [c, HasLimit.isoOfNatIso_hom_π, Category.assoc, α]
  have hprojection (n : ℕ) : V.map
      (((clopenSiteInclusion j).sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
          (completedIntegralCommRingProjectionUnrestricted l E X n)) =
        R.map (limit.π (integralCoefficientSheafSystem l E X) (op n)) := by
    rfl
  have hprojectionY (n : ℕ) :
      V.map (completedIntegralCommRingProjectionUnrestricted l E Y n) =
        limit.π (integralCoefficientSheafSystem l E Y) (op n) := by
    rfl
  let e : completedIntegralCommRingSheafUnrestricted l E Y ≅
      clopenRingRestriction j (completedIntegralCommRingSheafUnrestricted l E X) :=
    V.preimageIso c.symm
  have hfinite (n : ℕ) : V.map (clopenConstantMap j (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) = (finite n).inv := by
    rw [clopenConstantMap_eq]
    simp only [finite, Scheme.ProEt.constantComparison, Functor.mapIso_inv, Iso.symm_inv]
    rfl
  have he (n : ℕ) :
      e.hom ≫ ((clopenSiteInclusion j).sheafPushforwardContinuous CommRingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (completedIntegralCommRingProjectionUnrestricted l E X n) =
        completedIntegralCommRingProjectionUnrestricted l E Y n ≫
          clopenConstantMap j (CommRingCat.of
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
    apply V.map_injective
    simp only [Functor.map_comp, hfinite, hprojection, hprojectionY]
    simp only [e, Functor.preimageIso_hom, Functor.map_preimage, Iso.symm_hom]
    change c.inv ≫ R.map (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
      limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫ (finite n).inv
    apply (cancel_mono (finite n).hom).mp
    rw [Category.assoc, hc, Iso.inv_hom_id_assoc]
    simp
  refine ⟨e.hom, ⟨inferInstance, he⟩, ?_⟩
  intro f hf
  apply V.map_injective
  apply (isLimitOfPreserves R (limit.isLimit (integralCoefficientSheafSystem l E X))).hom_ext
  intro n
  change V.map f ≫ R.map (limit.π _ n) = V.map e.hom ≫ R.map (limit.π _ n)
  rw [← hprojection n.unop]
  rw [← V.map_comp, ← V.map_comp, hf.2 n.unop, he n.unop]

/-- The limit lift of the normalized finite coefficient comparisons.
Source: Stacks 03CO (blueprint: def-pur-clopen-integral-restriction). -/
def clopenCompletionMap {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  (clopenCompletionMap_existsUnique l E j).exists.choose

/-- Invertibility follows from the uniquely specified limit comparison.
Source: Stacks 03CO (blueprint: def-pur-clopen-integral-restriction). -/
instance clopenCompletionMapIsIso {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    IsIso (clopenCompletionMap l E j) :=
  (clopenCompletionMap_existsUnique l E j).exists.choose_spec.1

/-- Ordinary module restriction with the canonical completed coefficient transport.
Source: Stacks 04TS and 03CO (blueprint: def-pur-clopen-integral-restriction). -/
def clopenIntegralModuleRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    scalarReductionSource l E X ⥤ scalarReductionSource l E Y :=
  clopenRestriction j (completedIntegralCommRingSheafUnrestricted l E X) ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (clopenCompletionMap l E j))

section ClopenScalarEquivalence
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{u + 1}}

private def restrictionRoundTrip (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle (c : R ≅ S) (M : SheafOfModules.{u + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private def restrictionEquivalence (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

private theorem restriction_isEquivalence (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
  (restrictionEquivalence c).isEquivalence_functor

private theorem restrictionEquivalence_unit (c : R ≅ S)
    (M : SheafOfModules.{u + 1} S) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((restrictionEquivalence c).unit.app M).val.app U x = x := by
  rfl

end ClopenScalarEquivalence

/-- Restriction and the isomorphic scalar transport are additive and exact.
Source: Stacks 04TS (blueprint: def-pur-clopen-integral-restriction).
Proof: restriction is exact on the localized pro-etale site, and scalar transport
along a ring isomorphism is an additive equivalence. Compose these exact functors. -/
theorem clopenIntegralRestriction_exact {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    (clopenIntegralModuleRestriction l E j).Additive ∧
      PreservesFiniteLimits (clopenIntegralModuleRestriction l E j) ∧
      PreservesFiniteColimits (clopenIntegralModuleRestriction l E j) := by
  let c := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (asIso (clopenCompletionMap l E j))
  have : (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
    restriction_isEquivalence c
  change (clopenRestriction j (completedIntegralCommRingSheafUnrestricted l E X) ⋙
      SheafOfModules.restrictScalars c.hom).Additive ∧
    PreservesFiniteLimits (clopenRestriction j
      (completedIntegralCommRingSheafUnrestricted l E X) ⋙
        SheafOfModules.restrictScalars c.hom) ∧
    PreservesFiniteColimits (clopenRestriction j
      (completedIntegralCommRingSheafUnrestricted l E X) ⋙
        SheafOfModules.restrictScalars c.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity extracted from exactness. Source: Stacks 04TS
(blueprint: def-pur-clopen-integral-restriction). -/
instance clopenIntegralRestrictionAdditive {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : (clopenIntegralModuleRestriction l E j).Additive :=
  (clopenIntegralRestriction_exact l E j).1

/-- Left exactness extracted from exactness. Source: Stacks 04TS
(blueprint: def-pur-clopen-integral-restriction). -/
instance clopenIntegralRestrictionLimits {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (clopenIntegralModuleRestriction l E j) :=
  (clopenIntegralRestriction_exact l E j).2.1

/-- Right exactness extracted from exactness. Source: Stacks 04TS
(blueprint: def-pur-clopen-integral-restriction). -/
instance clopenIntegralRestrictionColimits {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteColimits (clopenIntegralModuleRestriction l E j) :=
  (clopenIntegralRestriction_exact l E j).2.2

/-- Unbounded ordinary restriction, descended degreewise through quasi-isomorphisms.
Source: Stacks 015F (blueprint: def-pur-clopen-integral-restriction). -/
def clopenIntegralDerivedRestriction {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] := (clopenIntegralModuleRestriction l E j).mapDerivedCategory

/-- The canonical shift comparison of exact derived restriction. Source: Stacks 015F
(blueprint: def-pur-clopen-integral-restriction). -/
instance clopenIntegralDerivedRestrictionShift {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : (clopenIntegralDerivedRestriction l E j).CommShift ℤ :=
  inferInstanceAs ((clopenIntegralModuleRestriction l E j).mapDerivedCategory.CommShift ℤ)

/-- Degreewise exact restriction on ordinary cochain complexes. Source: Stacks 015F
(blueprint: def-pur-clopen-integral-restriction). -/
abbrev clopenIntegralComplexRestriction {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :=
  (clopenIntegralModuleRestriction l E j).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restrict strict towers degreewise, including their transition maps and strict maps.
Source: Stacks 08TC (blueprint: def-pur-clopen-integral-restriction). -/
def clopenIntegralStrictRestriction {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (clopenIntegralModuleRestriction l E j)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction on the other standard encoding of strict towers of complexes.
Source: Stacks 08TC (blueprint: def-pur-clopen-integral-restriction). -/
abbrev clopenIntegralComplexTowers {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (clopenIntegralComplexRestriction l E j)

/-- The actual strict reduction tower, functorial in its input complex.
Source: Bhatt--Scholze 3.5.2 (blueprint: def-pur-clopen-integral-restriction). -/
def clopenStrictReductionFunctor (X : Scheme.{u}) :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E X n)
    (unrestrictedIntegralTransition l E X)).flip

/-- The actual derived reduction tower, functorial in all derived morphisms.
Source: Bhatt--Scholze 3.5.2 (blueprint: def-pur-clopen-integral-restriction). -/
def clopenDerivedReductionFunctor (X : Scheme.{u}) :=
  (Functor.ofOpSequence (X := fun n ↦ sfDerivedReductionRestricted l E X n)
    (sfDerivedReductionTransition l E X)).flip


end PurityFiniteSetting
end WeilConjectures
