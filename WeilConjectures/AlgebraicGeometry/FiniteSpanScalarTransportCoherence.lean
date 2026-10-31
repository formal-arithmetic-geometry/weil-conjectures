/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSpanModuleComparisonData
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Geometric finite-span scalar compositors

Source: Stacks Project, Modules on Sites, Tags 03D6 and 03D7.
(blueprint: lem-sf-finite-span-scalar-coherence). -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteSpanComparison

private theorem nativeCoefficient_comp (l : ℕ) [Fact l.Prime]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (weilCoefficientsForgetAb l Z).map (adicConstantSheafToLowerStar l (f ≫ g)) =
      (weilCoefficientsForgetAb l Z).map (adicConstantSheafToLowerStar l g) ≫
        (lowerStar Ab.{u + 1} g).map
          ((weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f)) ≫
        (lowerStarComp Ab.{u + 1} f g).hom.app (nativeAb l X) := by
  have h := congrArg ((weilCoefficientsForgetAb l Z).map)
    (adicConstantSheafToLowerStar_comp l f g)
  have hc : (weilCoefficientsForgetAb l Z).map
      ((lowerStarComp (WeilCoefficients.{u} l) f g).hom.app (adicConstantSheaf l X)) =
      (lowerStarComp Ab.{u + 1} f g).hom.app (nativeAb l X) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}).map
      (((lowerStarComp (WeilCoefficients.{u} l) f g).hom.app
        (adicConstantSheaf l X)).hom.app V) = _
    rw [lowerStarComp_hom_app_hom_app, lowerStarComp_hom_app_hom_app]
    rfl
  have hm : (weilCoefficientsForgetAb l Z).map
      ((lowerStar (WeilCoefficients.{u} l) g).map (adicConstantSheafToLowerStar l f)) =
      (lowerStar Ab.{u + 1} g).map
        ((weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f)) := by
    ext V x
    rfl
  simpa only [Functor.map_comp, hc, hm] using h.symm

set_option maxHeartbeats 2000000 in
-- The composite Hom equivalence expands the geometric inverse-image functors.
private theorem rho_comp (l : ℕ) [Fact l.Prime]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rho l (f ≫ g) = (upperStarComp Ab.{u + 1} f g).hom.app (nativeAb l Z) ≫
      (upperStar Ab.{u + 1} f).map (rho l g) ≫ rho l f := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  have hu := unit_conjugateEquiv
    ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f))
    (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    (upperStarComp Ab.{u + 1} f g).hom (nativeAb l Z)
  rw [conjugateEquiv_upperStarComp_hom] at hu
  erw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu]
  rw [Category.assoc, ← (lowerStarComp Ab.{u + 1} f g).hom.naturality]
  rw [← Category.assoc, ← Adjunction.homEquiv_unit, Adjunction.comp_homEquiv]
  change _ = (upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _
    ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
      ((upperStar Ab.{u + 1} f).map (rho l g) ≫ rho l f)) ≫ _
  erw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact nativeCoefficient_comp l f g

private def comparisonComposite (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (equivalence l X (d.theta X)).functor ⋙
        (direct l f (d.coefficientMap f) ⋙ direct l g (d.coefficientMap g)) ≅
      (equivalence l X (d.theta X)).functor ⋙ direct l (f ≫ g) (d.coefficientMap (f ≫ g)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d.pushComparison f).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (d.pushComparison g).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g) _ ≪≫
    d.pushComparison (f ≫ g)

private def pushCompositor (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    direct l f (d.coefficientMap f) ⋙ direct l g (d.coefficientMap g) ≅
      direct l (f ≫ g) (d.coefficientMap (f ≫ g)) :=
  ((Functor.whiskeringLeft _ _ _).obj (equivalence l X (d.theta X)).functor).preimageIso
    (comparisonComposite l f g)

private theorem pushCompositor_compatible (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : internal l X) :
    (d.pushComparison g).hom.app ((CondensedRing.lowerStar
        (Profinite.padicAlgClRingObj l) f).obj M) ≫
      (direct l g (d.coefficientMap g)).map ((d.pushComparison f).hom.app M) ≫
      (pushCompositor l f g).hom.app ((equivalence l X (d.theta X)).functor.obj M) =
    (equivalence l Z (d.theta Z)).functor.map
      ((CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g).hom.app M) ≫
      (d.pushComparison (f ≫ g)).hom.app M := by
  have h := congr_app
    (((Functor.whiskeringLeft _ _ _).obj
      (equivalence l X (d.theta X)).functor).map_preimage (comparisonComposite l f g).hom) M
  change (pushCompositor l f g).hom.app _ = _ at h
  rw [h]
  simp [comparisonComposite]

set_option maxHeartbeats 2000000 in
-- Comparing the forgotten functors expands both iterated scalar restrictions.
private theorem pushCompositor_underlying (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    (h2 : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : internal l X)
      (V : Y.ProEtᵒᵖ) (m : ((CondensedRing.lowerStar
        (Profinite.padicAlgClRingObj l) f).obj M).X.obj.obj V),
      (((d.pushComparison f).hom.app M).val.app V) m = m)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerRight (pushCompositor l f g).hom (SheafOfModules.toSheaf (ring l Z)) =
      Functor.whiskerLeft (SheafOfModules.toSheaf (ring l X))
        (lowerStarComp Ab.{u + 1} f g).hom := by
  apply ((Functor.whiskeringLeft (internal l X) (modules l X)
      (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})).obj
    (equivalence l X (d.theta X)).functor).map_injective
  ext M V m
  have h := congrArg (fun q ↦ ((q.val.app V).hom) m)
    (pushCompositor_compatible l f g M)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply, h2] at h
  change (((pushCompositor l f g).hom.app
    ((equivalence l X (d.theta X)).functor.obj M)).val.app V).hom
      ((((d.pushComparison f).hom.app M).val.app
        ((InternalModuleOperations.siteMap g).op.obj V)).hom m) = _ at h
  rw [h2] at h
  erw [h2] at h
  change _ = (((CondensedRing.lowerStarComp
    (Profinite.padicAlgClRingObj l) f g).hom.app M).hom.hom.app V).hom m at h
  rw [CondensedRing.lowerStarComp_hom_app_hom] at h
  exact h

/-- Geometric compositors for a section-normalized ordinary scalar comparison.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03D7, composition of
pullbacks and pushforwards; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-finite-span-scalar-coherence).

Proof. Forget scalars in the native coefficient composition law
`adicConstantSheafToLowerStar_comp`; the component formula for the geometric compositor
identifies the forgotten compositor with the abelian-sheaf one. Its adjunct under the abelian
inverse-image/direct-image Hom equivalence, with the unit-conjugation identity for
`upperStarComp`, is the rho composition law. Precomposition with the equivalence at X is
fully faithful, so pc is the unique isomorphism whose whiskering is the inverse push
comparisons for f and g, the internal push compositor, and the push comparison for the
composite; this gives its compatibility square. After the same precomposition, the push
comparisons are identity section maps by h2, so pc has the geometric section formula.
Define qc to be the inverse of the left-adjoint comparison associated to pc. Apply the
compositor theorem for adjunction comparisons to the compatibility square, using h1 to
identify the three ordinary mates, and cancel the inverse internal pull compositor to get
the displayed pullback composition equation. The hypothesis h0 is not used. -/
theorem finiteSpanScalarTransportCoherence (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    (h0 :
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEtᵒᵖ)
    (r : (ring l Y).obj.obj V) (x : ((InternalModuleOperations.siteMap f).obj V.unop).left),
    (((d.coefficientMap f).hom.app V r).down.1 x) =
      r.down.1 ((Limits.pullback.fst V.unop.hom f).base x)))
    (h1 :
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (adjunction l f (d.coefficientMap f)) (d.pullComparison f).inv).natTrans =
        (d.pushComparison f).hom))
    (h2 :
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : internal l X)
    (V : Y.ProEtᵒᵖ) (m : ((CondensedRing.lowerStar
      (Profinite.padicAlgClRingObj l) f).obj M).X.obj.obj V),
    (((d.pushComparison f).hom.app M).val.app V) m = m))
    : ∃ pc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        direct l f (d.coefficientMap f) ⋙ direct l g (d.coefficientMap g) ≅
          direct l (f ≫ g) (d.coefficientMap (f ≫ g)),
      ∃ qc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        inverse l (f ≫ g) (d.coefficientMap (f ≫ g)) ≅
          inverse l g (d.coefficientMap g) ⋙ inverse l f (d.coefficientMap f),
      let d' : Data.{u} l := { d with pushComposition := pc, pullComposition := qc }
      letI := d'
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    rho l (f ≫ g) = (upperStarComp Ab.{u + 1} f g).hom.app (nativeAb l Z) ≫
      (upperStar Ab.{u + 1} f).map (rho l g) ≫ rho l f) ∧
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : modules l X) (V : Z.ProEtᵒᵖ)
    (m : ((direct l g (d'.coefficientMap g)).obj
      ((direct l f (d'.coefficientMap f)).obj M)).val.obj V),
    (((d'.pushComposition f g).hom.app M).val.app V).hom m =
      (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
        ((SheafOfModules.toSheaf (ring l X)).obj M)).hom.app V).hom m) ∧
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    d'.pullComposition f g = (Adjunction.leftAdjointCompIso
      (adjunction l g (d'.coefficientMap g)) (adjunction l f (d'.coefficientMap f))
      (adjunction l (f ≫ g) (d'.coefficientMap (f ≫ g))) (d'.pushComposition f g)).symm) ∧
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : internal l Z),
    (d'.pullComparison (f ≫ g)).hom.app M ≫
      (d'.pullComposition f g).hom.app ((equivalence l Z (d'.theta Z)).functor.obj M) =
    (equivalence l X (d'.theta X)).functor.map
      ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).hom.app M) ≫
      (d'.pullComparison f).hom.app
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M) ≫
      (inverse l f (d'.coefficientMap f)).map ((d'.pullComparison g).hom.app M)) := by
  have _ := @h0
  let pc := fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
    pushCompositor l f g
  let qc := fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
    (Adjunction.leftAdjointCompIso (adjunction l g (d.coefficientMap g))
      (adjunction l f (d.coefficientMap f))
      (adjunction l (f ≫ g) (d.coefficientMap (f ≫ g))) (pc f g)).symm
  refine ⟨pc, qc, rho_comp l, ?_, ?_, ?_⟩
  · intro X Y Z f g M V m
    have h := congr_app (pushCompositor_underlying l h2 f g) M
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun q ↦ q.hom) h) V) m
  · intros
    rfl
  · intro X Y Z f g M
    have h := equivalenceAdjunctionComparison_compositor
      (equivalence l Z (d.theta Z)) (equivalence l Y (d.theta Y))
      (equivalence l X (d.theta X))
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) g)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) (f ≫ g))
      (adjunction l g (d.coefficientMap g)) (adjunction l f (d.coefficientMap f))
      (adjunction l (f ≫ g) (d.coefficientMap (f ≫ g)))
      (d.pushComparison g) (d.pushComparison f) (d.pushComparison (f ≫ g))
      (d.pullComparison g) (d.pullComparison f) (d.pullComparison (f ≫ g))
      (h1 g) (h1 f) (h1 (f ≫ g))
      (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g) (pc f g)
      (pushCompositor_compatible l f g)
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).symm
      (qc f g).symm
      (by
        change conjugateEquiv _ _ ((conjugateEquiv _ _).symm _) = _
        exact Equiv.apply_symm_apply _ _)
      (by
        change conjugateEquiv _ _ ((conjugateEquiv _ _).symm _) = _
        exact Equiv.apply_symm_apply _ _) M
    apply (cancel_epi ((equivalence l X (d.theta X)).functor.map
      ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).inv.app M))).1
    simp only [Iso.symm_hom] at h
    simp only [← Category.assoc]
    erw [h]
    simp [← Functor.map_comp, Category.assoc]


end AlgebraicGeometry.ProEtale.FiniteSpanComparison
