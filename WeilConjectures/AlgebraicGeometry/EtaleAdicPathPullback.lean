/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
import all WeilConjectures.AlgebraicGeometry.EtaleAdicPathData

/-!
# Compatibility of normalized etale adic paths

Source: Weil II (1.1.1), (1.1.6); Stacks 0BND (2).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y z : Spec (.of Ω) ⟶ Y}
open CategoryTheory.Limits

private theorem lifted_germ_comparison (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (t : Spec (.of Ω) ⟶ Y) (U : Y.Etale) (a : (pointSmallEtale t).fiber.obj U) :
    (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber U ⟨a⟩ F.obj ≫
        (((pointSmallEtale t).uliftSheafFiberIso.{u + 1}
          (ModuleCat.{u + 1} R)).app F).hom =
      (pointSmallEtale t).toPresheafFiber U a F.obj := by
  exact Functor.Final.ι_colimitIso_hom
    (Functor.Elements.uliftEquivalence.{u + 1} (pointSmallEtale t).fiber).functor.op
    (pointedEtaleStalkDiagram F t) (op ⟨U, ⟨a⟩⟩)

private theorem lifted_automorphism_germ (h : Y ≅ Y)
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (t : Spec (.of Ω) ⟶ Y) (U : Y.Etale) (a : (pointSmallEtale t).fiber.obj U) :
    (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber U ⟨a⟩
        ((automorphismModuleSheafPullback h R).obj F).obj ≫
        (automorphismModuleLiftedStalkIso h R F t).hom =
      (pointSmallEtale (t ≫ h.hom)).ulift.{u + 1}.toPresheafFiber
        ((automorphismEtaleReindex h).obj U)
        ⟨automorphismPointedEtaleLift h t U a⟩ F.obj := by
  unfold automorphismModuleLiftedStalkIso
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, lifted_germ_comparison]
  rw [show (automorphismModuleStalkIso h R F t).hom =
    (automorphismModuleStalkIso_exists h R F t).exists.choose.hom from rfl]
  erw [(automorphismModuleStalkIso_exists h R F t).exists.choose_spec U a]
  apply (cancel_mono (((pointSmallEtale (t ≫ h.hom)).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} R)).app F).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (lifted_germ_comparison R F (t ≫ h.hom) _ _).symm

private theorem reindex_finite_endpoint (h : Y ≅ Y) (τ : fiber y ≅ fiber z)
    (P : Y.FiniteEtale) (a : (fiber y).obj P) :
    let H : Y.FiniteEtale := ⟨(automorphismEtaleReindex h).obj P.obj,
      by
        have : IsFinite P.obj.hom := P.property
        change IsFinite (P.obj.hom ≫ h.hom)
        infer_instance⟩
    (pullbackPathIso h.hom τ).hom.app H
        (automorphismPointedEtaleLift h y P.obj a) =
      automorphismPointedEtaleLift h z P.obj (τ.hom.app P a) := by
  dsimp only
  apply Over.OverMorphism.ext
  rw [pullbackPathIso_hom_app_left]
  let H : Y.FiniteEtale := ⟨(automorphismEtaleReindex h).obj P.obj, by
        have : IsFinite P.obj.hom := P.property
        change IsFinite (P.obj.hom ≫ h.hom)
        infer_instance⟩
  let k : P ⟶ (FiniteEtale.pullback h.hom).obj H := ObjectProperty.homMk
    (MorphismProperty.Over.homMk
      (Limits.pullback.lift (𝟙 P.obj.left) P.obj.hom (by
        simp only [Category.id_comp]
        rfl))
      (Limits.pullback.lift_snd _ _ _))
  have hk : (pullbackFiberIso h.hom y).inv.app H
      (automorphismPointedEtaleLift h y P.obj a) = (fiber y).map k a := by
    apply Over.OverMorphism.ext
    rw [pullbackFiberIso_inv_app_left, fiber_map_left]
    change Limits.pullback.lift a.left y _ =
      a.left ≫ Limits.pullback.lift (𝟙 P.obj.left) P.obj.hom _
    apply Limits.pullback.hom_ext <;> simp [Category.assoc, fiber_left_comp]
  rw [hk]
  have hn : τ.hom.app ((FiniteEtale.pullback h.hom).obj H) ((fiber y).map k a) =
      (fiber z).map k (τ.hom.app P a) :=
    ConcreteCategory.congr_hom (τ.hom.naturality k) a
  have hn' := congrArg (fun b ↦ b.left ≫ Limits.pullback.fst H.obj.hom h.hom) hn
  change _ = (τ.hom.app P a).left
  have hproj : k.hom.left ≫ Limits.pullback.fst H.obj.hom h.hom = 𝟙 P.obj.left :=
    Limits.pullback.lift_fst _ _ _
  have hn'' := hn'.trans (by
    rw [fiber_map_left, Category.assoc, hproj]
    )
  exact hn''

private theorem finite_path_pullback (h : Y ≅ Y)
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    (hPfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj ((automorphismModuleSheafPullback h R).obj F)))
    (τ : fiber y ≅ fiber z) :
    (etaleFinitePathIso R ((automorphismModuleSheafPullback h R).obj F)
        (automorphismModuleSheafPullback_isFiniteLocallyConstant h R F hF) hPfin τ).hom ≫
        (automorphismModuleLiftedStalkIso h R F z).hom =
      (automorphismModuleLiftedStalkIso h R F y).hom ≫
        (etaleFinitePathIso R F hF hfin (pullbackPathIso h.hom τ)).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  let G := (automorphismModuleSheafPullback h R).obj F
  have hG := automorphismModuleSheafPullback_isFiniteLocallyConstant h R F hF
  have hL := isLisseModuleSheaf_of_locallyConstant_of_finite_stalk R G
    hG.toIsLocallyConstantSheaf hPfin
  obtain ⟨P, a, s, rfl⟩ := finiteModuleGerm_surjective (y := y) R G hL x
  change (automorphismModuleLiftedStalkIso h R F z).hom
    ((etaleFinitePathIso R G hG hPfin τ).hom _) =
      (etaleFinitePathIso R F hF hfin (pullbackPathIso h.hom τ)).hom
        ((automorphismModuleLiftedStalkIso h R F y).hom _)
  rw [etaleFinitePath_germ]
  have hg (t : Spec (.of Ω) ⟶ Y) (b : (pointSmallEtale t).fiber.obj P.obj) :=
    show (automorphismModuleLiftedStalkIso h R F t).hom
        ((pointSmallEtale t).ulift.{u + 1}.toPresheafFiber P.obj ⟨b⟩ G.obj s) =
      (pointSmallEtale (t ≫ h.hom)).ulift.{u + 1}.toPresheafFiber
        ((automorphismEtaleReindex h).obj P.obj)
        ⟨automorphismPointedEtaleLift h t P.obj b⟩ F.obj s from
      ConcreteCategory.congr_hom (lifted_automorphism_germ h R F t P.obj b) s
  rw [hg z, hg y]
  let H : Y.FiniteEtale := ⟨(automorphismEtaleReindex h).obj P.obj, by
        have : IsFinite P.obj.hom := P.property
        change IsFinite (P.obj.hom ≫ h.hom)
        infer_instance⟩
  rw [etaleFinitePath_germ R F hF hfin (pullbackPathIso h.hom τ) H]
  have ha := reindex_finite_endpoint h τ P a
  change _ = (pointSmallEtale (z ≫ h.hom)).ulift.{u + 1}.toPresheafFiber
    ((automorphismEtaleReindex h).obj P.obj)
    ⟨(pullbackPathIso h.hom τ).hom.app H
      (automorphismPointedEtaleLift h y P.obj a)⟩ F.obj s
  rw [ha]

variable (l : ℕ) [Fact l.Prime]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]

private theorem integral_path_pullback (h : Y ≅ Y)
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : LisseIntegralSheaf l E Y) (τ : fiber y ≅ fiber z) :
    (etaleIntegralPathIso l E ((lisseIntegralAutomorphismPullback h l E).obj F) τ).hom ≫
        (lisseIntegralAutomorphismFiberIso h l E z F).hom =
      (lisseIntegralAutomorphismFiberIso h l E y F).hom ≫
        (etaleIntegralPathIso l E F (pullbackPathIso h.hom τ)).hom := by
  apply limit.hom_ext
  rintro ⟨n⟩
  have hp (t : Spec (.of Ω) ⟶ Y) :
      (lisseIntegralAutomorphismFiberIso h l E t F).hom ≫
        limit.π (F.obj ⋙ (pointSmallEtale (t ≫ h.hom)).ulift.{u + 1}.sheafFiber) (op n) =
      limit.π (((lisseIntegralAutomorphismPullback h l E).obj F).obj ⋙
        (pointSmallEtale t).ulift.{u + 1}.sheafFiber) (op n) ≫
        (automorphismModuleLiftedStalkIso h (Padic.coefficientExtensionIntegers l E)
          (F.obj.obj (op n)) t).hom :=
    (lisseIntegralAutomorphismFiberIso_exists h l E t F).exists.choose_spec n
  simp only [Category.assoc]
  rw [hp z, ← Category.assoc, etaleIntegralPath_projection, Category.assoc,
    etaleIntegralPath_projection]
  conv_rhs => rw [← Category.assoc, hp y, Category.assoc]
  exact congrArg (fun k ↦ limit.π _ (op n) ≫ k)
    (finite_path_pullback h (Padic.coefficientExtensionIntegers l E)
      (F.obj.obj (op n)) (F.property.1 n) (etaleIntegralLevel_finite l E F n)
      (etaleIntegralLevel_finite l E
        ((lisseIntegralAutomorphismPullback h l E).obj F) n) τ)

private theorem path_cast {A C : Type*} [Category C] (f g : A → C)
    (e : ∀ a, f a ≅ g a) {a b : A} (hab : a = b) :
    (e a).hom ≫ eqToHom (congrArg g hab) =
      eqToHom (congrArg f hab) ≫ (e b).hom := by
  subst hab
  simp

private theorem rational_path_pullback (h : Y ≅ Y)
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : LisseRationalSheaf l E Y) (τ : fiber y ≅ fiber z) :
    (etaleRationalPathIso l E ((lisseRationalAutomorphismPullback h l E).obj F) τ).hom ≫
        (lisseRationalAutomorphismFiberIso h l E z F).hom =
      (lisseRationalAutomorphismFiberIso h l E y F).hom ≫
        (etaleRationalPathIso l E F (pullbackPathIso h.hom τ)).hom := by
  unfold lisseRationalAutomorphismFiberIso
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  rw [← Category.assoc, path_cast
    (fun G ↦ lisseRationalFiber l E Y y G)
    (fun G ↦ lisseRationalFiber l E Y z G) (fun G ↦ etaleRationalPathIso l E G τ)
    (lisseRationalAutomorphismPullbackObjEq h l E F)]
  rw [Category.assoc, Category.assoc]
  apply congrArg (fun k ↦ eqToHom
    (congrArg (lisseRationalFiber l E Y y)
      (lisseRationalAutomorphismPullbackObjEq h l E F)) ≫ k)
  unfold etaleRationalPathIso
  simp only [Functor.mapIso_hom]
  erw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (integral_path_pullback l h E F.integral τ)

attribute [local irreducible] lisseRationalAutomorphismPullback
  etaleRationalPathIso etaleIntegralPathIso lisseRationalFiber lisseIntegralFiber
  automorphismLisseCoefficientTransformation

private theorem algebraic_path_stage (h : Y ≅ Y)
    (F : LisseAlgebraicSheaf l Y Q) (τ : fiber y ≅ fiber z) :
    (etaleAlgebraicPathIso l Q ((lisseAlgebraicAutomorphismPullback h l Q).obj F) τ).hom ≫
        eqToHom (lisseAlgebraicAutomorphismFiberAtStage_eq h l Q z F) =
      eqToHom (lisseAlgebraicAutomorphismFiberAtStage_eq h l Q y F) ≫
        ((ModuleCat.extendScalars (algebraMap (lisseAlgebraicPair l Y Q F).base.val Q)).mapIso
          (etaleRationalPathIso l (lisseAlgebraicPair l Y Q F).base.val
            ((lisseRationalAutomorphismPullback h l
              (lisseAlgebraicPair l Y Q F).base.val).obj
              (lisseCoefficientPairModel l Y Q (lisseAlgebraicPair l Y Q F))) τ)).hom := by
  let P := lisseAlgebraicPair l Y Q F
  let G := (lisseRationalAutomorphismPullback h l P.base.val).obj
    (lisseCoefficientPairModel l Y Q P)
  let B := lisseAlgebraicAutomorphismPullbackObj h l Q F
  let e := (lisseCoefficientDiagramData l Y Q).obj_eq P.base
  have he : (eqToHom e).toFunctor.obj ((eqToHom e.symm).toFunctor.obj G) = G := by
    exact congrArg (fun T ↦ T.toFunctor.obj G) (eqToHom_trans e.symm e)
  let S := ModuleCat.extendScalars (algebraMap P.base.val Q)
  let hz (t : Spec (.of Ω) ⟶ Y) :=
    congrArg (fun H ↦ S.obj (lisseRationalFiber l P.base.val Y t H)) he
  have hstage := path_cast
    (fun H ↦ S.obj (lisseRationalFiber l P.base.val Y y H))
    (fun H ↦ S.obj (lisseRationalFiber l P.base.val Y z H))
    (fun H ↦ S.mapIso (etaleRationalPathIso l P.base.val H τ)) he
  have hobj := path_cast (fun H ↦ lisseAlgebraicFiber l Y Q y H)
    (fun H ↦ lisseAlgebraicFiber l Y Q z H)
    (fun H ↦ etaleAlgebraicPathIso l Q H τ)
    (lisseAlgebraicAutomorphismPullback_obj h l Q F)
  calc
    _ = (etaleAlgebraicPathIso l Q
        ((lisseAlgebraicAutomorphismPullback h l Q).obj F) τ).hom ≫
        eqToHom (congrArg (lisseAlgebraicFiber l Y Q z)
          (lisseAlgebraicAutomorphismPullback_obj h l Q F)) ≫ eqToHom (hz z) := by
      rw [← eqToHom_trans]
    _ = eqToHom (congrArg (lisseAlgebraicFiber l Y Q y)
          (lisseAlgebraicAutomorphismPullback_obj h l Q F)) ≫
        (etaleAlgebraicPathIso l Q B τ).hom ≫ eqToHom (hz z) := by
      rw [← Category.assoc, hobj, Category.assoc]
    _ = eqToHom (congrArg (lisseAlgebraicFiber l Y Q y)
          (lisseAlgebraicAutomorphismPullback_obj h l Q F)) ≫
        eqToHom (hz y) ≫ (S.mapIso (etaleRationalPathIso l P.base.val G τ)).hom := by
      exact congrArg (fun k ↦ eqToHom
        (congrArg (lisseAlgebraicFiber l Y Q y)
          (lisseAlgebraicAutomorphismPullback_obj h l Q F)) ≫ k) hstage
    _ = _ := by
      dsimp only [P, G, S]
      simp only [← Category.assoc]
      congr 1
      exact eqToHom_trans _ _

/-- The specified pullback-fibre comparison commutes with every finite-fibre path.
Source: Weil II (1.1.6), Stacks 03Q1 (3), 0BND (2)
(blueprint: new-t2-etale-adic-path-pullback).
Proof: the small-etale automorphism sends a cover (U,u) to (U,h u).
Its stalk comparison carries the germ at a point a to the same section's germ
at its image. By the definition of pullbackPathIso, finite path evaluation on the
transformed cover gives exactly the transformed endpoint. The finite germ rule
therefore proves the square at every adic level. Composing with the limit
projections proves the integral square. The rational comparison is its scalar
extension, and the algebraic comparison is the further scalar extension at the
same finite coefficient field recorded by F. Both scalar extensions preserve the
square. The equality transporting the pullback object's recorded fibre to that
common stage is precisely lisseAlgebraicAutomorphismFiberAtStage_eq, so it yields
the stated equation on the recorded fibres. Identity automorphisms and zero-rank
objects give the corresponding identity and zero-map squares. -/
theorem etaleAlgebraicPath_pullback (h : Y ≅ Y)
    (F : LisseAlgebraicSheaf l Y Q) (τ : fiber y ≅ fiber z) :
    (etaleAlgebraicPathIso l Q ((lisseAlgebraicAutomorphismPullback h l Q).obj F) τ).hom ≫
        (lisseAlgebraicAutomorphismFiberIso h l Q z F).hom =
      (lisseAlgebraicAutomorphismFiberIso h l Q y F).hom ≫
        (etaleAlgebraicPathIso l Q F (pullbackPathIso h.hom τ)).hom := by
  unfold lisseAlgebraicAutomorphismFiberIso
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  rw [← Category.assoc, algebraic_path_stage, Category.assoc, Category.assoc]
  apply congrArg (fun k ↦ eqToHom
    (lisseAlgebraicAutomorphismFiberAtStage_eq h l Q y F) ≫ k)
  unfold etaleAlgebraicPathIso
  simp only [Functor.mapIso_hom]
  erw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (rational_path_pullback l h
    (lisseAlgebraicPair l Y Q F).base.val
    (lisseCoefficientPairModel l Y Q (lisseAlgebraicPair l Y Q F)) τ)

end AlgebraicGeometry.Scheme
