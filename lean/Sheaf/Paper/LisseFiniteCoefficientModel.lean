/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars
import all Sheaf.Paper.CondensedFinitePresentationMatrices
import Sheaf.Paper.CondensedLocalModelGluing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Finite coefficient models for lisse objects

Source: the finite-descent-lisse blueprint proof, steps 1--5.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma finite_affine_free_cover
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (h : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      Finite U.I₀ ∧ (∀ i, IsAffine (U.X i)) ∧
      ∀ i, Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M) := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨V, q, hfin, ho⟩ := QuasiCompactCover.exists_hom U.forgetQc
  have : Finite V.cover.I₀ := hfin
  have (i : V.cover.I₀) : QuasiCompact (V.cover.f i) := by infer_instance
  let W := Scheme.Cover.ofQuasiCompactCover V.cover
  refine ⟨W, hfin, fun i ↦ ?_, fun i ↦ ?_⟩
  · change IsAffine (Spec (V.X i))
    infer_instance
  · have hi := (free_pullback_comp_iff (q.h₀ i) (U.f (q.s₀ i)) M).mpr
      (free_pullback (q.h₀ i) (hU (q.s₀ i)))
    have hw : q.h₀ i ≫ U.f (q.s₀ i) = W.f i := q.w₀ i
    rw [hw] at hi
    exact hi

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- A lisse module over the algebraic closure admits a lisse finite-field model.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-lisse.proof.md, proof (1).
(blueprint: lem-sfb-lisse-finite-coefficient-model).

Proof in words: remove the invertible coefficient pullback from each local free
trivialization, pull along the identity, and refine to a finite affine cover. Choose the
base coefficient field and the standard free module of the required rank on each member.
Scalar extension preserves regular modules and finite biproducts, so their extensions
identify with the original local models. Apply the existing finite local-model gluing
theorem, which descends the overlap maps and glues compatible local submodules after one
finite enlargement. Its local identifications show that the result is locally finite free.
Transport along the coefficient comparison for the identity morphism. Pullback commutes
with scalar extension, so the same cover witnesses that this transported object is lisse.
Naturality of the coefficient comparison and canonical extension transitivity identify
its algebraic-closure extension with the identity pullback of the original module, hence
with the original module. Empty covers, varying ranks and zero ranks are included. -/
theorem exists_lisse_finiteCoefficient_model [CompactSpace X] [QuasiSeparatedSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (L_E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ E)),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L_E ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj L_E ≅ L) := by
  classical
  let B := upperStar Ab.{u + 1} (𝟙 X)
  let R := padicAlgClRingObj X ℓ
  let M := (B.mapMod R).obj L
  obtain ⟨U₀, hU₀⟩ := hL
  have hraw : ∀ i, Mod.IsFree ((upperStar Ab.{u + 1} (U₀.f i)).obj R)
      (((upperStar Ab.{u + 1} (U₀.f i)).mapMod R).obj L) := by
    intro i
    let φ := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) (U₀.f i)
    apply free_of_comap (inv φ)
    exact free_of_iso (hU₀ i) ((Mod.extendScalarsIsoComapInv φ).app _)
  have hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (B.obj R))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod (B.obj R)).obj M) := by
    refine ⟨U₀, fun i ↦ ?_⟩
    apply (free_pullback_comp_iff (U₀.f i) (𝟙 X) L).mp
    rw [Category.comp_id]
    exact hraw i
  obtain ⟨U, hfinite, haffine, hU⟩ := finite_affine_free_cover (B.obj R) M hM
  choose n en using hU
  let E := Padic.finiteCoefficientBase ℓ (PadicAlgCl ℓ)
  let N i := Mod.finiteFree ((upperStar Ab.{u + 1} (U.f i)).obj
    (B.obj (padicSubfieldRingObj X ℓ E))) (n i)
  have hN : ∀ i, Mod.IsFinitelyPresented _ (N i) :=
    fun i ↦ fp_of_free ⟨n i, ⟨Iso.refl _⟩⟩
  have eN (i : U.I₀) : Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        (B.map (padicSubfieldRingObjToPadicAlgCl X ℓ E)))).obj (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod (B.obj R)).obj M) := by
    obtain ⟨ei⟩ := en i
    exact ⟨extended_free_iso _ _ _ (n i) ≪≫ ei.symm⟩
  obtain ⟨F, hEF, P, eP, ⟨eM⟩⟩ := exists_finiteCoefficient_gluing_of_local_models
    X X (𝟙 X) ℓ M E U hfinite haffine N hN eN
  let r := condensedPullbackHom (Profinite.continuousMapRingObj F) (𝟙 X)
  let s := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) (𝟙 X)
  let a := padicSubfieldRingObjToPadicAlgCl X ℓ F
  let Q := (Mod.extendScalars r).obj P
  have hP : ∀ i, Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj
      (B.obj (padicSubfieldRingObj X ℓ F)))
      (((upperStar Ab.{u + 1} (U.f i)).mapMod _).obj P) := by
    intro i
    obtain ⟨ei⟩ := eP i
    apply free_of_iso _ ei.symm
    exact free_map (Mod.extendScalars _) (Mod.regularExtensionIso _)
      ⟨n i, ⟨Iso.refl _⟩⟩
  have hQ : IsLisseCoefficientModule (Profinite.continuousMapRingObj F) Q := by
    refine ⟨U, fun i ↦ ?_⟩
    let G := upperStar Ab.{u + 1} (U.f i)
    have hi := free_map (Mod.extendScalars (G.map r)) (Mod.regularExtensionIso _) (hP i)
    have hi' := free_of_iso hi
      ((pullbackExtendScalarsIso (U.f i) _ _ r).app P).symm
    exact free_map (Mod.extendScalars
      (condensedPullbackHom (Profinite.continuousMapRingObj F) (U.f i)))
      (Mod.regularExtensionIso _) hi'
  refine ⟨F, Q, hQ, ⟨?_⟩⟩
  have hsquare : r ≫ a = B.map a ≫ s :=
    (map_coefficientMap_comp_condensedPullbackHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) (𝟙 X)).symm
  exact (Mod.extendScalarsComp r a).symm.app P ≪≫
    (Mod.extendScalarsIsoOfEq hsquare).app P ≪≫
    (Mod.extendScalarsComp (B.map a) s).app P ≪≫
    (Mod.extendScalars s).mapIso eM ≪≫
    (CondensedRing.upperStarId (Profinite.padicAlgClRingObj ℓ) X).app L

end AlgebraicGeometry.ProEtale
