/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing finite étale schemes

Let `X = A ⊔_D B` be the pushout of two open immersions `D ⟶ A` and `D ⟶ B`, i.e. a scheme
covered by two opens `A` and `B` meeting in `D`. Finite étale schemes `P_A` over `A` and `P_B`
over `B` whose restrictions to `D` are isomorphic glue to a finite étale scheme over `X`
restricting to `P_A` and `P_B`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_pullback_inl_iso`): the glued scheme is the pushout
`P_A ⊔_{P_D} P_B`, whose charts are the base changes of `P_A` and `P_B` because the squares of
the morphism of spans are cartesian, and finiteness and étaleness are local on the target.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {D A B : Scheme.{u}} (dA : D ⟶ A) (dB : D ⟶ B) [IsOpenImmersion dA]
  [IsOpenImmersion dB]

/-- The isomorphism in `FÉt(Y)` attached to a cartesian square `P ⟶ Q.obj.left` over
`f : Y ⟶ X`. -/
noncomputable def isoPullbackOfIsPullback {X Y : Scheme.{u}} (f : Y ⟶ X) (P : Y.FiniteEtale)
    (Q : X.FiniteEtale) (h : P.obj.left ⟶ Q.obj.left)
    (H : IsPullback h P.obj.hom Q.obj.hom f) : (pullback f).obj Q ≅ P :=
  ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk H.isoPullback.symm
    (by simp))

/-- **Gluing finite étale schemes** over the pushout `A ⊔_D B` of two open immersions: finite
étale schemes over `A` and over `B` with isomorphic restrictions to `D` glue to a finite étale
scheme over `A ⊔_D B` restricting to the given ones. -/
theorem exists_pullback_inl_iso (PA : A.FiniteEtale) (PB : B.FiniteEtale)
    (e : (pullback dA).obj PA ≅ (pullback dB).obj PB) :
    ∃ P : (Limits.pushout dA dB).FiniteEtale,
      Nonempty ((pullback (Limits.pushout.inl dA dB)).obj P ≅ PA) ∧
        Nonempty ((pullback (Limits.pushout.inr dA dB)).obj P ≅ PB) := by
  have : IsFinite PA.obj.hom := PA.property
  have : Etale PA.obj.hom := PA.obj.prop
  have : IsFinite PB.obj.hom := PB.property
  have : Etale PB.obj.hom := PB.obj.prop
  let f' : Limits.pullback PA.obj.hom dA ⟶ PA.obj.left := Limits.pullback.fst PA.obj.hom dA
  let γ : Limits.pullback PA.obj.hom dA ⟶ D := Limits.pullback.snd PA.obj.hom dA
  let g' : Limits.pullback PA.obj.hom dA ⟶ PB.obj.left :=
    e.hom.hom.left ≫ Limits.pullback.fst PB.obj.hom dB
  have he : e.hom.hom.left ≫ Limits.pullback.snd PB.obj.hom dB = γ := hom_left_comp e.hom
  have hf : γ ≫ dA = f' ≫ PA.obj.hom := (Limits.pullback.condition).symm
  have hg : γ ≫ dB = g' ≫ PB.obj.hom := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, he]
  have hinv : e.inv.hom.left ≫ e.hom.hom.left = 𝟙 _ :=
    congrArg (fun φ ↦ φ.hom.left) e.inv_hom_id
  have HA : IsPullback γ f' dA PA.obj.hom := (IsPullback.of_hasPullback PA.obj.hom dA).flip
  have HB : IsPullback γ g' dB PB.obj.hom := by
    have h₀ := (IsPullback.of_hasPullback PB.obj.hom dB).flip
    let eL : Limits.pullback PA.obj.hom dA ≅ Limits.pullback PB.obj.hom dB :=
      (ObjectProperty.ι _ ⋙ MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso e
    refine h₀.of_iso eL.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [← he]
      simp only [Functor.mapIso_inv, Functor.comp_map, ObjectProperty.ι_map,
        MorphismProperty.Comma.forget_map, Over.forget_map, ← Category.assoc, hinv, eL]
      exact
        (Category.id_comp (Limits.pullback.snd PB.obj.hom dB)).symm
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, g']
      simp only [Functor.mapIso_inv, Functor.comp_map, ObjectProperty.ι_map,
        MorphismProperty.Comma.forget_map, Over.forget_map, ← Category.assoc, hinv, eL]
      exact
        (Category.id_comp (Limits.pullback.fst PB.obj.hom dB)).symm
  let q := Limits.pushout.map f' g' dA dB PA.obj.hom PB.obj.hom γ hf.symm hg.symm
  have hinl := isPullback_pushout_map_inl_of_isPullback dA dB f' g' PA.obj.hom PB.obj.hom γ hf hg
    HB
  have hinr := isPullback_pushout_map_inr_of_isPullback dA dB f' g' PA.obj.hom PB.obj.hom γ hf hg
    HA
  have hP (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] (hA : P PA.obj.hom)
      (hB : P PB.obj.hom) : P q := by
    refine IsZariskiLocalAtTarget.of_openCover (IsOpenImmersion.pushoutCover dA dB) fun i ↦ ?_
    cases i with
    | left =>
      refine (P.arrow_mk_iso_iff (Arrow.isoMk hinl.flip.isoPullback (Iso.refl _) ?_)).1 hA
      exact hinl.flip.isoPullback_hom_snd
    | right =>
      refine (P.arrow_mk_iso_iff (Arrow.isoMk hinr.flip.isoPullback (Iso.refl _) ?_)).1 hB
      exact hinr.flip.isoPullback_hom_snd
  let P : (Limits.pushout dA dB).FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ q (hP @Etale inferInstance inferInstance),
      hP @IsFinite inferInstance inferInstance⟩
  exact ⟨P, ⟨isoPullbackOfIsPullback _ PA P _ hinl.flip⟩,
    ⟨isoPullbackOfIsPullback _ PB P _ hinr.flip⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale
