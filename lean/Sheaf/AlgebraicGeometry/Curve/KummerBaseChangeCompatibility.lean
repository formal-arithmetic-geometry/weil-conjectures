/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.GmPicardPullback
import Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder

/-!
# Kummer compatibility under algebraically closed base change

Source: Weil conjectures blueprint, sec-curve-estimates/sk-prop-ext-invariance,
proper-case Kummer naturality sentence and affine-case Picard-torsion paragraph
(blueprint: lem-sc-kummer-base-change-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

set_option autoImplicit false

private theorem kummer_comparison (C P : Scheme.{u}) (π : P ⟶ C) (n : ℕ) :
    ∃ φ : ((Etale.upperStar AddCommGrpCat.{u + 1} π).mapShortComplex.obj
      (C.kummerSequence n)) ⟶ P.kummerSequence n,
      φ.τ₂ = upperStarGmSheafToGmSheaf π ∧
      φ.τ₃ = upperStarGmSheafToGmSheaf π := by
  let U := Etale.upperStar AddCommGrpCat.{u + 1} π
  let c := upperStarGmSheafToGmSheaf π
  have hg : U.map (C.kummerSequence n).g ≫ c = c ≫ (P.kummerSequence n).g := by
    change U.map (n • 𝟙 C.gmSheaf) ≫ c = c ≫ (n • 𝟙 P.gmSheaf)
    simp [U]
  have hz : (U.map (C.kummerSequence n).f ≫ c) ≫ (n • 𝟙 P.gmSheaf) = 0 := by
    change (U.map (C.kummerSequence n).f ≫ c) ≫ (P.kummerSequence n).g = 0
    rw [Category.assoc, ← hg, ← Category.assoc, ← U.map_comp]
    simp
  let a := kernel.lift (n • 𝟙 P.gmSheaf) (U.map (C.kummerSequence n).f ≫ c) hz
  refine ⟨{ τ₁ := a, τ₂ := c, τ₃ := c, comm₁₂ := ?_, comm₂₃ := hg.symm }, rfl, rfl⟩
  exact kernel.lift_ι _ _ _

/-- Kummer sequences, their connecting maps, and affine Picard torsion commute with extension of
algebraically closed ground fields. The proof follows the blueprint: base change preserves the
curve hypotheses; the comparison of units is adjoint to pullback; naturality of the derived
cohomology long exact sequence gives the ladder; degree zero is pullback of units and degree one
is pullback of invertible modules; in the affine case the Jacobian quotient and the abelian-variety
estimate give the isomorphism on `n`-torsion.

Source: Weil conjectures blueprint, sec-curve-estimates/sk-prop-ext-invariance, proper-case
Kummer naturality sentence and affine-case Picard-torsion paragraph
(blueprint: lem-sc-kummer-base-change-compatibility).

Proof: use `lem-sc-base-change-curve` for the hypotheses on the base change. The comparison map
of units and its restriction to roots of unity commute with the power maps, so the induced map of
short exact Kummer sequences is a `ShortComplex.Hom`. Apply `Sheaf.H.map_δSucc` and the
functoriality of the pullback maps to obtain the long-exact-sequence ladder. The degree-zero and
Picard assertions are the recorded pullback lemmas. For an affine curve, use the compactification
and Jacobian quotient from `lem-sc-pic-affine`, clauses (c) and (d) of `thm-av-final`, and
`lem-sc-divisible-quotient-torsion`.
-/
theorem kummer_base_change_compatibility
    (k k' : Type u) [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (P : Scheme.{u}) (π : P ⟶ C) (g : P ⟶ Spec (.of k'))
    (hπ : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0) :
      ∃ (hC : (C.kummerSequence n).ShortExact)
        (hP : (P.kummerSequence n).ShortExact)
        (φ : ((Etale.upperStar AddCommGrpCat.{u + 1} π).mapShortComplex.obj
          (C.kummerSequence n)) ⟶ P.kummerSequence n),
        φ.τ₂ = upperStarGmSheafToGmSheaf π ∧
        φ.τ₃ = upperStarGmSheafToGmSheaf π ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₃ q,
          Sheaf.H.map φ.τ₁ (q + 1)
              (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) (q + 1)
                (Sheaf.H.δSucc hC q x)) =
            Sheaf.H.δSucc hP q
              (Sheaf.H.map φ.τ₃ q
                (Etale.cohomologyMap π C.gmSheaf q x))) ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₁ q,
          Sheaf.H.map φ.τ₂ q
              (Etale.cohomologyMap π (C.kummerSequence n).X₂ q
                (Sheaf.H.map (C.kummerSequence n).f q x)) =
            Sheaf.H.map (P.kummerSequence n).f q
              (Sheaf.H.map φ.τ₁ q
                (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) q x))) ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₃ q,
          Sheaf.H.map φ.τ₃ q
              (Etale.cohomologyMap π C.gmSheaf q
                (Sheaf.H.map (C.kummerSequence n).g q x)) =
            Sheaf.H.map (P.kummerSequence n).g q
              (Sheaf.H.map φ.τ₂ q
                (Etale.cohomologyMap π C.gmSheaf q x))) ∧
        (∀ L : C.Pic,
          Pic.toCohomologicalPicardGroup P (Pic.map π L) =
            Sheaf.H.map (upperStarGmSheafToGmSheaf π) 1
              (Etale.cohomologyMap π C.gmSheaf 1
                (Pic.toCohomologicalPicardGroup C L))) ∧
        (∀ a : Γ(C, ⊤)ˣ,
          Sheaf.H.equiv₀ P.gmSheaf (MorphismProperty.Over.mkIdTerminal @Etale P)
            (Sheaf.H.map (upperStarGmSheafToGmSheaf π) 0
              (Etale.cohomologyMap π C.gmSheaf 0
                ((Sheaf.H.equiv₀ C.gmSheaf
                  (MorphismProperty.Over.mkIdTerminal @Etale C)).symm
                    (ULift.up (Additive.ofMul a))))) =
            ULift.up (Additive.ofMul (Units.map π.appTop.hom.toMonoidHom a))) ∧
        (IsAffine C →
          ∃ F : {x : C.Pic // x ^ n = 1} → {x : P.Pic // x ^ n = 1},
            Function.Bijective F ∧ ∀ x, (F x).1 = Pic.map π x.1)
      := by
  have hnC : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hnP : IsUnit (n : Γ(P, ⊤)) := by
    simpa using hnC.map π.appTop.hom
  let hC := C.kummerSequence_shortExact n hnC
  let hP := P.kummerSequence_shortExact n hnP
  obtain ⟨φ, h₂, h₃⟩ := kummer_comparison C P π n
  obtain ⟨hY, δC, δY, hδC, hδY, _, _, _, _, hf, hg, hδ⟩ :=
    Etale.pullbackCohomology_longExact_ladder π (C.kummerSequence n) hC
  have hδ' (q : ℕ) (x : Sheaf.H (C.kummerSequence n).X₃ q) :
      Etale.cohomologyMap π (C.kummerSequence n).X₁ (q + 1)
          (Sheaf.H.δSucc hC q x) =
        Sheaf.H.δSucc hY q (Etale.cohomologyMap π (C.kummerSequence n).X₃ q x) := by
    simpa only [hδC, hδY, Sheaf.H.δSucc_apply] using hδ q x
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : P.Over (Spec (.of k')) := ⟨g⟩
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hcurve := (baseChange_curve (k' := k') f).1
  have : IsCurve (pullback.snd f b) := hcurve
  have hdim : topologicalKrullDim P ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hπ.isoPullback).isHomeomorph]
    exact IsCurve.krullDim_le_one (f := pullback.snd f b)
  have : IsSeparated g := IsSeparated.isStableUnderBaseChange.of_isPullback hπ inferInstance
  have : LocallyOfFiniteType g :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback hπ inferInstance
  have : QuasiCompact g := quasiCompact_isStableUnderBaseChange.of_isPullback hπ inferInstance
  have : IsCurve g := { krullDim_le_one := hdim }
  have : IsCurve (C ↘ Spec (.of k)) := inferInstanceAs (IsCurve f)
  have : IsCurve (P ↘ Spec (.of k')) := inferInstanceAs (IsCurve g)
  obtain ⟨hPic, hUnits⟩ := Scheme.picard_cohomology_pullback k k' C P π
  refine ⟨hC, hP, φ, h₂, h₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q x
    erw [hδ']
    exact Sheaf.H.map_δSucc hY hP φ q _
  · intro q x
    exact (congrArg (Sheaf.H.map φ.τ₂ q) (hf q x)).trans
      (by simpa only [Sheaf.H.map_comp_apply, Functor.mapShortComplex,
          ShortComplex.map, Scheme.kummerSequence, Scheme.rootsOfUnitySheaf] using
        congrArg (fun a => Sheaf.H.map a q
          (Etale.cohomologyMap π (C.kummerSequence n).X₁ q x)) φ.comm₁₂.symm)
  · intro q x
    exact (congrArg (Sheaf.H.map φ.τ₃ q) (hg q x)).trans
      (by simpa only [Sheaf.H.map_comp_apply, Functor.mapShortComplex,
          ShortComplex.map, Scheme.kummerSequence, Scheme.rootsOfUnitySheaf] using
        congrArg (fun a => Sheaf.H.map a q
          (Etale.cohomologyMap π C.gmSheaf q x)) φ.comm₂₃.symm)
  · intro L
    let M := (fromSkeleton C.Modules).obj L.val
    obtain ⟨hM, hMpic⟩ := hPic M
    have : ((Modules.tensorPullback π).obj M).IsInvertible := hM
    obtain ⟨adj⟩ := Modules.nonempty_tensorPullbackAdjunction π
    let e := (Adjunction.leftAdjointUniq (Modules.pullbackPushforwardAdjunction π) adj).app M
    have he : Pic.map π L = Pic.ofIsInvertible ((Modules.tensorPullback π).obj M) := by
      apply (Pic.eq_ofIsInvertible_iff _ _).2
      exact ⟨fromSkeletonToSkeletonIso _ ≪≫ e⟩
    rw [he]
    simpa only [M, Pic.ofIsInvertible_fromSkeleton] using hMpic.symm
  · exact hUnits
  · intro hAff
    let : IsAffine C := hAff
    refine ⟨fun x => ⟨Pic.map π x.1, ?_⟩, ?_, fun _ => rfl⟩
    · change (Pic.mapHom π x.1) ^ n = 1
      rw [← map_pow, x.2, map_one]
    · exact affine_picard_torsion_base_change k k' C f P π g hπ n hn

end AlgebraicGeometry
