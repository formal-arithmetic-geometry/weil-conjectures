/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentPullbackCohomologyMaps
import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
import Sheaf.AlgebraicGeometry.QcoherentPullbackEffacingSquare
import Sheaf.AlgebraicGeometry.QcoherentEtaleCoefficientExact

/-! # Pullback naturality by simultaneous dimension shifting

Source: Stacks Project, Tags 010T, 0BDY and 03P2.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local irreducible] tensorPullback tensorPullbackObj
  moduleAbelianCohomologyLarge Sheaf.H.equiv₀
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Normalized comparisons respect pullback on the two abelian cohomology theories.
Source: Stacks Project, Tags 010T, 0BDY and 03P2.
(blueprint: lem-weil-pbc-qcoherent-normalized-pullback-naturality)

Proof: In degree zero both comparisons are the structural tensor-section unit.
The adjunction description of the two cohomology pullbacks and the structural
section composition identity give the same section on Y. For the induction,
embed F into a quasi-coherent acyclic E by the universally monic finite affine
cover embedding. Push its pullback out along psi and take cokernels, obtaining
a commuting square of short exact sequences of quasi-coherent modules. The
source boundary is surjective since E is acyclic. Write any class as the
boundary of a quotient class. Both pullback maps and both normalized comparisons
commute with the relevant boundaries. Apply the induction hypothesis to the
quotient coefficient map, then take the boundary. No acyclicity of the target
middle term and no flatness of the scheme map is needed. -/
theorem normalizedCoherentEtale_pullback_naturality (X Y : Scheme.{u})
    [CompactSpace X] [X.IsSeparated]
    (cX : ∀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source X F q ≃+ CoherentEtale.Target X F q)
    (cY : ∀ (G : SheafOfModules.{u} Y.ringCatSheaf) [G.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source Y G q ≃+ CoherentEtale.Target Y G q)
    (hcX : IsNormalizedCoherentEtaleComparison X cX)
    (hcY : IsNormalizedCoherentEtaleComparison Y cY) (g : Y ⟶ X) :
    ∀ (q : ℕ) (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
      [F.IsQuasicoherent] [G.IsQuasicoherent]
      (ψ : (tensorPullback g).obj F ⟶ G) (x : CoherentEtale.Source X F q),
      cY G q (zariskiPullbackCohomology g F G
          ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ) q x) =
        etalePullbackCohomology g F G ψ q (cX F q x) := by
  classical
  have hX : CoherentEtale.IsNormalized X
      (fun F G _ _ φ ↦ coherentEtaleMap F G φ)
      (fun F _ q ↦ (cX F q).toAddMonoidHom) := hcX
  have hY : CoherentEtale.IsNormalized Y
      (fun F G _ _ φ ↦ coherentEtaleMap F G φ)
      (fun F _ q ↦ (cY F q).toAddMonoidHom) := hcY
  intro q
  induction q with
  | zero =>
    intro F G hF hG ψ x
    apply (CoherentEtale.targetZero Y G).injective
    refine (hY.2.1 G _).trans ?_
    let s := CoherentEtale.sourceZero X F x
    have hu := congrArg (fun f ↦ f s) (tensorSectionsUnit_adjoint_app g F G ψ)
    change ψ.app ⊤ (tensorSectionsUnit g F s) = _ at hu
    have hx : cX F 0 x = (CoherentEtale.targetZero X F).symm
        (ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F s)) := by
      apply (CoherentEtale.targetZero X F).injective
      exact (hX.2.1 F x).trans
        ((CoherentEtale.targetZero X F).apply_symm_apply _).symm
    refine (congrArg (fun t ↦ ULift.up (tensorSectionsUnit (⊤_ Y.Etale).hom G t))
      (zariskiPullbackCohomology_zero g F G _ x)).trans ?_
    refine (congrArg (fun t ↦ ULift.up (tensorSectionsUnit (⊤_ Y.Etale).hom G t))
      hu.symm).trans ?_
    exact (etalePullbackCohomology_zero g F G ψ s).symm.trans
      (congrArg (fun t ↦ CoherentEtale.targetZero Y G
        (etalePullbackCohomology g F G ψ 0 t)) hx.symm)
  | succ q ih =>
    intro F G hF hG ψ x
    obtain ⟨D⟩ := exists_pullbackEffacingSquare X Y g F G ψ
    let : D.E.IsQuasicoherent := D.qcE
    let : D.Q.IsQuasicoherent := D.qcQ
    let : D.E'.IsQuasicoherent := D.qcE'
    let : D.Q'.IsQuasicoherent := D.qcQ'
    let S := ShortComplex.mk D.i D.p D.zero
    let R := ShortComplex.mk D.i' D.p' D.zero'
    have haS := D.exact.map_of_exact (toAb X)
    have haR := D.exact'.map_of_exact (toAb Y)
    obtain ⟨hzS, heS⟩ := coherentEtaleMap_shortExact S D.exact
    obtain ⟨hzR, heR⟩ := coherentEtaleMap_shortExact R D.exact'
    have hzero : Subsingleton (CoherentEtale.Source X D.E (q + 1)) := by
      let : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace (q + 1)).obj D.E) :=
        ModuleCat.subsingleton_of_isZero (D.acyclic (q + 1) (by omega))
      let hM : Subsingleton (coherentModuleGroup X D.E (q + 1)) := by
        change Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace (q + 1)).obj D.E)
        infer_instance
      exact (moduleAbelianCohomologyLarge X D.E (q + 1)).symm.injective.subsingleton
    let adj := Classical.choose (exists_tensorPullbackAdjunction g)
    let φ₁ := adj.homEquiv F G ψ
    let φ₂ := adj.homEquiv D.E D.E' D.middle
    let φ₃ := adj.homEquiv D.Q D.Q' D.last
    have h₁ : S.f ≫ φ₂ = φ₁ ≫ (pushforward g).map R.f := by
      exact adj.homEquiv_naturality_left_square D.i D.middle ψ D.i' D.first_comm
    have h₂ : S.g ≫ φ₃ = φ₂ ≫ (pushforward g).map R.g := by
      exact adj.homEquiv_naturality_left_square D.p D.last D.middle D.p' D.second_comm
    obtain ⟨y, hy⟩ := CoherentEtale.source_surjective S haS q hzero x
    rw [← hy]
    calc
      _ = cY G (q + 1) (CoherentEtale.sourceBoundary R haR q
          (zariskiPullbackCohomology g D.Q D.Q' φ₃ q y)) := by
        apply congrArg (cY G (q + 1))
        exact
          zariskiPullbackCohomology_boundary g S R haS haR φ₁ φ₂ φ₃ h₁ h₂ q y
      _ = CoherentEtale.targetBoundary
          (fun F G _ _ φ ↦ coherentEtaleMap F G φ) R hzR heR q
          (cY D.Q' q (zariskiPullbackCohomology g D.Q D.Q' φ₃ q y)) :=
        hY.2.2 R D.exact' hzR haR heR q _
      _ = CoherentEtale.targetBoundary
          (fun F G _ _ φ ↦ coherentEtaleMap F G φ) R hzR heR q
          (etalePullbackCohomology g D.Q D.Q' D.last q (cX D.Q q y)) := by
        rw [ih D.Q D.Q' D.last y]
      _ = etalePullbackCohomology g F G ψ (q + 1)
          (CoherentEtale.targetBoundary
            (fun F G _ _ φ ↦ coherentEtaleMap F G φ) S hzS heS q (cX D.Q q y)) := by
        exact
          (etalePullbackCohomology_boundary g S R hzS hzR heS heR ψ D.middle D.last
            D.first_comm D.second_comm q (cX D.Q q y)).symm
      _ = _ := by
        apply congrArg (etalePullbackCohomology g F G ψ (q + 1))
        exact (hX.2.2 S D.exact hzS haS heS q y).symm

end
end AlgebraicGeometry.Scheme.Modules
