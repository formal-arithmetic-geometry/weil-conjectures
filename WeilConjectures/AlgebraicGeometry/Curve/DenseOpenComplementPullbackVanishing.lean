/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenFiniteComplement
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality

/-! # Vanishing for a dense-open closed complement after open restriction

Source: Stacks Project, Tag 0GJA, proof and remark (d).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- A sheaf pushed forward from the closed complement of a dense open in a curve
has no positive cohomology after restriction along an open immersion.
Source: Stacks Project, Tag 0GJA, proof and remark (d). -/
theorem dense_open_complement_pullback_vanishing (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    (U : X.Opens) (hU : Dense (U : Set X))
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : Set.range i.base = (U : Set X)ᶜ)
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a] :
    ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H (((a)^*[AddCommGrpCat.{u + 1}]).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            (((i)_*[ModuleCat.{u + 1} Λ]).obj G))) q) := by
  classical
  let V := a ⁻¹ᵁ U
  obtain ⟨hfin, hcl, hsep⟩ := dense_open_finite_complement f U hU
  have hfin' : (V : Set W)ᶜ.Finite :=
    hfin.preimage a.isOpenEmbedding.injective.injOn
  have hcl' (x : W) (hx : x ∉ V) : IsClosed ({x} : Set W) := by
    have heq : a ⁻¹' {a x} = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact a.isOpenEmbedding.injective.eq_iff
    rw [← heq]
    exact (hcl (a x) hx).preimage a.continuous
  have hsep' (x : W) (hx : x ∉ V) : IsSepClosed (W.residueField x) := by
    have := hsep (a x) hx
    exact IsSepClosed.of_ringEquiv (asIso (a.residueFieldMap x)).commRingCatIsoToRingEquiv
  let M := ((i)_*[ModuleCat.{u + 1} Λ]).obj G
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M
  have hdis : Disjoint (Set.range (V.ι ≫ a).base) (Set.range i.base) := by
    rw [hi]
    apply disjoint_compl_right.mono_left
    change Set.range (V.ι ≫ a).base ⊆ (U : Set X)
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hzM := isZero_upperStar_lowerStar_of_disjoint_range
    (ModuleCat.{u + 1} Λ) (V.ι ≫ a) i hdis G
  obtain ⟨e⟩ := exists_upperStar_forget₂_natIso Λ (V.ι ≫ a)
  have : (sheafCompose (V : Scheme.{u}).smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive :=
    { map_add := by intros; rfl }
  have hzF : CategoryTheory.Limits.IsZero
      (((V.ι ≫ a)^*[AddCommGrpCat.{u + 1}]).obj F) :=
    (Functor.map_isZero (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) hzM).of_iso (e.app M).symm
  have hz : CategoryTheory.Limits.IsZero
      ((V.ι)^*[AddCommGrpCat.{u + 1}].obj ((a)^*[AddCommGrpCat.{u + 1}].obj F)) :=
    hzF.of_iso ((upperStarComp AddCommGrpCat.{u + 1} V.ι a).app F).symm
  intro q hq
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  exact subsingleton_H_of_isZero_upperStar V hfin' hcl' hsep' _ hz n

end AlgebraicGeometry.IsCurve
