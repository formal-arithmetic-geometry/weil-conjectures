/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusFixedPointsCount
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.UpperStarPointwise
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-!
# Tools for comparing stalks of Weil sheaves along morphisms of geometric fibers

This file collects three general facts used to compare the stalks of a Weil sheaf with those of
its pullback along a morphism `j : Ȳ ⟶ X̄` of geometric fibers intertwining Frobenius
structures, where the two geometric fibers may live over different algebraic closures.

- `AlgebraicGeometry.ProEtale.globalSectionsTransport_comm_of_upperStar_of_comp`: transports of
  global sections along structure maps commute with the transport along a morphism `θ : j^* M ⟶ N`
  compatible with them, the squares being taken over different bases `P'` and `P`.
- `FrobeniusModule.hasEigenvalue_of_iSup_range_eq_top`: an eigenvalue of the Frobenius of a
  Frobenius module spanned by the images of equivariant maps is an eigenvalue of one of the
  sources; hence such a module is pure if the sources are
  (`FrobeniusModule.IsPureOfWeight.of_iSup_range_eq_top`).
- `AlgebraicGeometry.Scheme.Hom.mem_finitePoints_of_comp_geometricGaloisFrobenius_pow`: a
  geometric point fixed by `Frᵐ` up to `σᵐ`, `m ≥ 1`, lies over a point with finite residue field
  whose degree divides `m`.
-/

@[expose] public section

universe u' u v w

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Transports of global sections along structure maps `ψ_M : g_Y^* M ⟶ M` and
`ψ_N : g_X^* N ⟶ N` commute with the transports along a morphism `θ : j^* M ⟶ N` compatible
with them, for `g_X ≫ j = j ≫ g_Y`. The squares for `ψ_M` live over `P`, those for `ψ_N` over
`P'`, and the transports along `θ` over a morphism `Θ : P' ⟶ P` commuting with the
reparametrisations. -/
lemma globalSectionsTransport_comm_of_upperStar_of_comp {X Y P P' : Scheme.{u}} (j : X ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) (hc : gX ≫ j = j ≫ gY) {M : Sheaf (Scheme.ProEt.topology Y) A}
    {N : Sheaf (Scheme.ProEt.topology X) A} (ψM : (gY)^*[A].obj M ⟶ M)
    (ψN : (gX)^*[A].obj N ⟶ N) (θ : (j)^*[A].obj M ⟶ N)
    (hθ : (upperStarComp A gX j).hom.app M ≫ (gX)^*[A].map θ ≫ ψN =
      (upperStarCongr A hc).hom.app M ≫ (upperStarComp A j gY).hom.app M ≫ (j)^*[A].map ψM ≫ θ)
    {Θ : P' ⟶ P} {t₁ t₂ : P ⟶ Y} {t₁' t₂' : P' ⟶ X} {τ : P ⟶ P} {τ' : P' ⟶ P'}
    (h₁ : Θ ≫ t₁ = t₁' ≫ j) (h₂ : Θ ≫ t₂ = t₂' ≫ j) (hY : τ ≫ t₁ = t₂ ≫ gY)
    (hX : τ' ≫ t₁' = t₂' ≫ gX) (hΘ : τ' ≫ Θ = Θ ≫ τ) :
    globalSectionsTransport A hY ψM ≫ globalSectionsTransport A h₂ θ =
      globalSectionsTransport A h₁ θ ≫ globalSectionsTransport A hX ψN := by
  have h₃ : (τ' ≫ Θ) ≫ t₁ = t₂' ≫ (gX ≫ j) := by
    rw [Category.assoc, h₁, ← Category.assoc, hX, Category.assoc]
  have h₄ : (Θ ≫ τ) ≫ t₁ = t₂' ≫ (j ≫ gY) := by
    rw [Category.assoc, hY, ← Category.assoc, h₂, Category.assoc]
  rw [globalSectionsTransport_comp A hY h₂ h₄, globalSectionsTransport_comp A h₁ hX h₃,
    globalSectionsTransport_congr A h₃ hc _ _ hθ, globalSectionsTransport_congr_left A _ hΘ]

end AlgebraicGeometry.ProEtale

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- If a Frobenius module `N` is spanned by the images of Frobenius-equivariant linear maps
`g i : M i ⟶ N`, every eigenvalue `α` of the Frobenius of `N` is an eigenvalue of the Frobenius
of some `M i`: otherwise `F - α` is bijective on every `M i`, so its image on `N` contains every
image of `g i`, hence is all of `N`, and `F - α` is injective on `N`. -/
theorem hasEigenvalue_of_iSup_range_eq_top {ι : Type*} {M : ι → FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{w, v} K} (g : ∀ i, (M i).carrier →ₗ[K] N.carrier)
    (hg : ∀ i x, g i ((M i).frobenius x) = N.frobenius (g i x))
    (hsup : ⨆ i, LinearMap.range (g i) = ⊤) {α : K} (hα : N.frobeniusEnd.HasEigenvalue α) :
    ∃ i, (M i).frobeniusEnd.HasEigenvalue α := by
  by_contra! hM
  let T : Module.End K N.carrier := N.frobeniusEnd - α • LinearMap.id
  have hTi (i : ι) (z : (M i).carrier) :
      g i ((M i).frobeniusEnd z - α • z) = T (g i z) := by
    simp [T, frobeniusEnd, hg]
  have hsurj (i : ι) : Function.Surjective ((M i).frobeniusEnd - α • LinearMap.id) := by
    refine LinearMap.injective_iff_surjective.mp fun a b hab ↦ ?_
    by_contra hne
    refine hM i (Module.End.hasEigenvalue_of_hasEigenvector (x := a - b) ?_)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, sub_ne_zero.2 hne⟩
    have h := sub_eq_zero.2 hab
    rw [← map_sub] at h
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
    exact sub_eq_zero.1 h
  have hrange : LinearMap.range T = ⊤ := by
    refine eq_top_iff.2 (hsup ▸ iSup_le fun i ↦ ?_)
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj i x
    exact ⟨g i z, (hTi i z).symm.trans (by simp)⟩
  have hTinj : Function.Injective T :=
    LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.1 hrange)
  obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
  refine hy.2 (hTinj ?_)
  simp [T, hy.1]

/-- A Frobenius module spanned by the images of Frobenius-equivariant linear maps from modules
pure of weight `w` is pure of weight `w`. -/
theorem IsPureOfWeight.of_iSup_range_eq_top {ι : Type*} {M : ι → FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{w, v} K} (g : ∀ i, (M i).carrier →ₗ[K] N.carrier)
    (hg : ∀ i x, g i ((M i).frobenius x) = N.frobenius (g i x))
    (hsup : ⨆ i, LinearMap.range (g i) = ⊤) {ι' : K →+* ℂ} {q : ℕ} {w' : ℝ}
    (h : ∀ i, (M i).IsPureOfWeight ι' q w') : N.IsPureOfWeight ι' q w' := fun α hα ↦ by
  obtain ⟨i, hi⟩ := hasEigenvalue_of_iSup_range_eq_top g hg hsup hα
  exact h i α hi

end FrobeniusModule

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A geometric point `s` of the geometric fiber with `s ≫ Frᵐ = σᵐ ≫ s`, `m ≥ 1`, lies over a
point `x` with finite residue field whose degree divides `m`: the embedding `κ(x) ↪ k̄` given by
`s` takes values in the elements fixed by the `m`-th power of the Frobenius. -/
theorem mem_finitePoints_of_comp_geometricGaloisFrobenius_pow {m : ℕ} (hm : m ≠ 0)
    {s : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber}
    (hs : s ≫ (f.geometricGaloisFrobenius ^ m).hom = (specGeometricFrobenius k ^ m).hom ≫ s) :
    (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _) ∈ X.finitePoints ∧
      f.degreeOver ((s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _)) ∣ m := by
  let := Fintype.ofFinite k
  set g := s ≫ f.geometricFiberProj
  let σm := (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m)
  let ψ : AlgebraicClosure k →+* AlgebraicClosure k := σm.symm.toRingEquiv.toRingHom
  have hψ (a : AlgebraicClosure k) : ψ a = a ^ (Nat.card k ^ m) := by
    have h := AlgEquiv.apply_symm_apply
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m) a
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h
    dsimp only at h
    change σm.symm a = _
    rw [AlgEquiv.symm_apply_eq]
    simp only [σm, FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, Nat.card_eq_fintype_card]
  have hfix : (specGeometricFrobenius k ^ m).hom ≫ g = g := by
    rw [← Category.assoc, ← hs, Category.assoc,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  let α := Spec.preimage (s ≫ f.geometricFiberToAlgebraicClosure)
  letI : Algebra k (AlgebraicClosure k) := (α.hom.comp (algebraMap k (AlgebraicClosure k))).toAlgebra
  have hmem : g ∈ f.fixedFieldPoints ψ := by
    refine ⟨?_, ?_⟩
    · have h := s ≫= f.geometricFiber_condition
      rw [← Category.assoc, ← Category.assoc,
        ← Spec.map_preimage (s ≫ f.geometricFiberToAlgebraicClosure)] at h
      refine h.trans ?_
      simp only [Scheme.specAlgebraicClosure, Over.mk_hom, ← Spec.map_comp]
      rfl
    · rw [← hfix, specGeometricFrobenius_pow_hom, ← Category.assoc, ← Spec.map_comp]
      convert hfix using 2
      · congr 1
        ext a
        exact σm.apply_symm_apply a
      · exact hfix
  have key := f.mem_finitePoints_of_mem_fixedFieldPoints hm ψ hψ hmem
  have hd : g.base default = g.base (IsLocalRing.closedPoint _) :=
    congrArg g.base (Subsingleton.elim _ _)
  rw [hd] at key
  exact key

end AlgebraicGeometry.Scheme.Hom
