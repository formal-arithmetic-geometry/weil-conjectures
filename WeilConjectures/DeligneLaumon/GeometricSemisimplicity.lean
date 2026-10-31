/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LisseFiltration
import WeilConjectures.WeilSheaf.GeometricConstituentMono

/-! # Geometric semisimplicity of simple source Weil sheaves

Source: the geometric-socle step of `sk-i-dl-general-real`.
(blueprint: lem-zl-source-geometric-semisimplicity).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

private theorem semisimple_quotient {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    [IrreducibleSpace Y] (n : ℕ) :
    ∀ (S : Fin n → AdicSheaf l Y) (_ : ∀ i, IsIrreducibleAdicLocalSystem (S i))
      (H : AdicSheaf l Y) (_ : IsAdicLisseSheaf H) (π : ⨁ S ⟶ H) [Epi π],
      ∃ (r : ℕ) (T : Fin r → AdicSheaf l Y),
        (∀ i, IsIrreducibleAdicLocalSystem (T i)) ∧ Nonempty (H ≅ ⨁ T) := by
  induction n with
  | zero =>
    intro S _ H _ π _
    exact ⟨0, S, fun i ↦ Fin.elim0 i,
      ⟨(IsZero.of_epi π (isZero_biproduct_fin_zero S)).iso
        (isZero_biproduct_fin_zero S)⟩⟩
  | succ n ih =>
    intro S hS H hH π _
    obtain ⟨e⟩ := nonempty_iso_biproduct_fin_succ S
    have hW : IsAdicLisseSheaf (⨁ fun i : Fin n ↦ S i.castSucc) :=
      IsAdicLisseSheaf.biproduct_fin n _ fun i ↦ (hS i.castSucc).1
    let π₁ := biprod.inl ≫ e.inv ≫ π
    have hH₁ : IsAdicLisseSheaf (Limits.image π₁) := hW.image hH π₁
    obtain ⟨r, T, hT, ⟨e₁⟩⟩ := ih (fun i ↦ S i.castSucc) (fun i ↦ hS _) _ hH₁
      (factorThruImage π₁)
    let ι₁ := image.ι π₁
    have hQ := (hH₁.kernel_cokernel_of_irreducibleSpace hH ι₁).2
    let c : S (Fin.last n) ⟶ cokernel ι₁ := biprod.inr ≫ e.inv ≫ π ≫ cokernel.π ι₁
    have hfac : e.inv ≫ π ≫ cokernel.π ι₁ = biprod.snd ≫ c := by
      apply biprod.hom_ext'
      · simp only [biprod.inl_snd_assoc, zero_comp]
        change π₁ ≫ cokernel.π ι₁ = 0
        rw [← image.fac_assoc π₁, cokernel.condition, comp_zero]
      · simp [c]
    have : Epi (e.inv ≫ π ≫ cokernel.π ι₁) := inferInstance
    rw [hfac] at this
    have : Epi c := epi_of_epi (biprod.snd (X := ⨁ fun i : Fin n ↦ S i.castSucc)) c
    by_cases hc : c = 0
    · have : Epi ι₁ := Abelian.epi_of_cokernel_π_eq_zero _
        ((IsZero.of_epi_eq_zero c hc).eq_of_tgt _ _)
      have : IsIso ι₁ := isIso_of_mono_of_epi ι₁
      exact ⟨r, T, hT, ⟨(asIso ι₁).symm ≪≫ e₁⟩⟩
    · have : IsIso c := by
        rcases (hS (Fin.last n)).2.2 _ (kernel.ι c) inferInstance
          ((hS (Fin.last n)).1.kernel_cokernel_of_irreducibleSpace hQ c).1 with h | h
        · have : Mono c := Preadditive.mono_of_isZero_kernel c h
          exact isIso_of_mono_of_epi c
        · exact (hc (by rw [← cancel_epi (kernel.ι c), kernel.condition, comp_zero])).elim
      let z : cokernel ι₁ ⟶ H := inv c ≫ biprod.inr ≫ e.inv ≫ π
      have hz : z ≫ cokernel.π ι₁ = 𝟙 _ := by
        simp only [z, Category.assoc]
        exact IsIso.inv_hom_id c
      let Q := ShortComplex.mk ι₁ (cokernel.π ι₁) (cokernel.condition ι₁)
      have hQ' : Q.Exact := Q.exact_of_g_is_cokernel (cokernelIsCokernel ι₁)
      let sp := ShortComplex.Splitting.ofExactOfSection Q hQ' z hz
        (inferInstance : Mono ι₁)
      let U : Fin r ⊕ Fin 1 → AdicSheaf l Y := Sum.elim T (fun _ ↦ S (Fin.last n))
      let T' : Fin (r + 1) → AdicSheaf l Y := fun i ↦ U (finSumFinEquiv.symm i)
      refine ⟨r + 1, T', ?_, ⟨sp.isoBinaryBiproduct ≪≫
        biprod.mapIso e₁ ((asIso c).symm ≪≫
          (biproductUniqueIso (fun k : Fin 1 ↦ U (Sum.inr k))).symm) ≪≫
        biprodBiproductSumIso U ≪≫
        biproduct.whiskerEquiv (f := U) (g := T') finSumFinEquiv
          (fun i ↦ eqToIso (by simp [T']))⟩⟩
      intro i
      change IsIrreducibleAdicLocalSystem (U (finSumFinEquiv.symm i))
      rcases finSumFinEquiv.symm i with a | b
      · exact hT a
      · exact hS (Fin.last n)

/-- The underlying geometric local system of an irreducible lisse Weil sheaf
is a finite direct sum of irreducible local systems.

Source: blueprint `sk-i-dl-general-real`, first step, geometric socle argument.
(blueprint: lem-zl-source-geometric-semisimplicity).

Proof: The proved source geometric-socle surjection presents the underlying sheaf
as a quotient of a finite sum of simple geometric local systems. Induct on this
number. The empty sum has only the zero quotient. For the induction step let I
be the image of all but the final summand and Q its cokernel in the given lisse
quotient H. Images and cokernels are lisse on the irreducible geometric fiber.
The final simple summand surjects onto Q. If that map is zero then Q is zero and
I is H, so use the induction hypothesis. Otherwise its kernel is zero by
simplicity, so it is an isomorphism; its inverse supplies a section Q to H.
The exact sequence splits H as I plus Q. Apply the induction hypothesis to I
and append the final simple summand. -/
theorem exists_geometric_semisimple_decomposition
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [IrreducibleSpace (X ↘ Spec (CommRingCat.of k)).geometricFiber]
    (V : WeilSheaf k l X) (hV : V.IsIrreducibleLisse) :
    ∃ (n : ℕ) (T : Fin n → AdicSheaf l (X ↘ Spec (CommRingCat.of k)).geometricFiber),
      (∀ i, IsIrreducibleAdicLocalSystem (T i)) ∧ Nonempty (V.obj.carrier ≅ ⨁ T) := by
  obtain ⟨N, S, m, hS, _, hπ⟩ := hV.exists_epi_biproduct_desc
  exact semisimple_quotient N S hS _ hV.1 (biproduct.desc m)

end AlgebraicGeometry.WeilSheaf
