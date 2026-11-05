/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.InjectiveAlternatingCechRowAugmentation
import WeilConjectures.Algebra.Homology.FiniteStripAugmentation

/-! # Finite-cover augmentation for complexes with injective terms

Source: Stacks Project, Tag 08C1, proof; Tags 01EP and 01FM.
(blueprint: lem-sc-injective-terms-alternating-cech-augmentation)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechDouble_isZero_column
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (p : ℤ) (hp : p < 0 ∨ (r : ℤ) ≤ p) :
    IsZero (((alternatingCechDoubleFunctor U).obj F).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  apply (show IsZero ((((alternatingCechDoubleFunctor U).obj F).X p).X n) from ?_).eq_of_src
  change IsZero (((alternatingCechModuleFunctor U).obj (F.X n)).X p)
  change IsZero (((alternatingCechComplex U
    ((alternatingCechModulePresheaf (X := X)).obj (F.X n))).extend
      ComplexShape.embeddingUpNat).X p)
  rcases hp with hp | hp
  · apply HomologicalComplex.isZero_extend_X
    intro k
    change (k : ℤ) ≠ p
    omega
  · have hnonneg : 0 ≤ p := le_trans (by omega) hp
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    apply IsZero.of_iso _ (HomologicalComplex.extendXIso _
      ComplexShape.embeddingUpNat (i := k) rfl)
    change IsZero (alternatingCechTerms U
      ((alternatingCechModulePresheaf (X := X)).obj (F.X n)) k)
    have : IsEmpty (Fin (k + 1) ↪o Fin r) := ⟨fun t ↦ by
      have ht := Fintype.card_le_of_injective t t.injective
      simp only [Fintype.card_fin] at ht
      omega⟩
    unfold alternatingCechTerms
    exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry
