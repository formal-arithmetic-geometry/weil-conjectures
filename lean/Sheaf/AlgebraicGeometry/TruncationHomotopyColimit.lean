/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.CategoryTheory.SequentialTelescopeMono
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-!
# Recovery of an etale complex from its upper truncations

Source: Weil conjectures blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node order 1720 (blueprint: lem-kun-hocolim-truncations); Stacks Project, Tags 0118 and 0949.

The homotopy colimit is given by a chosen telescope triangle, as in
`CategoryTheory.IsSequentialHomotopyColimit`. The conclusion asserts existence of the
comparison induced by the canonical truncation inclusions and that this comparison is an
isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- An eventually invertible sequential cocone computes the telescope cokernel. -/
@[irreducible] private noncomputable def stableTelescopeCokernel
    {A : Type*} [Category A] [Abelian A]
    (X : ℕ ⥤ A) (B : Cofan (fun n ↦ X.obj n)) (hB : IsColimit B)
    (Y : A) (b : ∀ n, X.obj n ⟶ Y)
    (hb : ∀ n, X.map (homOfLE (Nat.le_succ n)) ≫ b (n + 1) = b n)
    (N : ℕ) (hN : ∀ n, N ≤ n → IsIso (b n))
    (t : B.pt ⟶ B.pt)
    (ht : ∀ n, B.inj n ≫ t =
      B.inj n - X.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (a : B.pt ⟶ Y) (ha : ∀ n, B.inj n ≫ a = b n) (hz : t ≫ a = 0) :
    IsColimit (CokernelCofork.ofπ a hz) := by
  classical
  let L : Cocone X :=
    { pt := Y
      ι := NatTrans.ofSequence b (by simpa using hb) }
  have hL : IsColimit L := by
    have : IsIso (b N) := hN N le_rfl
    refine ⟨(fun s ↦ inv (b N) ≫ s.ι.app N), ?_, ?_⟩
    · intro s n
      change b n ≫ (inv (b N) ≫ s.ι.app N) = s.ι.app n
      by_cases hn : n ≤ N
      · have h := L.w (homOfLE hn)
        change X.map (homOfLE hn) ≫ b N = b n at h
        rw [← h, Category.assoc, IsIso.hom_inv_id_assoc]
        exact s.w (homOfLE hn)
      · have hn : N ≤ n := by omega
        have : IsIso (b n) := hN n hn
        have h := L.w (homOfLE hn)
        change X.map (homOfLE hn) ≫ b n = b N at h
        have : IsIso (X.map (homOfLE hn) ≫ b n) := by rw [h]; infer_instance
        have : IsIso (X.map (homOfLE hn)) := IsIso.of_isIso_comp_right _ (b n)
        apply (cancel_epi (X.map (homOfLE hn))).1
        rw [← Category.assoc, h, IsIso.hom_inv_id_assoc]
        exact (s.w (homOfLE hn)).symm
    · intro s m hm
      apply (cancel_epi (b N)).1
      simpa [L] using hm N
  let c (s : CokernelCofork t) : Cocone X :=
    { pt := s.pt
      ι := NatTrans.ofSequence (fun n ↦ B.inj n ≫ s.π) (by
        intro n
        have hn := congrArg (fun f ↦ B.inj n ≫ f) s.condition
        rw [← Category.assoc, ht, Preadditive.sub_comp, Category.assoc, comp_zero] at hn
        simpa using (sub_eq_zero.mp hn).symm) }
  refine CokernelCofork.IsColimit.ofπ a hz
    (fun s hs ↦ hL.desc (c (CokernelCofork.ofπ s hs))) ?_ ?_
  · intro Z s hs
    apply hB.hom_ext
    rintro ⟨n⟩
    change B.inj n ≫ (a ≫ _) = B.inj n ≫ s
    rw [← Category.assoc, ha]
    exact hL.fac (c (CokernelCofork.ofπ s hs)) n
  · intro Z s hs m hm
    apply hL.hom_ext
    intro n
    change b n ≫ m = b n ≫ hL.desc (c (CokernelCofork.ofπ s hs))
    rw [show b n ≫ hL.desc (c (CokernelCofork.ofπ s hs)) = B.inj n ≫ s from
      hL.fac (c (CokernelCofork.ofπ s hs)) n]
    rw [← ha, Category.assoc, hm]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem stableDerivedTelescope
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [HasFilteredColimitsOfSize.{0, 0} A] [AB5OfSize.{0, 0} A]
    [∀ r : ℤ, PreservesColimitsOfShape (Discrete ℕ)
      (_root_.DerivedCategory.homologyFunctor A r)]
    (X : ℕ ⥤ _root_.DerivedCategory A)
    (B : Cofan (fun n ↦ X.obj n)) (hB : IsColimit B)
    (E : _root_.DerivedCategory A) (b : ∀ n, X.obj n ⟶ E)
    (hb : ∀ n, X.map (homOfLE (Nat.le_succ n)) ≫ b (n + 1) = b n)
    (hstable : ∀ r : ℤ, ∃ N : ℕ, ∀ n, N ≤ n →
      IsIso ((_root_.DerivedCategory.homologyFunctor A r).map (b n)))
    (t : B.pt ⟶ B.pt)
    (ht : ∀ n, B.inj n ≫ t =
      B.inj n - X.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (H : _root_.DerivedCategory A) (p : B.pt ⟶ H) (q : H ⟶ B.pt⟦(1 : ℤ)⟧)
    (hT : Triangle.mk t p q ∈ distTriang (_root_.DerivedCategory A)) :
    ∃ c : H ⟶ E, (∀ n, B.inj n ≫ p ≫ c = b n) ∧ IsIso c := by
  let a : B.pt ⟶ E := Cofan.IsColimit.desc hB b
  have ha (n : ℕ) : B.inj n ≫ a = b n := Cofan.IsColimit.fac hB b n
  have hz : t ≫ a = 0 := by
    apply hB.hom_ext
    rintro ⟨n⟩
    change B.inj n ≫ (t ≫ a) = B.inj n ≫ 0
    rw [← Category.assoc, ht, Preadditive.sub_comp, Category.assoc, ha, ha, hb]
    simp
  let Δ := Triangle.mk t p q
  obtain ⟨c, hc⟩ := Triangle.yoneda_exact₂ Δ hT a hz
  change H ⟶ E at c
  have hc' : p ≫ c = a := hc.symm
  refine ⟨c, fun n ↦ ?_, ?_⟩
  · rw [hc', ha]
  · apply (_root_.DerivedCategory.isIso_iff A c).mpr
    intro r
    let F := _root_.DerivedCategory.homologyFunctor A r
    have hFB : IsColimit (Cofan.mk (F.obj B.pt) (fun n ↦ F.map (B.inj n))) :=
      Cofan.isColimitMapCoconeEquiv F _ B (isColimitOfPreserves F hB)
    have hFt (n : ℕ) : F.map (B.inj n) ≫ F.map t = F.map (B.inj n) -
        F.map (X.map (homOfLE (Nat.le_succ n))) ≫ F.map (B.inj (n + 1)) := by
      rw [← F.map_comp, ht, Functor.map_sub, Functor.map_comp]
    have hmono (i : ℤ) : Mono
        ((_root_.DerivedCategory.homologyFunctor A i).map t) := by
      let G := _root_.DerivedCategory.homologyFunctor A i
      have hGB : IsColimit (Cofan.mk (G.obj B.pt) (fun n ↦ G.map (B.inj n))) :=
        Cofan.isColimitMapCoconeEquiv G _ B (isColimitOfPreserves G hB)
      apply sequentialTelescope_mono (X ⋙ G) _ hGB (G.map t)
      intro n
      change G.map (B.inj n) ≫ G.map t = G.map (B.inj n) -
        G.map (X.map (homOfLE (Nat.le_succ n))) ≫ G.map (B.inj (n + 1))
      rw [← G.map_comp, ht, Functor.map_sub, Functor.map_comp]
    have hepi : Epi (F.map p) := by
      apply (_root_.DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
        Δ hT r (r + 1) rfl).mpr
      exact (_root_.DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        Δ hT r (r + 1) rfl).mp (hmono (r + 1))
    let S := ShortComplex.mk (F.map t) (F.map p) (by
      rw [← F.map_comp]
      exact (congrArg F.map (show t ≫ p = 0 from
        comp_distTriang_mor_zero₁₂ _ hT)).trans (F.map_zero _ _))
    have hS : S.Exact := _root_.DerivedCategory.HomologySequence.exact₂ Δ hT r
    have hcp := hS.gIsCokernel
    obtain ⟨N, hN⟩ := hstable r
    have hza : F.map t ≫ F.map a = 0 := by
      rw [← F.map_comp, hz, F.map_zero]
    let BF : Cofan (fun n ↦ (X ⋙ F).obj n) :=
      Cofan.mk (F.obj B.pt) (fun n ↦ F.map (B.inj n))
    have hca : IsColimit (CokernelCofork.ofπ (F.map a) hza) :=
      stableTelescopeCokernel (A := A) (X ⋙ F) BF hFB (F.obj E)
        (fun n ↦ F.map (b n)) (fun n ↦ by
          change F.map (X.map (homOfLE (Nat.le_succ n))) ≫ F.map (b (n + 1)) = _
          rw [← F.map_comp, hb])
        N hN (F.map t) hFt (F.map a)
        (fun n ↦ by
          change F.map (B.inj n) ≫ F.map a = _
          rw [← F.map_comp, ha]) hza
    have hmap : F.map p ≫ F.map c = F.map a :=
      (F.map_comp p c).symm.trans (congrArg F.map hc')
    let f : CokernelCofork.ofπ S.g S.zero ⟶ CokernelCofork.ofπ (F.map a) hza :=
      Cofork.mkHom (F.map c) hmap
    have : IsIso f := IsColimit.hom_isIso hcp hca f
    exact (Cocone.forget _).map_isIso f


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem homology_truncLE_inclusion_isIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (E : _root_.DerivedCategory A) (n r : ℤ) (hn : r ≤ n) :
    IsIso ((_root_.DerivedCategory.homologyFunctor A r).map
      ((_root_.DerivedCategory.TStructure.t.truncLEι n).app E)) := by
  let F := _root_.DerivedCategory.homologyFunctor A r
  let Θ := (_root_.DerivedCategory.TStructure.t.triangleLEGE n (n + 1) rfl).obj E
  have hΘ := _root_.DerivedCategory.TStructure.t.triangleLEGE_distinguished n (n + 1) rfl E
  have : Θ.obj₃.IsGE (n + 1) :=
    _root_.DerivedCategory.TStructure.t.isGE_truncGE_obj E (n + 1) (n + 1)
  have hm : Mono (F.map Θ.mor₁) := by
    apply (_root_.DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      Θ hΘ (r - 1) r (by omega)).mpr
    exact (_root_.DerivedCategory.isZero_of_isGE Θ.obj₃ (n + 1)
      (r - 1) (by omega)).eq_of_src _ _
  have he : Epi (F.map Θ.mor₁) := by
    apply (_root_.DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff Θ hΘ r).mpr
    exact (_root_.DerivedCategory.isZero_of_isGE Θ.obj₃ (n + 1)
      r (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi (F.map Θ.mor₁)

/-- Recovery from the bounded-above good truncations: the comparison from their
sequential telescope to `E`, induced by their inclusions, is an isomorphism.
The natural numbers form a cofinal sequence of upper cutoffs in the integers.
Source: blueprint sec-smooth-purity, sk-prop-sf-kunneth-ordinary, node order 1720;
Stacks Project, Tags 0118 and 0949 (blueprint: lem-kun-hocolim-truncations).

Proof:
1. The truncation inclusions form a compatible cocone. Their sum annihilates
   identity minus shift, so exactness of the given distinguished triangle produces
   a comparison from `H` to `E` with the required coprojection equations.
2. Homology preserves countable coproducts of etale module sheaves. In each degree,
   identity minus shift is monic by `sequentialTelescope_mono`; the homology exact
   sequence therefore identifies homology of `H` with its cokernel.
3. For a fixed degree `r`, the truncation inclusion induces an isomorphism on
   homology whenever `r ≤ n`, by the standard truncation triangle. Thus this cocone
   is eventually invertible and is colimiting. Its sum is another cokernel of
   identity minus shift. The homology of the comparison is the canonical map
   between these two cokernels and is an isomorphism. Homology detects
   isomorphisms in the derived category. -/
theorem isIso_truncationHomotopyColimit_comparison
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) (E : DerivedCategoryModule Λ T)
    (B : Cofan (fun n : ℕ ↦ (_root_.DerivedCategory.TStructure.t.truncLE (n : ℤ)).obj E))
    (hB : IsColimit B) (H : DerivedCategoryModule Λ T)
    (p : B.pt ⟶ H) (q : H ⟶ B.pt⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      (𝟙 B.pt - Cofan.IsColimit.desc hB (fun n : ℕ ↦
        (_root_.DerivedCategory.TStructure.t.natTransTruncLEOfLE (n : ℤ) (n + 1 : ℕ)
          (Int.ofNat_le.mpr (Nat.le_succ n))).app E ≫ B.inj (n + 1))) p q ∈
      distTriang (DerivedCategoryModule Λ T)) :
    ∃ c : H ⟶ E, (∀ n : ℕ, B.inj n ≫ p ≫ c =
      (_root_.DerivedCategory.TStructure.t.truncLEι (n : ℤ)).app E) ∧ IsIso c := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    let A := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    let X : ℕ ⥤ _root_.DerivedCategory A := Functor.ofSequence
      (X := fun n : ℕ ↦ (_root_.DerivedCategory.TStructure.t.truncLE (n : ℤ)).obj E)
      (fun n : ℕ ↦
        (_root_.DerivedCategory.TStructure.t.natTransTruncLEOfLE (n : ℤ) (n + 1 : ℕ)
          (Int.ofNat_le.mpr (Nat.le_succ n))).app E)
    let b (n : ℕ) : X.obj n ⟶ E :=
      (_root_.DerivedCategory.TStructure.t.truncLEι (n : ℤ)).app E
    have hb (n : ℕ) : X.map (homOfLE (Nat.le_succ n)) ≫ b (n + 1) = b n := by
      simp [X, b]
    change Cofan (fun n ↦ X.obj n) at B
    let t : B.pt ⟶ B.pt := 𝟙 B.pt - Cofan.IsColimit.desc hB (fun n : ℕ ↦
      X.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    have ht (n : ℕ) : B.inj n ≫ t =
        B.inj n - X.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1) := by
      simp [t, Preadditive.comp_sub]
    have hstable (r : ℤ) : ∃ N : ℕ, ∀ n, N ≤ n →
        IsIso ((_root_.DerivedCategory.homologyFunctor A r).map (b n)) := by
      exact ⟨r.toNat, fun n hn ↦ homology_truncLE_inclusion_isIso E (n : ℤ) r (by omega)⟩
    have : AB5OfSize.{0, 0} A := AB5OfSize_shrink.{0, 0, u + 1, u + 1} A
    have : HasColimitsOfSize.{u + 1, u + 1} A :=
      Sheaf.instHasColimitsOfSize
    have : HasColimitsOfSize.{0, 0} A :=
      hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} A
    have : HasColimitsOfShape (Discrete ℕ) A :=
      HasColimitsOfSize.has_colimits_of_shape _
    have : Abelian.HasKInjectiveResolutions A := inferInstance
    have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
    have : AB4OfSize.{0} A := AB4.of_AB5.{0} A
    have : HasExactColimitsOfShape (Discrete ℕ) A := AB4OfSize.ofShape ℕ
    have (r : ℤ) : PreservesColimitsOfShape (Discrete ℕ)
        (_root_.DerivedCategory.homologyFunctor A r) :=
      _root_.DerivedCategory.preservesColimitsOfShape_homologyFunctor.{u + 1, u + 2, 0, u + 1}
        (C := A) (β := ℕ) r
    exact stableDerivedTelescope X B hB E b hb hstable t ht H p q (by simpa [t, X] using hT)

end AlgebraicGeometry.Etale
