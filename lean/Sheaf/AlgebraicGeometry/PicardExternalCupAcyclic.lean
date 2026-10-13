/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.Algebra.Homology.TensorKunnethNat
import Sheaf.AlgebraicGeometry.PicardExternalCupZeroTensor
import Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic

/-! # Acyclic base case for external cup

Source: Stacks Project, Varieties, Tag 0BED, proof of lemma-kunneth.
(blueprint: lem-sc-picard-external-cup-acyclic).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem modelHomology_subsingleton
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (p : ℕ)
    (h : IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)) :
    Subsingleton ((picardScalarModel f F).homology (p : ℤ)) := by
  let : Subsingleton (scalarCohomology f F p) := by
    change Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    exact ModuleCat.isZero_iff_subsingleton.mp h
  exact (picardScalarModelEquiv f F p).injective.subsingleton

/-- The normalized external cup comparison is invertible when both coefficients are acyclic.
Source: Stacks Project, Varieties, Tag 0BED, acyclic base case after
`equation-kunneth-on-cech` (blueprint: lem-sc-picard-external-cup-acyclic).

Proof: Choose finite affine covers of X and Y. Affine diagonal makes their finite
intersections affine, as well as the intersections in the product cover. The affine
pullback and tensor section formulas identify the Cech complex on X times an affine
open V of Y with Cech(X,F) tensor G(V). Exactness of tensor over k and affine Cech
comparison show that its positive cohomology vanishes and its degree-zero cohomology
is Gamma(X,F) tensor G(V). The higher-direct-image presheaf description on the affine
basis gives R^q pr2_* externalCupCoefficients = 0 for q>0, and identifies pr2_* with
Gamma(X,F) tensor G, naturally in the affine opens. Choose a basis of Gamma(X,F);
this identifies that sheaf with a direct sum of copies of G. Affine diagonal implies
quasi-separatedness, so direct-sum cohomology on qcqs Y makes it acyclic. Leray gives
zero positive product cohomology and Gamma(X,F) tensor Gamma(Y,G) in degree zero.
The section comparison sends s tensor t to the tensor of their projection pullbacks;
this is the affine section tensor isomorphism, checked on each product affine open.
The natural-degree tensor Kunneth theorem and picardScalarModelEquiv identify the
source homology with the same degree-zero tensor, and with zero in positive degrees.
Lift degree-zero homology elements through the surjective homology projections.
Its tensor-cycle formula and hc identify the degree-zero homology map of c with
that section comparison. Linearity extends equality from pure tensors. Thus it is
invertible in degree zero and between zero objects in positive degrees. No dimension
or nonemptiness hypothesis is needed: zero coefficients and empty schemes give zero
section tensors and zero homology. -/
theorem picardExternalCupCochain_isIso_of_acyclic
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F))
    (hG : ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G))
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCupCochain f g F G c) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap c (n : ℤ)) :=
  open scoped TensorProduct in
  by
    classical
    let A := picardScalarModel f F
    let B := picardScalarModel g G
    let C := picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
    obtain ⟨e, he⟩ := HomologicalComplex.tensor_kunneth_nat A B
      (picardScalarModel_negative f F) (picardScalarModel_negative g G) n
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    by_cases hn : n = 0
    · subst n
      let I := {pq : ℕ × ℕ // pq.1 + pq.2 = 0}
      let M : I → Type w := fun i ↦ TensorProduct k
        (A.homology (i.val.1 : ℤ)) (B.homology (i.val.2 : ℤ))
      let i₀ : I := ⟨(0, 0), rfl⟩
      have hi : ∀ i : I, i = i₀ := by
        intro i
        apply Subtype.ext
        have h := i.property
        apply Prod.ext <;> change _ = 0 <;> omega
      let inc : M i₀ →ₗ[k] DirectSum I M := DirectSum.lof k I M i₀
      have hinj : Function.Injective inc := by
        intro x y h
        have h' := congrArg (fun z : DirectSum I M ↦ z i₀) h
        simpa [inc, DirectSum.lof_eq_of] using h'
      have hsurj : Function.Surjective inc := by
        intro x
        induction x using DirectSum.induction_on with
        | zero => exact ⟨0, map_zero inc⟩
        | add x y hx hy =>
          obtain ⟨x', rfl⟩ := hx
          obtain ⟨y', rfl⟩ := hy
          exact ⟨x' + y', map_add inc x' y'⟩
        | of i x =>
          obtain rfl := hi i
          exact ⟨x, rfl⟩
      let d : (TensorProduct k (A.homology 0) (B.homology 0)) ≃ₗ[k]
          (picardExternalTotal f g F G).homology 0 :=
        (LinearEquiv.ofBijective inc ⟨hinj, hsurj⟩).trans e
      obtain ⟨s, hs⟩ := picardExternalCup_zero_tensor k X Y f g F G
      let t : (TensorProduct k (A.homology 0) (B.homology 0)) ≃ₗ[k] C.homology 0 :=
        ((TensorProduct.congr (picardScalarModelEquiv f F 0)
          (picardScalarModelEquiv g G 0)).trans s).trans
            (picardScalarModelEquiv (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G) 0).symm
      have hmap : (HomologicalComplex.homologyMap c 0).hom.comp d.toLinearMap =
          t.toLinearMap := by
        apply TensorProduct.ext'
        intro a b
        obtain ⟨a', ha'⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ 0)).mp inferInstance a
        obtain ⟨b', hb'⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ 0)).mp inferInstance b
        obtain ⟨z, hz, hez⟩ := he i₀ a' b'
        apply (picardScalarModelEquiv (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) 0).injective
        change picardScalarModelEquiv _ _ 0
          (HomologicalComplex.homologyMap c 0 (d (a ⊗ₜ[k] b))) =
            picardScalarModelEquiv _ _ 0 (t (a ⊗ₜ[k] b))
        dsimp only [t, LinearEquiv.trans_apply]
        erw [LinearEquiv.apply_symm_apply, TensorProduct.congr_tmul]
        change picardScalarModelEquiv _ _ 0
          (HomologicalComplex.homologyMap c 0 (e (inc (a ⊗ₜ[k] b)))) = _
        rw [← ha', ← hb']
        dsimp only [inc]
        erw [hez]
        erw [hc 0 i₀ a' b' z hz]
        simpa [i₀, A, B] using (hs (picardScalarModelEquiv f F 0 (A.homologyπ 0 a'))
          (picardScalarModelEquiv g G 0 (B.homologyπ 0 b'))).symm
      have hmap' : ∀ x, HomologicalComplex.homologyMap c 0 (d x) = t x :=
        fun x ↦ LinearMap.congr_fun hmap x
      constructor
      · intro x y hxy
        obtain ⟨x', rfl⟩ := d.surjective x
        obtain ⟨y', rfl⟩ := d.surjective y
        exact congrArg d (t.injective ((hmap' x').symm.trans (hxy.trans (hmap' y'))))
      · intro y
        obtain ⟨x, rfl⟩ := t.surjective y
        exact ⟨d x, hmap' x⟩
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hsum : ∀ x : (DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun i ↦ TensorProduct k (A.homology (i.val.1 : ℤ))
            (B.homology (i.val.2 : ℤ)))), x = 0 := by
        intro x
        induction x using DirectSum.induction_on with
        | zero => rfl
        | add x y hx hy => simp [hx, hy]
        | of i x =>
          have hx : x = 0 := by
            by_cases hp : 0 < i.val.1
            · let := modelHomology_subsingleton f F i.val.1 (hF _ hp)
              exact Subsingleton.elim _ _
            · have hq : 0 < i.val.2 := by have h := i.property; omega
              let := modelHomology_subsingleton g G i.val.2 (hG _ hq)
              exact Subsingleton.elim _ _
          simp [hx]
      let : Subsingleton ((picardExternalTotal f g F G).homology (n : ℤ)) :=
        ⟨fun x y ↦ e.symm.injective ((hsum _).trans (hsum _).symm)⟩
      let := modelHomology_subsingleton (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) n
        (picardExternalCupCoefficients_acyclic k X Y f g F G hF hG n hn')
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end AlgebraicGeometry.Scheme.Modules
