/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricProductSections
public import Sheaf.AlgebraicGeometry.SymmetricProductPolynomial
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Algebra.Polynomial.BigOperators
import Sheaf.AlgebraicGeometry.SymmetricProductSectionsNonvanishing
import Sheaf.AlgebraicGeometry.SymmetricProductSectionsPermutation
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-!
# No common zero and permutation invariance

Source: Weil conjectures blueprint, symmetric-product-properties, parts (a)--(d);
Stacks Project, Etale Cohomology, proof of Tag 0A4F, and Constructions, Tags 01NE and 01NG
(blueprint: lem-weil-pbc-symmetric-product-properties).

The positive integer n is written m + 1. The product is described by its universal
cone in schemes over S; this applies in particular to the inductively formed fibre product.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Classical in
private theorem coeff_prod_linear {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (a b : ι → R) (j : ℕ) :
    (∏ i, (Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i))).coeff j =
      ∑ J ∈ (Finset.univ : Finset ι).powerset.filter (fun J ↦ J.card = j),
        (∏ i ∈ J, a i) * ∏ i ∈ (Finset.univ : Finset ι) \ J, b i := by
  classical
  rw [Finset.prod_add]
  have ht (J : Finset ι) :
      (∏ i ∈ J, (Polynomial.C (a i) * Polynomial.X)) *
          ∏ i ∈ (Finset.univ : Finset ι) \ J, Polynomial.C (b i) =
        Polynomial.C ((∏ i ∈ J, a i) *
          ∏ i ∈ (Finset.univ : Finset ι) \ J, b i) * Polynomial.X ^ J.card := by
    rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod, Finset.prod_const, Polynomial.C_mul]
    ring
  simp_rw [ht, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  simp only [Finset.sum_filter, eq_comm]

open Classical in
private theorem monomial_pair {n : ℕ} [DecidableEq (Fin n)] (J : Finset (Fin n)) :
    (∏ i ∈ J, (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin n ⊕ Fin n) ℤ)) *
        ∏ i ∈ (Finset.univ : Finset (Fin n)) \ J, MvPolynomial.X (Sum.inr i) =
      MvPolynomial.monomial
        ((∑ i ∈ J, Finsupp.single (Sum.inl i) 1) +
          ∑ i ∈ (Finset.univ : Finset (Fin n)) \ J, Finsupp.single (Sum.inr i) 1) 1 := by
  rw [show (1 : ℤ) = 1 * 1 from rfl, ← MvPolynomial.monomial_mul,
    MvPolynomial.monomial_sum_one, MvPolynomial.monomial_sum_one]
  rfl

open Classical in
/-- The multidegree part. (blueprint: lem-weil-pbc-symmetric-product-properties) -/
private theorem symmetricProduct_properties_support (n : ℕ) (hn : 0 < n) (j : Fin (n + 1))
    (d : (Fin n ⊕ Fin n) →₀ ℕ)
    (hd : d ∈ (symmetricProductPolynomial n hn j).support) (i : Fin n) :
    d (Sum.inl i) + d (Sum.inr i) = 1 := by
  have hc := coeff_prod_linear (R := MvPolynomial (Fin n ⊕ Fin n) ℤ)
    (fun i ↦ MvPolynomial.X (Sum.inl i)) (fun i ↦ MvPolynomial.X (Sum.inr i)) j.val
  unfold symmetricProductPolynomial at hd
  rw [hc] at hd
  obtain ⟨J, hJ, hdJ⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  rw [monomial_pair] at hdJ
  have hd' := MvPolynomial.support_monomial_subset hdJ
  simp only [Finset.mem_singleton] at hd'
  subst d
  simp only [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte,
    Finset.sum_const_zero, add_zero, zero_add]
  by_cases hi : i ∈ J <;> simp [Finset.sum_ite_eq', hi]

private theorem symmetricProductLineBundle_invertible {S X : Scheme.{v}} (m : ℕ)
    (pr : Fin (m + 1) → (X ⟶ ℙ(ULift.{v} (Fin 2); S))) :
    (symmetricProductLineBundle pr).IsInvertible := by
  have hf (i : Fin (m + 1)) : (symmetricProductFactor pr i).IsInvertible :=
    ((Scheme.Modules.invertible_pullback_tensor (pr i)).1
      (ProjectiveSpace.twist _ S 1)).2
  change (Scheme.Modules.positiveTensorFamily m (symmetricProductFactor pr)).IsInvertible
  have hall : ∀ (n : ℕ) (L : Fin (n + 1) → X.Modules),
      (∀ i, (L i).IsInvertible) → (Scheme.Modules.positiveTensorFamily n L).IsInvertible := by
    intro n
    induction n with
    | zero => intro L h; exact h 0
    | succ n ih =>
      intro L h
      have h₁ := ih (fun i ↦ L i.castSucc) (fun i ↦ h i.castSucc)
      have h₂ := h (Fin.last (n + 1))
      exact (Scheme.Modules.invertible_pullback_tensor (𝟙 X)).2.1 _ _
  exact hall m _ hf

open Classical in
/-- The coefficient formula, multidegree, generation, coordinate morphism and its
invariance under permutations of the factors.

Source: blueprint symmetric-product-properties, parts (a)--(d); Stacks Tag 0A4F
(blueprint: lem-weil-pbc-symmetric-product-properties).

Proof:
1. Expand the product of linear forms using product-linear-forms-coefficients. Each
   monomial uses precisely one variable from each pair. Tensoring the corresponding
   pulled-back sections gives F_j in L_n; invertible-pullback-tensor gives invertibility.
2. The two coordinate sections have no common zero: the standard opens D_+(T_0),
   D_+(T_1) cover P^1 (01NG), and T_k is a basis on its own chart. Pullback preserves
   their fibrewise nonvanishing by invertible-pullback-tensor.
3. Let J index the factors where the second coordinate vanishes at the point. In
   F_|J|, the tensor indexed by J is nonvanishing. Every other subset K of that size
   omits some member of J, so its tensor vanishes. Thus F_|J| is nonvanishing. The
   invertible-generating-sections-fibre criterion gives the epimorphism.
4. Apply projective-space-functor-of-points (01NE) and the recorded morphism-by-sections
   construction to obtain sigma_n, its projections and its section-preserving isomorphism.
5. The product universal property constructs the permutation automorphism and its
   inverse. Pullback-composition and tensor symmetry give beta. Permuting the subsets
   in the tensor coefficient formula proves beta(tau^* F_j) = F_j.
6. Both composites to S agree. The integral composites agree because pullback of the
   generating pair is isomorphic via beta to the original pair, and 01NE gives uniqueness.
   The fibre-product universal property gives tau followed by sigma_n equals sigma_n. -/
theorem symmetricProduct_properties (S : Scheme.{v}) (m : ℕ)
    (X : Over S)
    (pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift.{v} (Fin 2); S) ↘ S)))
    (_hprod : IsLimit (Fan.mk X pr)) :
    (∀ j : Fin (m + 2),
      symmetricProductPolynomial (m + 1) (Nat.zero_lt_succ m) j =
        ∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset.filter
            (fun J ↦ J.card = j.val),
          (∏ i ∈ J, MvPolynomial.X (Sum.inl i)) *
            ∏ i ∈ (Finset.univ : Finset (Fin (m + 1))) \ J,
              MvPolynomial.X (Sum.inr i)) ∧
    (∀ j : Fin (m + 2),
      ∀ d ∈ (symmetricProductPolynomial (m + 1) (Nat.zero_lt_succ m) j).support,
        ∀ i : Fin (m + 1), d (Sum.inl i) + d (Sum.inr i) = 1) ∧
    (∀ z : X.left, ∃ j : ULift.{v} (Fin (m + 2)),
      z ∈ Scheme.Modules.nonvanishingLocus
        (symmetricProductLineBundle (fun i ↦ (pr i).left))
        ((symmetricProductCoordinateSection (fun i ↦ (pr i).left) j).val
          (Opposite.op ⊤))) ∧
    ∃ (hL : (symmetricProductLineBundle (fun i ↦ (pr i).left)).IsInvertible)
      (hs : Epi ((symmetricProductLineBundle (fun i ↦ (pr i).left)).freeHomEquiv.symm
        (symmetricProductCoordinateSection (fun i ↦ (pr i).left)))),
      ∃ σ : X.left ⟶ ℙ(ULift.{v} (Fin (m + 2)); S),
        σ = @ProjectiveSpace.homOfGeneratingSections.{v}
          (ULift.{v} (Fin (m + 2))) _ X.left S X.hom
          (symmetricProductLineBundle (fun i ↦ (pr i).left)) hL
          (symmetricProductCoordinateSection (fun i ↦ (pr i).left)) hs ∧
        σ ≫ ℙ(ULift.{v} (Fin (m + 2)); S) ↘ S = X.hom ∧
        ∃ ψ : X.left ⟶ ℙ(ULift.{v} (Fin (m + 2)); Spec (CommRingCat.of (ULift.{v} ℤ))),
          σ ≫ ProjectiveSpace.toProjInt _ S = ψ ≫ ProjectiveSpace.toProjInt _ _ ∧
          (∃ e : (Scheme.Modules.tensorPullback ψ).obj
              (ProjectiveSpace.twist (ULift.{v} (Fin (m + 2)))
                (Spec (CommRingCat.of (ULift.{v} ℤ))) 1) ≅
              symmetricProductLineBundle (fun i ↦ (pr i).left),
            ∀ j : ULift.{v} (Fin (m + 2)),
              e.hom.app ⊤ (((Classical.choose
                (Scheme.Modules.exists_tensorPullbackAdjunction ψ)).unit.app
                  (ProjectiveSpace.twist (ULift.{v} (Fin (m + 2)))
                    (Spec (CommRingCat.of (ULift.{v} ℤ))) 1)).val.app (Opposite.op ⊤)
                      (ProjectiveSpace.twistOneSection _ _ j)) =
                (symmetricProductCoordinateSection (fun i ↦ (pr i).left) j).val
                  (Opposite.op ⊤)) ∧
          ∀ π : Equiv.Perm (Fin (m + 1)), ∃ τ : X ≅ X,
            (∀ i, τ.hom ≫ pr i = pr (π i)) ∧
            (∀ i, τ.inv ≫ pr i = pr (π.symm i)) ∧
            (∃ β : (Scheme.Modules.tensorPullback τ.hom.left).obj
                (symmetricProductLineBundle (fun i ↦ (pr i).left)) ≅
                symmetricProductLineBundle (fun i ↦ (pr i).left),
              ∀ j : ULift.{v} (Fin (m + 2)),
                β.hom.app ⊤ (((Classical.choose
                  (Scheme.Modules.exists_tensorPullbackAdjunction τ.hom.left)).unit.app
                    (symmetricProductLineBundle (fun i ↦ (pr i).left))).val.app
                      (Opposite.op ⊤)
                        ((symmetricProductCoordinateSection (fun i ↦ (pr i).left) j).val
                          (Opposite.op ⊤))) =
                  (symmetricProductCoordinateSection (fun i ↦ (pr i).left) j).val
                    (Opposite.op ⊤)) ∧
            τ.hom.left ≫ σ = σ := by
  have hn := symmetricProduct_sections_nonvanishing m (fun i ↦ (pr i).left)
  have hL := symmetricProductLineBundle_invertible m (fun i ↦ (pr i).left)
  have hs := (Scheme.Modules.invertible_generating_sections_fibre_criterion X.left
    (symmetricProductLineBundle (fun i ↦ (pr i).left)) (m + 1)
    (symmetricProductCoordinateSection (fun i ↦ (pr i).left))).1.mpr hn
  refine ⟨?_, (fun j d hd i ↦ symmetricProduct_properties_support (m + 1)
    (Nat.zero_lt_succ m) j d hd i), hn, hL, hs, ?_⟩
  · intro j
    exact coeff_prod_linear (R := MvPolynomial (Fin (m + 1) ⊕ Fin (m + 1)) ℤ)
      (fun i ↦ MvPolynomial.X (Sum.inl i)) (fun i ↦ MvPolynomial.X (Sum.inr i)) j.val
  let L := symmetricProductLineBundle (fun i ↦ (pr i).left)
  let s := symmetricProductCoordinateSection (fun i ↦ (pr i).left)
  let σ := ProjectiveSpace.homOfGeneratingSections _ X.hom L s hs
  let ψ := ProjectiveSpace.integralHomOfGeneratingSections _ L s hs
  have hσ := ProjectiveSpace.homOfGeneratingSections_spec _ X.hom L s hs
  obtain ⟨eψ, heψ⟩ := ProjectiveSpace.integralHomOfGeneratingSections_spec _ L s hs
  refine ⟨σ, rfl, hσ.1, ψ, hσ.2.1, ⟨eψ, heψ⟩, ?_⟩
  intro π
  let f := Fan.IsLimit.lift _hprod (fun i ↦ pr (π i))
  let g := Fan.IsLimit.lift _hprod (fun i ↦ pr (π.symm i))
  have hf (i) : f ≫ pr i = pr (π i) := Fan.IsLimit.fac _hprod _ i
  have hg (i) : g ≫ pr i = pr (π.symm i) := Fan.IsLimit.fac _hprod _ i
  let τ : X ≅ X :=
    { hom := f
      inv := g
      hom_inv_id := by
        apply Fan.IsLimit.hom_ext _hprod
        intro i
        change (f ≫ g) ≫ pr i = (𝟙 X) ≫ pr i
        simp only [Category.assoc, hg, hf, Equiv.apply_symm_apply, Category.id_comp]
      inv_hom_id := by
        apply Fan.IsLimit.hom_ext _hprod
        intro i
        change (g ≫ f) ≫ pr i = (𝟙 X) ≫ pr i
        simp only [Category.assoc, hf, hg, Equiv.symm_apply_apply, Category.id_comp] }
  obtain ⟨β, hβ⟩ := symmetricProduct_sections_permutation m (fun i ↦ (pr i).left)
    τ.hom.left π (fun i ↦ congrArg (fun q ↦ q.left) (hf i))
  refine ⟨τ, hf, hg, ⟨β, hβ⟩, ?_⟩
  obtain ⟨e', he'⟩ := (projectiveSpace_functor_of_points (m + 1)).2.2 X.left X.left
    τ.hom.left ψ L (fun i ↦ (s (ULift.up i)).val (Opposite.op ⊤)) eψ
    (fun i ↦ heψ (ULift.up i))
  have hψ : τ.hom.left ≫ ψ = ψ := by
    apply (Classical.choose_spec
      (ProjectiveSpace.generatingSections_integralHom_exists _ L s hs)).2
    refine ⟨e' ≪≫ β, ?_⟩
    intro j
    change β.hom.app ⊤ (e'.hom.app ⊤ _) = _
    rw [he' j.down, hβ j]
  apply hσ.2.2
  · rw [Category.assoc, hσ.1]
    exact Over.w τ.hom
  · rw [Category.assoc, hσ.2.1, ← Category.assoc, hψ]

end AlgebraicGeometry
