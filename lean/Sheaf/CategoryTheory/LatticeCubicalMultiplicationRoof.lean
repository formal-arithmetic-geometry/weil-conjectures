/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.CategoryTheory.LatticeCubicalMultiplicationData

import Sheaf.CategoryTheory.LatticeCubicalNormalizedRoof
import Sheaf.CategoryTheory.LatticeCubicalNumeratorComparison
import Sheaf.CategoryTheory.LatticeCubicalTensorRepresentatives
import Mathlib.Tactic.Ring

/-! # Cubical comparison of multiplication evaluation roofs

Source: direct-images paragraph (3), lattice expansion, steps 12--14
(blueprint: lem-sfb-lattice-cubical-multiplication-roof).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace Profinite.DiscreteLattice.CubicalMultiplication

variable (R : CategoryTheory.CondensedBar.Ring.{u}) (r : ℕ)
    (J : CubicalEvaluation.DiscreteComparison R r)
    (C : CubicalEvaluation.CubicalModel R r)
    (K : KoszulModel R.toMon r) (B : DerivedCup.Algebra R.toMon r)
    (P : FlatTwisted.Pairing K B)

private theorem sign_add (p q : ℕ) :
    CubicalEvaluation.cSign (p + q) =
      (-1 : ℤ) ^ (p * q) * CubicalEvaluation.cSign p * CubicalEvaluation.cSign q := by
  have hp : p * (p + 1) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp (Nat.even_mul_succ_self p))
  have hq : q * (q + 1) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp (Nat.even_mul_succ_self q))
  have hnum : (p + q) * (p + q + 1) = p * (p + 1) + q * (q + 1) + 2 * (p * q) := by
    ring
  have htri : (p + q) * (p + q + 1) / 2 =
      p * (p + 1) / 2 + q * (q + 1) / 2 + p * q := by omega
  simp only [CubicalEvaluation.cSign, htri, pow_add]
  ring

private theorem localized_roof
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V]
    {W : Type*} [Category W] {X L Z : V} (F : Roof X L Z) (Q : V ⥤ W)
    (s : X ⊗ X ⟶ X) (m : Z ⊗ Z ⟶ Z)
    (hnum : F.f s = F.comparison ≫ F.g m) (hden : F.comparison ≫ F.b = F.a)
    [IsIso (Q.map F.a)] [IsIso (Q.map F.b)] : F.Localized Q s m := by
  refine ⟨asIso (Q.map F.a), asIso (Q.map F.b), rfl, rfl, ?_⟩
  change inv (Q.map F.a) ≫ Q.map (F.f s) = inv (Q.map F.b) ≫ Q.map (F.g m)
  have hn : Q.map (F.f s) = Q.map F.comparison ≫ Q.map (F.g m) := by
    rw [hnum, Q.map_comp]
  have hd : Q.map F.a = Q.map F.comparison ≫ Q.map F.b := by
    rw [← Q.map_comp, hden]
  apply (cancel_epi (Q.map F.a)).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [hn, hd]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

private theorem rank_zero_product :
    productCoordinate R r K B P 0 0 ⟨∅, rfl⟩ ⟨∅, rfl⟩ ⟨∅, rfl⟩ =
      (MonObj.mul (X := B.X)).hom := by
  rw [productCoordinate, Category.assoc, P.coordinates]
  simp only [Finset.disjoint_empty_left, Finset.empty_union, and_self, if_true,
    Finset.product_eq_sprod, Finset.empty_product, Finset.filter_empty,
    Finset.card_empty, pow_zero, one_smul,
    Finset.prod_empty, map_one, End.one_def, id_tensorHom_id, Category.id_comp]

private theorem rank_one_products (i : Fin r) :
    productCoordinate R r K B P 0 1 ⟨∅, rfl⟩ ⟨{i}, by simp⟩ ⟨{i}, by simp⟩ =
        (MonObj.mul (X := B.X)).hom ∧
    productCoordinate R r K B P 1 0 ⟨{i}, by simp⟩ ⟨∅, rfl⟩ ⟨{i}, by simp⟩ =
        (𝟙 B.X.V ⊗ₘ B.X.ρ (generator i)) ≫ (MonObj.mul (X := B.X)).hom := by
  constructor
  · rw [productCoordinate, Category.assoc, P.coordinates]
    simp only [Finset.disjoint_empty_left, Finset.empty_union, and_self, if_true,
      Finset.product_eq_sprod, Finset.empty_product, Finset.filter_empty,
      Finset.card_empty, pow_zero, one_smul,
      Finset.prod_empty, map_one, End.one_def, id_tensorHom_id, Category.id_comp]
  · rw [productCoordinate, Category.assoc, P.coordinates]
    simp only [Finset.disjoint_empty_right, Finset.union_empty, and_self, if_true,
      Finset.product_eq_sprod, Finset.product_empty, Finset.filter_empty,
      Finset.card_empty, pow_zero, one_smul,
      Finset.prod_singleton]

private theorem rank_one_diagonal
    (F : Roof (koszul R r K B) (lattice R r J C) (algebra R r B))
    (hF : Normalized R r J C K B F) (i : Fin r) (v : Fin r → ℤ) :
    cell R r J C (-1) v {i} ≫ (F.diagonal.f (-1)).hom =
      cellTensor R r J C (-1) v v ∅ {i} +
        cellTensor R r J C (-1) v (v + IntegralLatticeCubical.unitVector r i) {i} ∅ := by
  rw [hF.2.1 (-1) v {i} (by simp)]
  have hp : ({i} : Finset (Fin r)).powerset = {∅, {i}} := by
    change (insert i (∅ : Finset (Fin r))).powerset = _
    rw [Finset.powerset_insert]
    simp
  simp [hp, IntegralLatticeCubical.partitionSign, IntegralLatticeCubical.directionSum]

/-- The integral diagonal, signed evaluation, actual common denominator and localized
roof equalities, including the original algebra unit and low-rank formulas.
Source: paragraph (3), agent lattice expansion, steps 12--14
(blueprint: lem-sfb-lattice-cubical-multiplication-roof).

Proof:
1. Extend the integral cubical diagonal R-linearly on each free-cell inclusion.
The integral chain-map, translation and counit identities are finite integer identities,
so they hold internally; degree a becomes degree -a with unchanged tensor sign.
2. On supported coefficients A,C and a cell I, both numerators vanish unless A,C
partition I. The first then has coefficient c_(p+q) epsilon(A,C) T^v(x_A) T^(v+u_A)(y_C).
The second has epsilon(A,C)(-1)^(pq)c_p c_q times the same product, because its middle
interchange swaps degrees q and -p. The triangular-number identity gives equal signs.
Internal coproduct universal properties prove equality of the chain maps.
3. The double counit gives b delta=a. After forgetting action use the recorded integral
contraction h and e=s epsilon. On L tensor L set H=h tensor 1+(-1)^|l| e tensor h;
then dH+Hd=1-e tensor e. Tensoring with X uses (-1)^|x| times 1 tensor H. Both
augmentation denominators are homotopy equivalences after forgetting action. Exactness
detection gives their equivariant quasi-isomorphisms. Localization inverts them and
cancels the common comparison, yielding the equality with these actual denominators.
4. The flat-pairing theorem gives flat terms and K-flatness of tK_B; cubical terms are
free and its integral contraction gives K-flatness of L. Tensor products preserve these
properties, since the acyclicity-preserving tensor functors compose. Thus the ordinary
signed tensors are K-flat representatives for the canonical derived tensors.
5. Unit evaluation is zero on positive cells and sends every vertex to c_0 T^v(1_B)=1_B.
Rank zero has only the empty partition, giving ordinary multiplication and unit. Rank
one has exactly the two partitions (empty,{i}) and ({i},empty), both with sign one;
the second shifts the vertex by u_i and twists y by T_i. All formulas are finite sums
with integral signs, so include the zero ring, zero algebra and characteristic two. -/
theorem lattice_cubical_multiplication_roof [IsCommMonObj B.X]
    (hflat : exactFunctor (Modules R.toMon) (Modules R.toMon) (tensorLeft B.X.V)) :
    ∃ F : Roof (koszul R r K B) (lattice R r J C) (algebra R r B),
    (∀ v : Fin r → ℤ, cell R r J C 0 v ∅ ≫ (F.augmentation.f 0).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (Equivariant R.toMon r))).hom.hom = 𝟙 _) ∧
    (∀ (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)), (I.card : ℤ) = -n →
      cell R r J C n v I ≫ (F.diagonal.f n).hom =
        ∑ A ∈ I.powerset, IntegralLatticeCubical.partitionSign r A (I \ A) •
          cellTensor R r J C n v
            (v + IntegralLatticeCubical.directionSum r A) A (I \ A)) ∧
    (∀ (p : ℕ) (A : Subsets r (p : ℤ)) (v : Fin r → ℤ) (I : Subsets r (p : ℤ)),
      (coefficient R r K B p A ⊗ₘ cell R r J C (-(p : ℤ)) v I.val) ≫
        inclusion R r (koszul R r K B) (lattice R r J C) p (-(p : ℤ)) 0 ≫
        (F.evaluation.f 0).hom ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).hom.hom =
      if A = I then CubicalEvaluation.cSign p •
        ((ρ_ B.X.V).hom ≫ B.X.ρ (Multiplicative.ofAdd v)) else 0) ∧
    F.Identities (star R r K B P) (unit R r K B P) (mul R r B) (eta R r B) ∧
    (∀ p q : ℕ, CubicalEvaluation.cSign (p + q) =
      (-1 : ℤ) ^ (p * q) * CubicalEvaluation.cSign p * CubicalEvaluation.cSign q) ∧
    (∀ (p q : ℕ) (A : Subsets r (p : ℤ)) (A' : Subsets r (q : ℤ))
        (v : Fin r → ℤ) (I : Subsets r ((p : ℤ) + q)),
      supported R r J C K B p q A A' v I ≫
        ((F.f (star R r K B P)).f 0).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).hom.hom =
          value R r B p q A A' v I ∧
      supported R r J C K B p q A A' v I ≫
        ((F.comparison ≫ F.g (mul R r B)).f 0).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).hom.hom =
          value R r B p q A A' v I) ∧
    QuasiIso F.a ∧ QuasiIso F.b ∧
    F.Localized DerivedCategory.Q.{u + 2} (star R r K B P) (mul R r B) ∧
    (∀ W : CochainComplex (Equivariant R.toMon r) ℤ,
      (W = koszul R r K B ⊗ koszul R r K B ∨
        W = (koszul R r K B ⊗ koszul R r K B) ⊗ lattice R r J C ∨
        W = (koszul R r K B ⊗ lattice R r J C) ⊗ (koszul R r K B ⊗ lattice R r J C)) →
      ∀ V : CochainComplex (Equivariant R.toMon r) ℤ,
        V.Acyclic → (W ⊗ V).Acyclic) ∧
    (∀ W V : CochainComplex (Equivariant R.toMon r) ℤ,
      (W = koszul R r K B ⊗ koszul R r K B ∨
        W = (koszul R r K B ⊗ koszul R r K B) ⊗ lattice R r J C ∨
        W = (koszul R r K B ⊗ lattice R r J C) ⊗ (koszul R r K B ⊗ lattice R r J C)) →
      (V = koszul R r K B ⊗ koszul R r K B ∨
        V = (koszul R r K B ⊗ koszul R r K B) ⊗ lattice R r J C ∨
        V = (koszul R r K B ⊗ lattice R r J C) ⊗ (koszul R r K B ⊗ lattice R r J C)) →
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} W V)) ∧
    (r = 0 →
      productCoordinate R r K B P 0 0 ⟨∅, rfl⟩ ⟨∅, rfl⟩ ⟨∅, rfl⟩ =
        (MonObj.mul (X := B.X)).hom ∧
      P.unit.f 0 ≫ (K.coordinates B.X 0).hom ≫ biproduct.π _ ⟨∅, rfl⟩ =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R.toMon))).hom ≫
          (MonObj.one (X := B.X)).hom) ∧
    (r = 1 → ∀ i : Fin r,
      productCoordinate R r K B P 0 1 ⟨∅, rfl⟩ ⟨{i}, by simp⟩ ⟨{i}, by simp⟩ =
        (MonObj.mul (X := B.X)).hom ∧
      productCoordinate R r K B P 1 0 ⟨{i}, by simp⟩ ⟨∅, rfl⟩ ⟨{i}, by simp⟩ =
        (𝟙 B.X.V ⊗ₘ B.X.ρ (generator i)) ≫ (MonObj.mul (X := B.X)).hom) ∧
    (r = 1 → ∀ (i : Fin r) (v : Fin r → ℤ),
      cell R r J C (-1) v {i} ≫ (F.diagonal.f (-1)).hom =
        cellTensor R r J C (-1) v v ∅ {i} +
          cellTensor R r J C (-1) v (v + IntegralLatticeCubical.unitVector r i) {i} ∅) := by
  obtain ⟨F, hF⟩ := exists_normalized_roof R r J C K B
  obtain ⟨hnum, hunit, hcoeff⟩ := normalized_roof_numerators R r J C K B P F hF
  obtain ⟨hden, ha, hb, hflatT, hmu⟩ :=
    normalized_roof_tensor_representatives R r J C K B hflat F hF
  have : IsIso (DerivedCategory.Q.{u + 2}.map F.a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Equivariant R.toMon r) F.a).2 ha
  have : IsIso (DerivedCategory.Q.{u + 2}.map F.b) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Equivariant R.toMon r) F.b).2 hb
  refine ⟨F, hF.1, hF.2.1, hF.2.2.1, ?_, sign_add, ?_, ha, hb, ?_,
    hflatT, hmu, ?_, ?_, ?_⟩
  · exact ⟨hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2, hnum, hden, hunit⟩
  · intro p q A A' v I
    refine ⟨hcoeff p q A A' v I, ?_⟩
    rw [← hnum]
    exact hcoeff p q A A' v I
  · exact localized_roof F DerivedCategory.Q.{u + 2}
      (star R r K B P) (mul R r B) hnum hden
  · intro _
    exact ⟨rank_zero_product R r K B P, P.unitCoordinates ⟨∅, rfl⟩⟩
  · intro _ i
    exact rank_one_products R r K B P i
  · intro _ i v
    exact rank_one_diagonal R r J C K B F hF i v

end Profinite.DiscreteLattice.CubicalMultiplication
