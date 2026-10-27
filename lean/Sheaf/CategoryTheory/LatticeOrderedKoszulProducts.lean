/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison
public import Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Sheaf.CategoryTheory.KoszulSingleTensorNormalization
import Sheaf.CategoryTheory.KoszulTrivialSubsetDecomposition
import Sheaf.CategoryTheory.KoszulSubsetShuffleBinary

/-! # Ordered subset products in the trivial internal Koszul complex

Source: blueprint direct-image stability proof, paragraph (3), the agent-formulated
algebraic dense-lattice normalization; Stacks Tag 0FNH for ordered tensor shifts
(blueprint: lem-sfb-lattice-ordered-koszul-products).

The original Koszul model, its subset coordinates, and its cup pairing are retained.
The single complexes below are the degree-q presentations of R[0][-q]. Their tensor
identifications are pinned by unsigned regular multiplication on the unique summand.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Profinite.DiscreteLattice.OrderedKoszul

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- Finite biproducts of complexes are the existing finite products in this additive category.
Source: paragraph (3), subset decomposition
(blueprint: lem-sfb-lattice-ordered-koszul-products). -/
instance complexBiproducts : HasFiniteBiproducts (CochainComplex (Modules R) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- R placed in degree q, the canonical single-term presentation of R[0][-q].
Source: paragraph (3), ordered normalization
(blueprint: lem-sfb-lattice-ordered-koszul-products). -/
abbrev single (q : ℕ) : CochainComplex (Modules R) ℤ :=
  (HomologicalComplex.single (Modules R) (.up ℤ) (q : ℤ)).obj (𝟙_ (Modules R))

/-- The left-associated product, normalized at each step by the ordered identification.
The empty product is the empty-subset inclusion, with no symmetry of factors.
Source: paragraph (3), proof step 5
(blueprint: lem-sfb-lattice-ordered-koszul-products). -/
def orderedProduct {r : ℕ} {K : CochainComplex (Modules R) ℤ}
    (star : K ⊗ K ⟶ K)
    (incl : ∀ I : Finset (Fin r), single R I.card ⟶ K)
    (mul : ∀ p q : ℕ, single R p ⊗ single R q ≅ single R (p + q)) :
    ∀ q : ℕ, (Fin q → Fin r) → (single R q ⟶ K)
  | 0, _ => incl ∅
  | q + 1, f => (mul q 1).inv ≫
      (orderedProduct star incl mul q (fun i ↦ f i.castSucc) ⊗ₘ
        incl {f (Fin.last q)}) ≫ star

/-- The derived product uses the same ordered identifications, localized through the
canonical K-flat tensor comparison. The theorem below asserts that these comparisons
are invertible, so the inverses here are actual inverses.
Source: paragraph (3), proof step 6
(blueprint: lem-sfb-lattice-ordered-koszul-products). -/
def derivedOrderedProduct {r : ℕ} {K : CochainComplex (Modules R) ℤ}
    (star : K ⊗ K ⟶ K)
    (incl : ∀ I : Finset (Fin r), single R I.card ⟶ K)
    (mul : ∀ p q : ℕ, single R p ⊗ single R q ≅ single R (p + q))
    (hmodel : ∀ p q : ℕ,
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} (single R p) (single R q))) :
    ∀ q : ℕ, (Fin q → Fin r) →
      (DerivedCategory.Q.{u + 2}.obj (single R q) ⟶ DerivedCategory.Q.{u + 2}.obj K)
  | 0, _ => DerivedCategory.Q.map (incl ∅)
  | q + 1, f => DerivedCategory.Q.map (mul q 1).inv ≫
      @inv _ _ _ _
        (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} (single R q) (single R 1)) (hmodel q 1) ≫
      (derivedOrderedProduct star incl mul hmodel q (fun i ↦ f i.castSucc) ⊗ₘ
        DerivedCategory.Q.map (incl {f (Fin.last q)})) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} K K ≫ DerivedCategory.Q.map star

/-- All normalizations and identities for the existing trivial regular-algebra cup.
The inclusion, decomposition, and tensor identification fields are specified by their
coordinates, so none can be replaced by arbitrary morphisms or signed identifications.
Source: paragraph (3), proof steps 1--6; Stacks Tag 0FNH
(blueprint: lem-sfb-lattice-ordered-koszul-products). -/
structure Products (r : ℕ) (K : KoszulModel R r) (c : Comparison R r K)
    (cup : TriangulatedCup.CupComparison R r K c (Mon.trivial (Equivariant R r))) where
  single_shift : ∀ q : ℕ, single R q ≅ (single R 0)⟦(-(q : ℤ))⟧
  single_shift_coordinates : ∀ q : ℕ,
    (single_shift q).hom.f (q : ℤ) ≫
      (CochainComplex.shiftFunctorObjXIso (single R 0) (-(q : ℤ)) (q : ℤ) 0
        (by omega)).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R))).hom =
        (HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (𝟙_ (Modules R))).hom
  differential_zero : ∀ a b : ℤ,
    (K.functor.obj (𝟙_ (Equivariant R r))).d a b = 0
  incl : ∀ I : Finset (Fin r), single R I.card ⟶ K.functor.obj (𝟙_ (Equivariant R r))
  incl_coordinates : ∀ (I : Finset (Fin r)) (J : Subsets r (I.card : ℤ)),
    (HomologicalComplex.singleObjXSelf (.up ℤ) (I.card : ℤ) (𝟙_ (Modules R))).inv ≫
      (incl I).f (I.card : ℤ) ≫ (K.coordinates (𝟙_ (Equivariant R r)) I.card).hom ≫
      biproduct.π _ J = if I = J.val then 𝟙 _ else 0
  decomposition :
    (⨁ fun I : Finset (Fin r) ↦ single R I.card) ≅ K.functor.obj (𝟙_ (Equivariant R r))
  decomposition_incl : ∀ I : Finset (Fin r),
    biproduct.ι (fun I : Finset (Fin r) ↦ single R I.card) I ≫ decomposition.hom = incl I
  kflat : ∀ E : CochainComplex (Modules R) ℤ, E.Acyclic →
    (K.functor.obj (𝟙_ (Equivariant R r)) ⊗ E).Acyclic
  mul : ∀ p q : ℕ, single R p ⊗ single R q ≅ single R (p + q)
  mul_coordinates : ∀ p q : ℕ,
    ((HomologicalComplex.singleObjXSelf (.up ℤ) (p : ℤ) (𝟙_ (Modules R))).inv ⊗ₘ
      (HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (𝟙_ (Modules R))).inv) ≫
      HomologicalComplex.ιTensorObj (single R p) (single R q) (p : ℤ) (q : ℤ)
        ((p + q : ℕ) : ℤ) (Nat.cast_add p q).symm ≫
      (mul p q).hom.f ((p + q : ℕ) : ℤ) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) ((p + q : ℕ) : ℤ)
        (𝟙_ (Modules R))).hom = (λ_ (𝟙_ (Modules R))).hom
  binary : ∀ A C : Finset (Fin r), (incl A ⊗ₘ incl C) ≫ cup.star =
    if h : Disjoint A C then
      ((-1 : ℤ) ^ ((A.product C).filter (fun ac ↦ ac.2 < ac.1)).card) •
        ((mul A.card C.card).hom ≫
          eqToHom (congrArg (single R) (Finset.card_union_of_disjoint h).symm) ≫ incl (A ∪ C))
    else 0
  increasing : ∀ (q : ℕ) (f : Fin q → Fin r) (hf : StrictMono f),
    orderedProduct R cup.star incl mul q f =
      eqToHom (congrArg (single R) (by
        simp [Finset.card_image_of_injective Finset.univ hf.injective])) ≫
        incl (Finset.univ.image f)
  empty_unit : incl ∅ = cup.unit
  tensor_model : ∀ p q : ℕ,
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} (single R p) (single R q))
  derived_binary : ∀ A C : Finset (Fin r),
    (DerivedCategory.Q.{u + 2}.map (incl A) ⊗ₘ DerivedCategory.Q.map (incl C)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2}
        (K.functor.obj (𝟙_ (Equivariant R r))) (K.functor.obj (𝟙_ (Equivariant R r))) ≫
      DerivedCategory.Q.map cup.star =
    if h : Disjoint A C then
      ((-1 : ℤ) ^ ((A.product C).filter (fun ac ↦ ac.2 < ac.1)).card) •
        (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} (single R A.card) (single R C.card) ≫
          DerivedCategory.Q.map ((mul A.card C.card).hom ≫
            eqToHom (congrArg (single R) (Finset.card_union_of_disjoint h).symm) ≫ incl (A ∪ C)))
    else 0
  derived_increasing : ∀ (q : ℕ) (f : Fin q → Fin r) (hf : StrictMono f),
    derivedOrderedProduct R cup.star incl mul tensor_model q f =
      DerivedCategory.Q.map
        (eqToHom (congrArg (single R) (by
          simp [Finset.card_image_of_injective Finset.univ hf.injective])) ≫
        incl (Finset.univ.image f))
  rank_zero_iso : r = 0 → (K.functor.obj (𝟙_ (Equivariant R r)) ≅ single R 0)
  rank_zero_coordinates : ∀ h : r = 0,
    (rank_zero_iso h).hom.f 0 = (K.coordinates (𝟙_ (Equivariant R r)) 0).hom ≫
      biproduct.π _ ⟨∅, rfl⟩ ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R))).inv
  rank_zero_identity : ∀ h : r = 0, incl ∅ ≫ (rank_zero_iso h).hom = 𝟙 (single R 0)

private theorem inclusion_transport {r : ℕ} {K : CochainComplex (Modules R) ℤ}
    (incl : ∀ I : Finset (Fin r), single R I.card ⟶ K)
    {A B : Finset (Fin r)} (h : A = B) {n : ℕ}
    {hA : n = A.card} {hB : n = B.card} :
    eqToHom (congrArg (single R) hA) ≫ incl A =
      eqToHom (congrArg (single R) hB) ≫ incl B := by
  subst B
  rfl

private theorem ordered_step {r : ℕ} {K : CochainComplex (Modules R) ℤ}
    (star : K ⊗ K ⟶ K)
    (incl : ∀ I : Finset (Fin r), single R I.card ⟶ K)
    (mul : ∀ p q : ℕ, single R p ⊗ single R q ≅ single R (p + q))
    (binary : ∀ A C : Finset (Fin r), (incl A ⊗ₘ incl C) ≫ star =
      if h : Disjoint A C then
        ((-1 : ℤ) ^ ((A.product C).filter (fun ac ↦ ac.2 < ac.1)).card) •
          ((mul A.card C.card).hom ≫
            eqToHom (congrArg (single R) (Finset.card_union_of_disjoint h).symm) ≫
              incl (A ∪ C))
      else 0)
    (n : ℕ) (A : Finset (Fin r)) (b : Fin r) (hn : n = A.card)
    (hb : Disjoint A {b}) (hlt : ∀ a ∈ A, a < b) :
    (mul n 1).inv ≫
      ((eqToHom (congrArg (single R) hn) ≫ incl A) ⊗ₘ incl {b}) ≫ star =
    eqToHom (congrArg (single R) (by
      rw [Finset.card_union_of_disjoint hb, Finset.card_singleton, hn])) ≫
        incl (A ∪ {b}) := by
  subst n
  have hz : (A.product {b}).filter (fun ac ↦ ac.2 < ac.1) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro ac hac hlt'
    obtain ⟨ha, hc⟩ := Finset.mem_product.mp hac
    have hc' : ac.2 = b := Finset.mem_singleton.mp hc
    exact (hlt ac.1 ha).not_gt (hc' ▸ hlt')
  have hcalc := binary A {b}
  rw [dif_pos hb, hz] at hcalc
  simp only [Finset.card_empty, pow_zero, one_zsmul] at hcalc
  change (incl A ⊗ₘ incl {b}) ≫ star =
    (mul A.card 1).hom ≫ eqToHom _ ≫ incl (A ∪ {b}) at hcalc
  simpa only [eqToHom_refl, Category.id_comp, Category.assoc,
    Iso.inv_hom_id_assoc] using congrArg ((mul A.card 1).inv ≫ ·) hcalc

private theorem orderedProduct_increasing {r : ℕ} {K : CochainComplex (Modules R) ℤ}
    (star : K ⊗ K ⟶ K)
    (incl : ∀ I : Finset (Fin r), single R I.card ⟶ K)
    (mul : ∀ p q : ℕ, single R p ⊗ single R q ≅ single R (p + q))
    (binary : ∀ A C : Finset (Fin r), (incl A ⊗ₘ incl C) ≫ star =
      if h : Disjoint A C then
        ((-1 : ℤ) ^ ((A.product C).filter (fun ac ↦ ac.2 < ac.1)).card) •
          ((mul A.card C.card).hom ≫
            eqToHom (congrArg (single R) (Finset.card_union_of_disjoint h).symm) ≫
              incl (A ∪ C))
      else 0)
    (q : ℕ) (f : Fin q → Fin r) (hf : StrictMono f) :
    orderedProduct R star incl mul q f =
      eqToHom (congrArg (single R) (by
        simp [Finset.card_image_of_injective Finset.univ hf.injective])) ≫
          incl (Finset.univ.image f) := by
  induction q with
  | zero =>
    have he : Finset.univ.image f = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, _, _⟩ := Finset.mem_image.mp hx
      exact Fin.elim0 i
    simpa only [orderedProduct, eqToHom_refl, Category.id_comp] using
      (inclusion_transport R incl he (n := 0) (hA := by rw [he]; rfl) (hB := rfl)).symm
  | succ q ih =>
    let g : Fin q → Fin r := fun i ↦ f i.castSucc
    have hg : StrictMono g := hf.comp Fin.strictMono_castSucc
    let A := Finset.univ.image g
    let b := f (Fin.last q)
    have hn : q = A.card := by
      simp [A, Finset.card_image_of_injective Finset.univ hg.injective]
    have hlt : ∀ a ∈ A, a < b := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hf (Fin.castSucc_lt_last i)
    have hb : Disjoint A {b} := by
      rw [Finset.disjoint_singleton_right]
      intro h
      exact (hlt b h).ne rfl
    have hU : A ∪ {b} = Finset.univ.image f := by
      ext x
      simp only [A, b, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro (⟨i, rfl⟩ | rfl)
        · exact ⟨i.castSucc, rfl⟩
        · exact ⟨Fin.last q, rfl⟩
      · rintro ⟨i, rfl⟩
        exact Fin.lastCases (Or.inr rfl) (fun j ↦ Or.inl ⟨j, rfl⟩) i
    dsimp only [orderedProduct]
    rw [ih g hg]
    have hs := ordered_step R star incl mul binary q A b hn hb hlt
    exact hs.trans (inclusion_transport R incl hU
      (hA := by rw [Finset.card_union_of_disjoint hb, Finset.card_singleton, hn])
      (hB := by simp [Finset.card_image_of_injective Finset.univ hf.injective]))

private theorem derivedOrderedProduct_eq {r : ℕ} {K : CochainComplex (Modules R) ℤ}
    (star : K ⊗ K ⟶ K)
    (incl : ∀ I : Finset (Fin r), single R I.card ⟶ K)
    (mul : ∀ p q : ℕ, single R p ⊗ single R q ≅ single R (p + q))
    (hmodel : ∀ p q : ℕ,
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} (single R p) (single R q)))
    (q : ℕ) (f : Fin q → Fin r) :
    derivedOrderedProduct R star incl mul hmodel q f =
      DerivedCategory.Q.map (orderedProduct R star incl mul q f) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    let := hmodel q 1
    dsimp only [derivedOrderedProduct, orderedProduct]
    rw [ih]
    simp only [Functor.map_comp]
    rw [Functor.LaxMonoidal.μ_natural_assoc]
    simp only [IsIso.inv_hom_id_assoc]

private theorem trivial_differential_zero (r : ℕ) (K : KoszulModel R r) (a b : ℤ) :
    (K.functor.obj (𝟙_ (Equivariant R r))).d a b = 0 := by
  by_cases h : a + 1 = b
  · subst b
    apply (cancel_mono (K.coordinates (𝟙_ (Equivariant R r)) (a + 1)).hom).1
    apply biproduct.hom_ext
    intro J
    apply (cancel_epi (K.coordinates (𝟙_ (Equivariant R r)) a).inv).1
    apply biproduct.hom_ext'
    intro I
    simpa only [Category.assoc, Limits.zero_comp, Limits.comp_zero] using
      (K.differential (𝟙_ (Equivariant R r)) a I J).trans (by
        simp [differentialEntry])
  · exact (K.functor.obj (𝟙_ (Equivariant R r))).shape a b h

/-- The trivial internal Koszul complex has its canonical subset decomposition,
unsigned ordered tensor identifications, and the stated chain and derived products.
No nonzero-ring, characteristic, flatness, or completeness assumption is imposed on R.

Source: blueprint direct-image stability proof paragraph (3), agent-formulated
algebraic dense-lattice input; Stacks Tag 0FNH for the shift convention
(blueprint: lem-sfb-lattice-ordered-koszul-products).

Proof, following the six DAG steps:
1. Each T_i-1 is zero. The subset inclusions and projections are mutually inverse
finite-biproduct matrices, giving the zero differential and complex decomposition.
For rank zero only the empty subset remains and its inclusion is the identity.
2. The relative regular-module unitor makes R tensor - exact. Apply the existing
flat-algebra cup comparison with the trivial regular algebra. It gives K-flatness,
the shuffle pairing and its empty-degree unit, representing the canonical derived cup.
3. Extract the first shift and then the second. The first comparison is unsigned;
the second has first-factor degree zero, so its sign is +1. The resulting map is
regular multiplication. Associativity of multiplication makes ordered iterations coherent.
4. Test the pairing on every finite biproduct component. The only surviving shuffle
is (A,C), when disjoint; its coefficient is the inversion sign. If they intersect,
there is no such partition and every component vanishes. The finite-free coordinate
lemma performs this calculation internally, without sectionwise tensor assumptions.
5. Induct on an increasing list. At each split all earlier indices precede the last
one, so the inversion set is empty and the surviving coefficient is +1. The empty
list gives the unit. The same calculation at consecutive blocks handles any bracketing.
6. Each S_p is K-flat: tensor with an acyclic E reindexes E and multiplies its
differential by (-1)^p. The K-flat localization comparison is natural, so applying Q
to the chain identities gives the displayed derived binary and iterated identities.
All calculations use finite sums and regular multiplication, valid also for the zero
ring and in characteristic two. -/
theorem lattice_ordered_koszul_products (r : ℕ) (K : KoszulModel R r)
    (c : Comparison R r K)
    (cup : TriangulatedCup.CupComparison R r K c (Mon.trivial (Equivariant R r))) :
    Nonempty (Products R r K c cup) := by
  obtain ⟨single_shift, mul, hshift, hmul, hmodel⟩ := single_tensor_normalization R
  have hd := trivial_differential_zero R r K
  obtain ⟨incl, decomposition, rank_zero_iso, hi, hdec, hunit, hzero, hid⟩ :=
    trivial_subset_decomposition R r K c cup hd
  have hb := subset_shuffle_binary R r K c cup incl mul hi hmul
  have hincr := orderedProduct_increasing R cup.star incl mul hb
  refine ⟨{
    single_shift := single_shift
    single_shift_coordinates := hshift
    differential_zero := hd
    incl := incl
    incl_coordinates := hi
    decomposition := decomposition
    decomposition_incl := hdec
    kflat := cup.kflat
    mul := mul
    mul_coordinates := hmul
    binary := hb
    increasing := hincr
    empty_unit := hunit
    tensor_model := hmodel
    derived_binary := ?_
    derived_increasing := ?_
    rank_zero_iso := rank_zero_iso
    rank_zero_coordinates := hzero
    rank_zero_identity := hid
  }⟩
  · intro A C
    rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp, hb]
    split_ifs
    · rw [Functor.map_zsmul, Preadditive.comp_zsmul]
    · rw [Functor.map_zero, Limits.comp_zero]
  · intro q f hf
    rw [derivedOrderedProduct_eq, hincr q f hf]

end Profinite.DiscreteLattice.OrderedKoszul
