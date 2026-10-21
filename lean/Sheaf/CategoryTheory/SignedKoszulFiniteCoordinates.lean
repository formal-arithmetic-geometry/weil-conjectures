/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.SignedKoszulCompletionModel

/-!
# Finite coordinates of the normalized negative Koszul tensors

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, finite free tensor calculation.
(blueprint: lem-cbc-signed-koszul-finite-coordinates).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The ordered negative Koszul tensors have normalized finite subset coordinates,
scalar-diagonal transitions, compatible empty-coordinate inclusions, and preserve
quasi-isomorphisms. No countable product, fibre, localization, or coefficient functor
comparison occurs in this finite statement.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, bounded finite free Koszul calculation;
steps 1--3 and 7 of lem-cbc-exact-linear-koszul-fiber.
(blueprint: lem-cbc-signed-koszul-finite-coordinates).

Proof in words: induct on the number of ordered factors. The empty tensor is O[0]
and its tensor with K is K by the right unitor. Split a subset into whether it contains
the first index and the subset of successor indices. The two supported degrees of the
first factor and distribution of tensor over finite direct sums identify the next
ordered tensor with the direct sum indexed by those subsets. The inclusion into a
subset coordinate is the inverse unitor, tensor of the specified basis maps, and the
total tensor inclusion; these are exactly ringedNegativeKoszulSummand. Multiplication
in the rank-one factors supplies inverse coordinates. Naturality of the unitors and
total tensor inclusions makes coefficient maps diagonal in these coordinates.
The first total differential is d_K. The differential of the ith negative factor
has coefficient a_i^(m+1), preceded by one sign for each earlier negative factor and
by (-1)^(q+|I|) for the coefficient degree. This is exactly the displayed erased-index
matrix, including all equality transports. Conjugate the diagonal scalar product over
I by these coordinates to construct the transition. Its chain equation reduces to
(product over I of a_j) a_i^(m+1) = a_i^(m+2) (product over I.erase i of a_j).
The empty-coordinate inclusions are chain maps and commute with transitions because
the empty product is one. Filter the tensor by subset cardinality at most k.
The kth quotient is the finite direct sum of reindexed copies of K with |I|=k,
whose differential is d_K; a degreewise sign twist identifies them with the usual
shifts. This filtration is finite and degreewise split. A quasi-isomorphism of K
induces quasi-isomorphisms on the quotients; the long exact homology sequences and
induction give a quasi-isomorphism on each tensor. This works for unbounded K.
For r=0 only the empty coordinate occurs. For r=1 the negative summand has
coefficient (-1)^(q+1) a_0^(m+1) and transition a_0. No inverse scalar is used, so
zero and unit scalars, zero rings, and empty sites are all allowed. -/
theorem exists_ringedSignedKoszulFiniteCoordinates
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin r → A) :
  letI := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  ∃ (coordinates : ∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ),
    ((ringedNegativeKoszulTensor O ρ a m).obj K).X q ≅
      ⨁ fun I : Finset (Fin r) ↦ K.X (q + I.card))
    (step : ∀ m : ℕ, ringedNegativeKoszulTensor O ρ a (m + 1) ⟶
      ringedNegativeKoszulTensor O ρ a m)
    (inclusion : ∀ m : ℕ, 𝟭 (ringedSiteComplex O) ⟶ (ringedNegativeKoszulTensor O ρ a) m),
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
      (I L : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates m K q).inv ≫
        (((ringedNegativeKoszulTensor O ρ a) m).obj K).d q (q + 1) ≫ (coordinates m K (q + 1)).hom ≫
          biproduct.π _ L =
      (if I = L then K.d (q + I.card) ((q + 1) + L.card) else 0) +
      (if h : q + (I.card : ℤ) = (q + 1) + (L.card : ℤ) then
        ringedKoszulCoefficientSMul O ρ (∑ i ∈ I, if I.erase i = L then
          (if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
            (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1) else 0)
              (K.XIsoOfEq h).hom else 0)) ∧
    (∀ (m : ℕ) {K L : ringedSiteComplex O} (f : K ⟶ L)
      (q : ℤ) (I P : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates m K q).inv ≫ (((ringedNegativeKoszulTensor O ρ a) m).map f).f q ≫
        (coordinates m L q).hom ≫ biproduct.π _ P =
      if h : I = P then f.f (q + I.card) ≫
        (L.XIsoOfEq (congrArg (fun V : Finset (Fin r) ↦ q + (V.card : ℤ)) h)).hom
      else 0) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
      (I L : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates (m + 1) K q).inv ≫ ((step m).app K).f q ≫
        (coordinates m K q).hom ≫ biproduct.π _ L =
      if h : I = L then ringedKoszulCoefficientSMul O ρ (∏ i ∈ I, a i)
        (K.XIsoOfEq (congrArg (fun V : Finset (Fin r) ↦ q + (V.card : ℤ)) h)).hom
      else 0) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
      (I : Finset (Fin r)),
    ((inclusion m).app K).f q ≫ (coordinates m K q).hom ≫ biproduct.π _ I =
      if h : q = q + (I.card : ℤ) then (K.XIsoOfEq h).hom else 0) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I : Finset (Fin r)),
      biproduct.ι _ I ≫ (coordinates m K q).inv =
        ringedNegativeKoszulSummand O ρ a m K q I) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O),
      (inclusion (m + 1)).app K ≫ (step m).app K = (inclusion m).app K) ∧
    (∀ (m : ℕ) {K L : ringedSiteComplex O} (f : K ⟶ L),
      QuasiIso f → QuasiIso ((ringedNegativeKoszulTensor O ρ a m).map f)) := by
  sorry

end CategoryTheory
