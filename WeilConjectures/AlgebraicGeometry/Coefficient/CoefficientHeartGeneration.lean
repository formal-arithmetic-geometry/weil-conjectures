/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedCohomologyConeWitness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated

/-!
# Finite cone generation of the bounded constructible coefficient category

The witness below is a nonempty finite sequence ending at the specified object. Its
entries are shifted lisse extensions or shifted cones between strictly earlier entries.
Distinguished triangles express cones intrinsically in the ordinary derived category.
No closure under arbitrary coproducts or direct summands enters the statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private def constructionValid {C : Type*} (G : C → Prop) (R : C → C → C → Prop)
    {n : ℕ} (F : Fin n → C) : Prop :=
  ∀ r, G (F r) ∨ ∃ i j, i < r ∧ j < r ∧ R (F i) (F j) (F r)

private def constructionWitness {C : Type*} (G : C → Prop) (R : C → C → C → Prop)
    (K : C) : Prop :=
  ∃ (N : ℕ) (F : Fin (N + 1) → C), F (Fin.last N) = K ∧ constructionValid G R F

private theorem constructionValid_append {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {m n : ℕ} {F : Fin m → C} {H : Fin n → C}
    (hF : constructionValid G R F) (hH : constructionValid G R H) :
    constructionValid G R (Fin.append F H) := by
  intro r
  refine Fin.addCases (fun r ↦ ?_) (fun r ↦ ?_) r
  · rcases hF r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · right
      refine ⟨i.castAdd n, j.castAdd n, ?_, ?_, ?_⟩
      · exact hi
      · exact hj
      · simpa using h
  · rcases hH r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · right
      refine ⟨i.natAdd m, j.natAdd m, ?_, ?_, ?_⟩
      · simpa using hi
      · simpa using hj
      · simpa using h

private theorem constructionWitness_generator {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {K : C} (hK : G K) : constructionWitness G R K := by
  exact ⟨0, fun _ ↦ K, rfl, fun _ ↦ Or.inl hK⟩

private theorem constructionWitness_step {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {A B K : C}
    (hA : constructionWitness G R A) (hB : constructionWitness G R B)
    (hK : R A B K) : constructionWitness G R K := by
  obtain ⟨m, F, hF, hvF⟩ := hA
  obtain ⟨n, H, hH, hvH⟩ := hB
  refine ⟨(m + 1) + (n + 1), Fin.snoc (Fin.append F H) K, by simp, ?_⟩
  intro r
  refine Fin.lastCases ?_ (fun r ↦ ?_) r
  · right
    refine ⟨((Fin.last m).castAdd (n + 1)).castSucc,
      ((Fin.last n).natAdd (m + 1)).castSucc, ?_, ?_, ?_⟩
    · exact Fin.castSucc_lt_last _
    · exact Fin.castSucc_lt_last _
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left,
        Fin.append_right, hF, hH] using hK
  · rcases constructionValid_append hvF hvH r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨i.castSucc, j.castSucc, hi, hj, by simpa using h⟩

private theorem constructionWitness_induction {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {P : C → Prop}
    (hG : ∀ K, G K → P K)
    (hR : ∀ A B K, R A B K → P A → P B → P K)
    {K : C} (hK : constructionWitness G R K) : P K := by
  obtain ⟨N, F, hF, hv⟩ := hK
  have h : ∀ n (hn : n < N + 1), P (F ⟨n, hn⟩) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases hv ⟨n, hn⟩ with h | ⟨i, j, hi, hj, h⟩
      · exact hG _ h
      · exact hR _ _ _ h (ih i.val hi i.isLt) (ih j.val hj j.isLt)
  rw [← hF]
  exact h N (Nat.lt_succ_self N)

private theorem constructionWitness_bind {C : Type*} {G H : C → Prop}
    {R : C → C → C → Prop} {K : C} (hK : constructionWitness G R K)
    (hG : ∀ A, G A → constructionWitness H R A) : constructionWitness H R K := by
  exact constructionWitness_induction hG
    (fun _ _ _ h hA hB ↦ constructionWitness_step hA hB h) hK

private theorem coefficientBounded_triangulated (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X] :
    (constantModelBoundedConstructible (coefficientHeartRingObj Λ) X
      ).IsClosedUnderIsomorphisms ∧
    (constantModelBoundedConstructible (coefficientHeartRingObj Λ) X).IsTriangulated := by
  rcases hΛ with ⟨E, hE, rfl⟩ | rfl
  · let E' : PadicAlgCl.FiniteIntermediateField ℓ := ⟨E, hE⟩
    have h := (constantModelBoundedConstructible_field_triangulated ℓ X).1 E'
    exact ⟨h.1, h.2.1⟩
  · have h := (constantModelBoundedConstructible_field_triangulated ℓ X).2
    exact ⟨h.1, h.2.1⟩

/-- Bounded constructibility over E or Qbar_l is equivalent to the explicit finite cone
construction from shifted locally closed extensions of lisse coefficient modules.
`Fin (N + 1)` lists the objects K_1,...,K_{N+1}; its last entry equals K. A distinguished
triangle with third vertex `(F r)[n]` says that `F r` is a cone up to integer shift and
isomorphism, since distinguished triangles are closed under isomorphism. -/
theorem coefficientHeart_generation (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) X))) :
    constantModelBoundedConstructible (coefficientHeartRingObj Λ) X K ↔
      ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) X))),
        F (Fin.last N) = K ∧ ∀ r : Fin (N + 1),
          (∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
            (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
              (condensedRingObj (coefficientHeartRingObj Λ) S)) (n : ℤ),
            IsLisseCoefficientModule (coefficientHeartRingObj Λ) L ∧
              Nonempty (F r ≅ ((DerivedCategory.singleFunctor _ 0).obj
                ((coefficientHeartLocallyClosedExtension
                  (coefficientHeartRingObj Λ) a ha).obj L))⟦n⟧)) ∨
          (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
            ∃ (n : ℤ) (f : F i ⟶ F j) (g : F j ⟶ (F r)⟦n⟧)
              (h : (F r)⟦n⟧ ⟶ (F i)⟦(1 : ℤ)⟧),
              Pretriangulated.Triangle.mk f g h ∈ distTriang _) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (coefficientHeartRingObj Λ) X)
  let R : DerivedCategory A → DerivedCategory A → DerivedCategory A → Prop :=
    fun U V W ↦ ∃ (n : ℤ) (f : U ⟶ V) (g : V ⟶ W⟦n⟧)
      (h : W⟦n⟧ ⟶ U⟦(1 : ℤ)⟧), Pretriangulated.Triangle.mk f g h ∈ distTriang _
  let G : DerivedCategory A → Prop := fun W ↦
    ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) S)) (n : ℤ),
      IsLisseCoefficientModule (coefficientHeartRingObj Λ) L ∧
        Nonempty (W ≅ ((DerivedCategory.singleFunctor _ 0).obj
          ((coefficientHeartLocallyClosedExtension
            (coefficientHeartRingObj Λ) a ha).obj L))⟦n⟧)
  change constantModelBoundedConstructible (coefficientHeartRingObj Λ) X K ↔
    constructionWitness G R K
  constructor
  · intro hK
    have hw := DerivedCategory.bounded_cohomology_cone_witness A K hK.1
    let H : DerivedCategory A → Prop := fun W ↦ ∃ q n : ℤ,
      Nonempty (W ≅ ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A q).obj K))⟦n⟧)
    have hw' : constructionWitness H R K := hw
    apply constructionWitness_bind hw'
    rintro W ⟨q, n, hW⟩
    exact coefficientHeart_sheaf_cone_witness ℓ Λ hΛ X
      ((DerivedCategory.homologyFunctor A q).obj K) (hK.2 q) n W hW
  · intro hK
    let P := constantModelBoundedConstructible (coefficientHeartRingObj Λ) X
    obtain ⟨hi, ht⟩ := coefficientBounded_triangulated ℓ Λ hΛ X
    have : P.IsClosedUnderIsomorphisms := hi
    have : P.IsTriangulated := ht
    apply constructionWitness_induction (P := P) (K := K) (hK := hK)
    · rintro W ⟨S, a, ha, L, n, hL, ⟨e⟩⟩
      exact P.prop_of_iso e.symm (P.le_shift n _
        (coefficientHeart_lisse_extension_constructible ℓ Λ hΛ X S a ha L hL))
    · intro U V W h hU hV
      obtain ⟨n, f, g, h, hT⟩ := h
      have hW : P (W⟦n⟧) := P.ext_of_isTriangulatedClosed₃
        (Pretriangulated.Triangle.mk f g h) hT hU hV
      exact (ObjectProperty.prop_shift_iff_of_isStableUnderShift P W n).mp hW

end AlgebraicGeometry.ProEtale
