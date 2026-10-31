/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.CoefficientHeartTriangulated
import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneration

/-! # Triangulation and finite cone generation for field coefficients

Source: blueprint latest, sec-six-functors-basics/sk-cor-coefficient-heart-ii,
`_section.md` and `sk-cor-coefficient-heart-ii.proof.md`
(blueprint: sk-cor-coefficient-heart-ii).

The bounded constructible property and the locally closed extension functor are the
recorded finite constant model and coefficient-heart constructions. Finite generation
is expressed by the same finite sequence of shifted generators and distinguished cones
as in `coefficientHeart_generation`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- For a Noetherian scheme and coefficients E or Qbar_l, the bounded constructible
subcategory is triangulated, and every object is obtained by finitely many cones from
integer shifts of locally closed extensions by zero of lisse modules.

The coefficient disjunction ranges over all finite intermediate extensions in the fixed
algebraic closure `PadicAlgCl ℓ`, as well as the algebraic closure itself. A finite sequence
ends in K; every entry is a shifted lisse extension or a cone between earlier entries,
up to integer shift. Distinguished triangles incorporate isomorphism of cones.

Source: blueprint latest, sec-six-functors-basics/sk-cor-coefficient-heart-ii,
`_section.md` and the two paragraphs of `sk-cor-coefficient-heart-ii.proof.md`
(blueprint: sk-cor-coefficient-heart-ii).

Proof plan:
1. By sk-def-sfb-constructible, Dbc is the full subcategory of bounded objects with
constructible cohomology. Apply det-cor-coefficient-heart-ii-triangulated to X and the
chosen coefficient ring. Its zero, isomorphism, shift and two-out-of-three closure
assertions give the first conclusion in this same ambient derived category.
2. The functor a_! is i_* u_! for the canonical locally closed factorization from
sk-lem-coefficient-heart. Apply det-cor-coefficient-heart-ii-generation to each K in Dbc.
Its generators are precisely these a_! L[n], for all locally closed immersions a, lisse L
and integer n. Its finite sequence ends at K and each later term is a generator or a
shifted cone between earlier terms. Induction on that sequence gives finite cone
construction; shifts are already allowed among generators. No retract or infinite
colimit is used. -/
theorem coefficientHeart_ii (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X] :
    (constantModelBoundedConstructible (coefficientHeartRingObj Λ) X).IsTriangulated ∧
      ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) X)),
        constantModelBoundedConstructible (coefficientHeartRingObj Λ) X K →
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
  constructor
  · rcases hΛ with ⟨E, hE, rfl⟩ | rfl
    · let E' : PadicAlgCl.FiniteIntermediateField ℓ := ⟨E, hE⟩
      exact ((constantModelBoundedConstructible_field_triangulated ℓ X).1 E').2.1
    · exact (constantModelBoundedConstructible_field_triangulated ℓ X).2.2.1
  · intro K hK
    exact (coefficientHeart_generation ℓ Λ hΛ X K).1 hK

end AlgebraicGeometry.ProEtale
