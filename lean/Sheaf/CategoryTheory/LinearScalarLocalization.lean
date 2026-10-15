/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Category laws for raw scalar localization

Source: the Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi` (blueprint: lem-weil-linear-scalar-localization-category).
The scalar-first tensor order is the convention of `LinearMap.baseChange`.
`ULift.{0} C` is only a wrapper for the unchanged objects, with no new objects adjoined.
-/

@[expose] public section

universe r u v

open CategoryTheory TensorProduct

namespace CategoryTheory

/-- The raw tensor-Hom localization is a linear category, with a linear localization functor
and induced strict automorphisms.
Source: the Weil conjectures blueprint, `def-weil-rationalization-karoubi`
(blueprint: lem-weil-linear-scalar-localization-category).

Proof plan:
1. Extend the bilinear composition of the original category by the unique bilinear extension
of module base change (Stacks 00CV, 00CX, 05G4).
2. Every tensor is a finite sum of pure tensors. On three pure tensors associativity is the
associativity of the original composition and of scalar multiplication; extend by additivity.
The original identities tensored with one give the two identity laws in the same way.
3. The maps `f ↦ 1 ⊗ f` are R-linear, preserve identities by construction, and preserve
composition because `1 * 1 = 1`. They therefore define the linear functor Q.
4. Base change the linear Hom maps of T. These preserve composition and identities on pure
tensors, hence on finite sums, and give an A-linear functor T'.
5. The strict inverse S of T is linear: apply the bijective Hom maps of T to the additivity
and scalar equations for S. Its base change gives S'. The inverse equations hold on objects
and on pure tensors and therefore on all morphisms. The two composites with Q agree on
objects and on `1 ⊗ f`, giving the strict commuting square.

The linear Hom equivalences below give tensor coordinates for the morphisms. The category
instance supplies associativity and both identity laws. Instance-binding lambdas merely
scope the existential category and linear structures; they introduce no extra hypotheses. -/
theorem exists_linear_scalarLocalization_category
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) :
    (∀ K L M : C,
      ∃! β : (Localization.Away p ⊗[R] (L ⟶ M)) →ₗ[Localization.Away p]
          (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
          (Localization.Away p ⊗[R] (K ⟶ M)),
        ∀ (f : L ⟶ M) (g : K ⟶ L) (a b : Localization.Away p),
          β (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f)) ∧
    ∃ d : Category.{max r v} (ULift.{0} C),
      (fun [catInst : Category.{max r v} (ULift.{0} C)] ↦
        ∃ a : Preadditive (ULift.{0} C), (fun [addInst : Preadditive (ULift.{0} C)] ↦
          ∃ l : Linear (Localization.Away p) (ULift.{0} C),
            (fun [linInst : Linear (Localization.Away p) (ULift.{0} C)] ↦
              ∃ e : ∀ K L : C, (Localization.Away p ⊗[R] (K ⟶ L))
                  ≃ₗ[Localization.Away p] (ULift.up K ⟶ ULift.up L),
                (∀ K : C, e K K (1 ⊗ₜ[R] 𝟙 K) = 𝟙 (ULift.up K)) ∧
                (∀ (K L M : C) (f : L ⟶ M) (g : K ⟶ L)
                    (a b : Localization.Away p),
                  e K L (b ⊗ₜ[R] g) ≫ e L M (a ⊗ₜ[R] f) =
                    e K M ((a * b) ⊗ₜ[R] (g ≫ f))) ∧
                ∃ lr : Linear R (ULift.{0} C), (fun [rlinInst : Linear R (ULift.{0} C)] ↦
                  (∀ (K L : ULift.{0} C) (r : R) (f : K ⟶ L),
                    r • f = (algebraMap R (Localization.Away p) r) • f) ∧
                  ∃ Q : C ⥤ ULift.{0} C,
                    (∀ K : C, Q.obj K = ULift.up K) ∧
                    (∀ (K L : C) (f : K ⟶ L), HEq (Q.map f) (e K L (1 ⊗ₜ[R] f))) ∧
                    Q.Additive ∧ Q.Linear R ∧
                    ∀ (T S : C ⥤ C) [T.Additive] [T.Linear R],
                      T ⋙ S = 𝟭 C → S ⋙ T = 𝟭 C →
                      ∃ T' S' : ULift.{0} C ⥤ ULift.{0} C,
                        T'.Additive ∧ T'.Linear (Localization.Away p) ∧
                        S'.Additive ∧ S'.Linear (Localization.Away p) ∧
                        (∀ K : C, T'.obj (ULift.up K) = ULift.up (T.obj K)) ∧
                        (∀ K : C, S'.obj (ULift.up K) = ULift.up (S.obj K)) ∧
                        (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
                          HEq (T'.map (e K L (a ⊗ₜ[R] f)))
                            (e (T.obj K) (T.obj L) (a ⊗ₜ[R] T.map f))) ∧
                        (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
                          HEq (S'.map (e K L (a ⊗ₜ[R] f)))
                            (e (S.obj K) (S.obj L) (a ⊗ₜ[R] S.map f))) ∧
                        T' ⋙ S' = 𝟭 (ULift.{0} C) ∧ S' ⋙ T' = 𝟭 (ULift.{0} C) ∧
                        T ⋙ Q = Q ⋙ T'
                ) (rlinInst := lr)
            ) (linInst := l)) (addInst := a)) (catInst := d) := by
  sorry

end CategoryTheory
