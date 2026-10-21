/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.Homotopy

/-!
# Cofinal subsequence comparison of strict Roos complexes

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok;
More on Algebra, Tag 0H9K, lemma-pro-isomorphism-iso-Rlim, explicit product maps.
The strict cochain refinement is the nine-step agent proof of
(blueprint: lem-fix-cofinal-roos-restriction).

Positive indices are encoded by their predecessors. Thus an order embedding `φ`
represents the positive-index function `n + 1 ↦ φ n + 1`. The two product maps
are real constructions; the theorem specifies one family of cone maps by both
coordinates, so its existential quantifier leaves no choice of cone completion.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CofinalRoos

/-- Restriction of complexes of strict towers along an increasing subsequence.
Source: Stacks Tag 0H9K, indices `m_n`
(blueprint: lem-fix-cofinal-roos-restriction). -/
abbrev restriction (A : Type u) [Category.{v} A] [Abelian A] (φ : ℕ ↪o ℕ) :=
  ((Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ A).obj φ.monotone.functor.op).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Coordinate selection `a_φ` on the source product of `1-s`.
Source: Stacks Tag 0H9K, map φ′ with identity component maps
(blueprint: lem-fix-cofinal-roos-restriction). -/
noncomputable def selection {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ : ℕ ↪o ℕ) :
    roosP X ⟶ roosP ((restriction A φ).obj X) :=
  Pi.lift (fun n ↦ Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (φ n))

/-- Finite-block summation `b_φ`: the summand `k` has original index `φ n + k`.
Source: Stacks Tag 0H9K, map φ″ with identity component maps
(blueprint: lem-fix-cofinal-roos-restriction). -/
noncomputable def block {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ : ℕ ↪o ℕ) :
    roosP X ⟶ roosP ((restriction A φ).obj X) :=
  Pi.lift (fun n ↦ ∑ k ∈ Finset.range (φ (n + 1) - φ n),
    Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (φ n + k) ≫
      X.asFunctor.map (homOfLE (Nat.le_add_right (φ n) k)).op)

/-- The specified cofinal Roos maps are quasi-isomorphisms, natural and strictly
compatible with composition, identity, and all strict augmentations.

Source: Stacks Tag 0941, Roos realization, and Tag 0H9K, product maps and finite-block
elimination (blueprint: lem-fix-cofinal-roos-restriction).

Proof, following the node's nine steps:
1. Products are degreewise. Projections and finite sums of transition chain maps
   define `selection` and `block`. In `roosχ` coordinates the differential is
   `(y,z) ↦ (-dy-(1-s)z,dz)` (def-weil-strict-roos-model).
2. Telescoping the block sum gives `roosU X ≫ block = selection ≫ roosU X'`.
   The induced shifted-cone map has diagonal coordinates `(block,selection)`.
3. Put m_n=φ(n), ν(i)=min{n : i≤m_n}. Define E by transition from m_ν(i)
   and J by extension by zero away from selected indices. Then aE=bJ=1 and
   δE=Jδ', giving a strict right inverse S(y,z)=(Jy,Ez).
4. The finite sum h(y)_i=Σ_{j=i}^{m_ν(i)-1} t_{i,j}y_j satisfies
   hδ=1-Ea and δh=1-Jb, including the initial block before m_0.
5. The degree-minus-one map K(y,z)=(0,-hy) satisfies DK+KD=1-SC.
6. Homotopy.homologyMap_eq (lem-weil-pbc-homotopic-maps-equal-cohomology)
   and CS=1 imply that every cohomology map of C is invertible, hence QuasiIso C
   (def-weil-abstract-derived-category). Exact countable products are retained.
7. A strict tower map commutes with every transition. Both selection and block
   therefore commute with its product map, proving strict naturality.
8. Nested finite blocks partition the single composite block; the tower law
   collapses their transitions. Selection composes too. Identity blocks have one
   term. This proves composition and identity before localization. HEq records
   only the equality transport of the reindexed complexes.
9. The augmentation roosAugment γ hγ has coordinates (0,γ). Applying (b,a)
   gives precisely (0,γ_φ(n)). All displayed equalities survive localization,
   which takes these quasi-isomorphisms to isomorphisms. -/
theorem cofinalRoosRestriction
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasCountableProducts (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)] :
    ∃ ρ : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
        (φ : ℕ ↪o ℕ), roosF.obj X ⟶ roosF.obj ((restriction _ φ).obj X),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
          (φ : ℕ ↪o ℕ) (_hunbounded : ∀ i : ℕ, ∃ n : ℕ, i ≤ φ n),
        roosU X ≫ block X φ = selection X φ ≫ roosU ((restriction _ φ).obj X) ∧
        QuasiIso (ρ X φ) ∧
        (∀ p : ℤ,
          (ρ X φ).f (p + 1) ≫ (roosχ ((restriction _ φ).obj X) p).hom =
            (roosχ X p).hom ≫
              biprod.map ((block X φ).f p) ((selection X φ).f (p + 1))) ∧
        (∀ (Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (f : X ⟶ Y),
          roosF.map f ≫ ρ Y φ = ρ X φ ≫ roosF.map ((restriction _ φ).map f)) ∧
        (∀ (ψ : ℕ ↪o ℕ) (_hψ : ∀ i : ℕ, ∃ n : ℕ, i ≤ ψ n),
          HEq (ρ X φ ≫ ρ ((restriction _ φ).obj X) ψ) (ρ X (ψ.trans φ))) ∧
        (∀ (P : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ)
            (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
            (hγ : ∀ n : ℕ,
              γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n),
          ∀ p : ℤ,
            (roosAugment γ hγ ≫ ρ X φ).f (p + 1) ≫
                (roosχ ((restriction _ φ).obj X) p).hom =
              biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ γ (φ n))).f (p + 1)))) ∧
      (∀ X, HEq (ρ X (RelEmbedding.refl (α := ℕ) (· ≤ ·))) (𝟙 (roosF.obj X))) := by
  sorry

end CategoryTheory.CofinalRoos
