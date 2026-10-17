/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# Perfectness of the pairing of a trace

Let `a : X ⟶ Y` admit a compactification and `t : (Ra_! Λ_X)[n] ⟶ Λ_Y` be a trace which is a
counit: every morphism `(Ra_! U)[n] ⟶ Λ_Y` is `(Ra_! z)[n] ≫ t` for a unique `z : U ⟶ Λ_X`.
Then the pairing of `t`,
`Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.poincarePairingOfTrace`), is perfect for every `K` at which the
projection formula holds. This is the argument of
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`, for the untwisted
evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X`, which is a counit for every `K`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairingOfTrace`: the pairing of a trace
  which is a counit is perfect.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]

omit [ConcreteCategory A FA] [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint] in
/-- The evaluation part of the pairing of a trace: maps `h : N ⟶ Ra_* K^∨` correspond
bijectively to maps `K ⊗ᴸ La^* N ⟶ Λ_X`, through `K ⊗ᴸ La^* h`, `K ⊗ᴸ` the counit of
`La^* ⊣ Ra_*` and the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X`. -/
theorem bijective_derivedTensor_map_comp_counit_comp_coefficientEvaluation (K : 𝐃(X, A))
    (N : 𝐃(Y, A)) :
    Function.Bijective (fun h : N ⟶ (R((a)_*[A])).obj
        ((DerivedCategory.coefficientDual A X).obj (op K)) ↦
      ((derivedTensor A X).obj K).map ((L((a)^*[A])).map h) ≫
        ((derivedTensor A X).obj K).map ((derivedUpperStarLowerStarAdjunction A a).counit.app _) ≫
          DerivedCategory.coefficientEvaluation K) := by
  have e : (fun h : N ⟶ (R((a)_*[A])).obj
        ((DerivedCategory.coefficientDual A X).obj (op K)) ↦
      ((derivedTensor A X).obj K).map ((L((a)^*[A])).map h) ≫
        ((derivedTensor A X).obj K).map ((derivedUpperStarLowerStarAdjunction A a).counit.app _) ≫
          DerivedCategory.coefficientEvaluation K) =
      ((derivedTensorHomAdjunction A K).homEquiv _ _).symm ∘
        ((derivedUpperStarLowerStarAdjunction A a).homEquiv _ _).symm := by
    funext h
    simp [Adjunction.homEquiv_counit, DerivedCategory.coefficientEvaluation]
    rfl
  rw [e]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

set_option maxRecDepth 4000 in
omit [HasSmallSiteSheafify A] [(R(a)_![A]).IsLeftAdjoint] in
/-- **The pairing of a trace which is a counit is perfect.** Let `t : Ra_!(Λ_X[n]) ⟶ Λ_Y` be
such that every morphism `Ra_!(U[n]) ⟶ Λ_Y` is `Ra_!(z[n]) ≫ t` for a unique `z : U ⟶ Λ_X`, and
let `K` satisfy the projection formula against every object. Then the pairing
`Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ⟶ Λ_Y` of the trace `(Ra_! Λ_X)[n] ≅ Ra_!(Λ_X[n]) ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.poincarePairingOfTrace`) is perfect. -/
theorem isPerfectPairing_poincarePairingOfTrace (K : 𝐃(X, A)) (n : ℤ)
    (t : (R(a)_![A]).obj ((𝟙_ _)⟦n⟧) ⟶ 𝟙_ _)
    (ht : ∀ U : 𝐃(X, A), Function.Bijective (fun z : U ⟶ 𝟙_ _ ↦ (R(a)_![A]).map (z⟦n⟧') ≫ t))
    (hPF : ∀ N, HasProjectionFormula A a K N) :
    IsPerfectPairing (poincarePairingOfTrace a K n
      (((R(a)_![A]).commShiftIso n).inv.app _ ≫ t)) := by
  constructor
  rw [poincarePairingOfTrace, mixedSupportCupProduct, Category.assoc]
  refine MonoidalClosed.isIso_curry_of_projection _ _ _ _ _ _ _ _ _ (fun _ ↦ True)
    (fun _ _ u hu ↦ isIso_of_bijective_comp_shift n u fun N ↦ hu N trivial) (fun N _ ↦ hPF N)
    ?_ ?_
  · exact bijective_derivedTensor_map_comp_counit_comp_coefficientEvaluation A a K
  · exact ht

section Untwisting

omit [ConcreteCategory A FA] [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint] in
/-- Tensoring with an object `L` which has a two-sided tensor inverse is bijective on
morphisms: `f ↦ f ⊗ᴸ L` is a bijection `(P ⟶ Q) ≃ (P ⊗ᴸ L ⟶ Q ⊗ᴸ L)`. -/
lemma bijective_derivedTensor_map_app {L L'' : 𝐃(Y, A)}
    (e : ((derivedTensor A Y).obj L).obj L'' ≅ 𝟙_ _)
    (e' : ((derivedTensor A Y).obj L'').obj L ≅ 𝟙_ _) (P Q : 𝐃(Y, A)) :
    Function.Bijective (fun f : P ⟶ Q ↦ ((derivedTensor A Y).map f).app L) :=
  (tensorRightEquivalenceOfTensorIso e e').fullyFaithfulFunctor.map_bijective P Q

omit [ConcreteCategory A FA] [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint] in
/-- **Untwisting a pairing.** Let `L` have a two-sided tensor inverse, `c : Λ_Y ≅ L' ⊗ᴸ L`, and
`tw : M ⊗ᴸ L' ⟶ Λ_Y`. Its untwisting is the morphism `M ⟶ L`
```
   ρ⁻¹        M ⊗ c             α⁻¹                tw ⊗ L        λ
M ──▶ M ⊗ᴸ Λ_Y ──▶ M ⊗ᴸ (L' ⊗ᴸ L) ──▶ (M ⊗ᴸ L') ⊗ᴸ L ──▶ Λ_Y ⊗ᴸ L ──▶ L.
```
For every `V`, the morphisms `m ≫ untwist` for `m : V ⟶ M` correspond bijectively to the
morphisms `(m ⊗ᴸ L') ≫ tw`. -/
lemma exists_bijective_comp_untwist {M L L' L'' V : 𝐃(Y, A)}
    (e : ((derivedTensor A Y).obj L).obj L'' ≅ 𝟙_ _)
    (e' : ((derivedTensor A Y).obj L'').obj L ≅ 𝟙_ _)
    (c : 𝟙_ 𝐃(Y, A) ≅ ((derivedTensor A Y).obj L').obj L)
    (tw : ((derivedTensor A Y).obj M).obj L' ⟶ 𝟙_ _) :
    ∃ Ψ : (((derivedTensor A Y).obj V).obj L' ⟶ 𝟙_ _) → (V ⟶ L), Function.Bijective Ψ ∧
      ∀ m : V ⟶ M, m ≫ (derivedTensorRightUnitor A Y M).inv ≫
        ((derivedTensor A Y).obj M).map c.hom ≫ (derivedTensorAssociator A Y M L' L).inv ≫
          ((derivedTensor A Y).map tw).app L ≫ (derivedTensorLeftUnitor A Y L).hom =
        Ψ (((derivedTensor A Y).map m).app L' ≫ tw) := by
  let i : V ≅ ((derivedTensor A Y).obj (((derivedTensor A Y).obj V).obj L')).obj L :=
    (ρ_ V).symm ≪≫ whiskerLeftIso V c ≪≫ (α_ V L' L).symm
  refine ⟨fun f ↦ i.hom ≫ ((derivedTensor A Y).map f).app L ≫ (λ_ L).hom, ?_, fun m ↦ ?_⟩
  · have := (Iso.homCongr i.symm (λ_ L)).bijective.comp
      (bijective_derivedTensor_map_app A e e' (((derivedTensor A Y).obj V).obj L') (𝟙_ _))
    convert this using 1
    funext f
    simp [Iso.homCongr_apply]
  · change m ≫ (ρ_ M).inv ≫ M ◁ c.hom ≫ (α_ M L' L).inv ≫ tw ▷ L ≫ (λ_ L).hom =
      ((ρ_ V).inv ≫ V ◁ c.hom ≫ (α_ V L' L).inv) ≫ (m ▷ L' ≫ tw) ▷ L ≫ (λ_ L).hom
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
    erw [associator_inv_naturality_left_assoc]
    rw [comp_whiskerRight]
    simp only [Category.assoc]

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] [(R(a)_![A]).IsLeftAdjoint] in
/-- **The twisted trace is a counit.** Let `T` have a two-sided tensor inverse,
`e : La^* N ≅ T`, and `s : Ra_!(T[n]) ⟶ Λ_Y` a counit: every `Ra_!(U[n]) ⟶ Λ_Y` is
`Ra_!(w[n]) ≫ s` for a unique `w : U ⟶ T`. Let `p_K : Ra_! K ⊗ᴸ N ⟶ Ra_!(K ⊗ᴸ La^* N)` be
natural isomorphisms (the projection maps). Then every morphism `(Ra_! U)[n] ⊗ᴸ N ⟶ Λ_Y` is
`((Ra_! z)[n] ⊗ᴸ N) ≫ tw` for a unique `z : U ⟶ Λ_X`, where `tw` is the twisted trace
```
                          ≅                        p
(Ra_! Λ_X)[n] ⊗ᴸ N ───▶ (Ra_! Λ_X ⊗ᴸ N)[n] ───▶ (Ra_!(Λ_X ⊗ᴸ La^* N))[n]
         Ra_!(Λ_X ⊗ e)[n]       Ra_!(λ)[n]               ≅              s
     ───────────────▶ ─────────────▶ (Ra_! T)[n] ─────▶ Ra_!(T[n]) ─────▶ Λ_Y.
``` -/
lemma bijective_derivedTensor_map_comp_twistedTrace (n : ℤ) {N : 𝐃(Y, A)} {T T' : 𝐃(X, A)}
    (eT : ((derivedTensor A X).obj T).obj T' ≅ 𝟙_ _)
    (eT' : ((derivedTensor A X).obj T').obj T ≅ 𝟙_ _) (e : (L((a)^*[A])).obj N ≅ T)
    (s : (R(a)_![A]).obj (T⟦n⟧) ⟶ 𝟙_ _)
    (hs : ∀ U : 𝐃(X, A), Function.Bijective (fun w : U ⟶ T ↦ (R(a)_![A]).map (w⟦n⟧') ≫ s))
    (p : ∀ K : 𝐃(X, A), ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj N ⟶
      (R(a)_![A]).obj (((derivedTensor A X).obj K).obj ((L((a)^*[A])).obj N)))
    (hp : ∀ {K K' : 𝐃(X, A)} (z : K ⟶ K'), ((derivedTensor A Y).map ((R(a)_![A]).map z)).app N ≫
      p K' = p K ≫ (R(a)_![A]).map (((derivedTensor A X).map z).app ((L((a)^*[A])).obj N)))
    (hpi : ∀ K, IsIso (p K)) (U : 𝐃(X, A)) :
    Function.Bijective (fun z : U ⟶ 𝟙_ _ ↦
      ((derivedTensor A Y).map (((R(a)_![A]).map z)⟦n⟧')).app N ≫
        (((derivedTensor A Y).flip.obj N).commShiftIso n).hom.app _ ≫
          (p (𝟙_ _))⟦n⟧' ≫
            ((R(a)_![A]).map (((derivedTensor A X).obj _).map e.hom ≫
              (derivedTensorLeftUnitor A X T).hom))⟦n⟧' ≫
              ((R(a)_![A]).commShiftIso n).inv.app T ≫ s) := by
  let F := R(a)_![A]
  let P := ((derivedTensor A X).obj U).obj ((L((a)^*[A])).obj N)
  let κ : ((derivedTensor A Y).obj ((F.obj U)⟦n⟧)).obj N ⟶ F.obj (P⟦n⟧) :=
    (((derivedTensor A Y).flip.obj N).commShiftIso n).hom.app _ ≫ (p U)⟦n⟧' ≫
      (F.commShiftIso n).inv.app P
  have := hpi U
  have : IsIso κ := by dsimp [κ]; infer_instance
  let j : P ≅ ((derivedTensor A X).obj U).obj T := ((derivedTensor A X).obj U).mapIso e
  let w : (U ⟶ 𝟙_ _) → (P ⟶ T) := fun z ↦
    j.hom ≫ ((derivedTensor A X).map z).app T ≫ (derivedTensorLeftUnitor A X T).hom
  have hw : Function.Bijective w := by
    have := (Iso.homCongr j.symm (derivedTensorLeftUnitor A X T)).bijective.comp
      (bijective_derivedTensor_map_app A eT eT' U (𝟙_ _))
    convert this using 1
    funext f
    simp [Iso.homCongr_apply, w]
  have hcomp : (fun z : U ⟶ 𝟙_ _ ↦
      ((derivedTensor A Y).map ((F.map z)⟦n⟧')).app N ≫
        (((derivedTensor A Y).flip.obj N).commShiftIso n).hom.app _ ≫
          (p (𝟙_ _))⟦n⟧' ≫
            (F.map (((derivedTensor A X).obj _).map e.hom ≫
              (derivedTensorLeftUnitor A X T).hom))⟦n⟧' ≫
              (F.commShiftIso n).inv.app T ≫ s) =
      (fun g ↦ κ ≫ g) ∘ (fun v ↦ F.map (v⟦n⟧') ≫ s) ∘ w := by
    funext z
    have h₁ : ((derivedTensor A Y).map ((F.map z)⟦n⟧')).app N ≫
        (((derivedTensor A Y).flip.obj N).commShiftIso n).hom.app (F.obj (𝟙_ _)) =
        (((derivedTensor A Y).flip.obj N).commShiftIso n).hom.app (F.obj U) ≫
          (((derivedTensor A Y).map (F.map z)).app N)⟦n⟧' :=
      ((derivedTensor A Y).flip.obj N).commShiftIso_hom_naturality (F.map z) n
    have h₃ : (F.commShiftIso n).inv.app P ≫ F.map ((w z)⟦n⟧') =
        (F.map (w z))⟦n⟧' ≫ (F.commShiftIso n).inv.app T :=
      ((F.commShiftIso n).inv.naturality (w z)).symm
    have h₄ : ((derivedTensor A X).map z).app ((L((a)^*[A])).obj N) ≫
        ((derivedTensor A X).obj (𝟙_ _)).map e.hom ≫ (derivedTensorLeftUnitor A X T).hom =
        w z := by
      simp only [w, j, Functor.mapIso_hom]
      exact (reassoc_of% (whisker_exchange z e.hom).symm) _
    have inner : ((derivedTensor A Y).map (F.map z)).app N ≫ p (𝟙_ _) ≫
          F.map (((derivedTensor A X).obj _).map e.hom ≫ (derivedTensorLeftUnitor A X T).hom) =
        p U ≫ F.map (w z) := by
      rw [reassoc_of% (hp z), ← F.map_comp, h₄]
    simp only [Function.comp_apply, κ, Category.assoc]
    rw [reassoc_of% h₃, reassoc_of% h₁, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc, inner, Functor.map_comp_assoc]
  rw [hcomp]
  exact ((isIso_iff_coyoneda_map_bijective κ).1 inferInstance _).comp ((hs _).comp hw)

end Untwisting

end Etale

end AlgebraicGeometry
