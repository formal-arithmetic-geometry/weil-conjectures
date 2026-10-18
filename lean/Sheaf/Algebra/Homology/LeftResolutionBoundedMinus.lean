/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus

/-!
# Functorial bounded-above resolutions from a zero-preserving left resolution

Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
 sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences
(blueprint: lem-sfb-left-resolution-bounded-minus).
The construction is implemented by the FromJoel `LeftResolution.CochainComplexMinus`
module, using `minusResolutionFunctor` and `minusResolutionNatTrans`
(blueprint: lem-sfb-left-resolution-bounded-minus).

## Main statements

* `CochainComplex.exists_functorial_boundedAbove_left_resolution`: a functor `S` on
  `CochainComplex.Minus A` with a natural quasi-isomorphic augmentation `S ⟶ Minus.ι A`,
  termwise in the essential image of `ι`, preserving every upper bound.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A zero-preserving epimorphic left resolution gives a functorial resolution of
all bounded-above cochain complexes, preserving upper bounds termwise.

Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences;
`WeilConjectures/FromJoel/Algebra/Homology/LeftResolution/CochainComplexMinus.lean:32-273`
(blueprint: lem-sfb-left-resolution-bounded-minus).

Proof:
1. Package `Q`, `π`, and `hπ` as `Λ : CategoryTheory.Abelian.LeftResolution ι`.
2. Use the existing `Λ.minusResolutionFunctor`, apply `ι.mapCochainComplexMinus`,
   and then include in all cochain complexes. Whisker `Λ.minusResolutionNatTrans`
   with the inclusion to obtain the augmentation. The existing quasi-isomorphism
   instance proves its components are quasi-isomorphisms. These constructions already
   implement the objectwise resolution, bounded totalization, additive total transport,
   and single-row identification of the original plan.
3. Every term is definitionally `ι` applied to the corresponding term of the
   `C`-valued resolution, so the essential-image witness uses the identity isomorphism.
4. For any upper bound `b` of `L`, the existing total-support instance gives that
   same upper bound for the `C`-valued total. Termwise application of `ι` preserves
   this strict support. No bound witness enters the functor or its augmentation. -/
theorem exists_functorial_boundedAbove_left_resolution
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {C : Type u₂} [Category.{v₂} C] [Preadditive C]
    [HasZeroObject C] [HasFiniteCoproducts C]
    (ι : C ⥤ A) [ι.Full] [ι.Faithful] [ι.Additive]
    (Q : A ⥤ C) [Q.PreservesZeroMorphisms]
    (π : Q ⋙ ι ⟶ 𝟭 A) (hπ : ∀ (X : A), Epi (π.app X)) :
    ∃ (S : CochainComplex.Minus A ⥤ CochainComplex A ℤ)
      (a : S ⟶ CochainComplex.Minus.ι A),
      (∀ (L : CochainComplex.Minus A), QuasiIso (a.app L)) ∧
      (∀ (L : CochainComplex.Minus A) (i : ℤ),
        ∃ (X : C), Nonempty ((S.obj L).X i ≅ ι.obj X)) ∧
      (∀ (L : CochainComplex.Minus A) (b : ℤ),
        L.obj.IsStrictlyLE b → (S.obj L).IsStrictlyLE b) := by
  let Λ : CategoryTheory.Abelian.LeftResolution ι := ⟨Q, π, hπ⟩
  let S := (Λ.minusResolutionFunctor ⋙ ι.mapCochainComplexMinus) ⋙ Minus.ι A
  let a : S ⟶ Minus.ι A := Functor.whiskerRight Λ.minusResolutionNatTrans (Minus.ι A)
  refine ⟨S, a, ?_, ?_, ?_⟩
  · intro L
    exact inferInstanceAs
      (QuasiIso ((Functor.whiskerRight Λ.minusResolutionNatTrans (Minus.ι A)).app L))
  · intro L i
    exact ⟨((Λ.minusResolutionFunctor.obj L).obj).X i, ⟨Iso.refl _⟩⟩
  · intro L b hL
    have : L.obj.IsStrictlyLE b := hL
    change CochainComplex.IsStrictlyLE ((ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Λ.bicomplexFunctor.obj L.obj).total (ComplexShape.up ℤ))) b
    infer_instance

end CochainComplex
