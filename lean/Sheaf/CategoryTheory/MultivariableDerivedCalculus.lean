/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.CategoryTheory.Localization.Pi
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Derived-functor calculus in one to four variables

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md,
paragraph on two-variable derived tensor, iterated products, and descending constraints
(blueprint: lem-sfb-multivariable-derived-calculus).

The main theorem supplies product derivability, existence, the universal bijection,
and detection on resolving tuples. The second theorem records all the comparison
laws using Mathlib's canonical `Functor.leftDerivedNatTrans`.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uP vP uD vD uH vH

namespace CategoryTheory

open _root_.CategoryTheory.Functor

variable (n : ℕ) (A : Fin n → Type uA) (P : Fin n → Type uP) (D : Fin n → Type uD)
  [∀ i, Category.{vA} (A i)] [∀ i, Category.{vP} (P i)] [∀ i, Category.{vD} (D i)]
  (I : ∀ i, P i ⥤ A i) [∀ i, (I i).Full] [∀ i, (I i).Faithful]
  (W : ∀ i, MorphismProperty (A i)) (L : ∀ i, A i ⥤ D i)
  [∀ i, (W i).ContainsIdentities] [∀ i, (L i).IsLocalization (W i)]
  {H : Type uH} [Category.{vH} H]

/-- Source: the derived-monoidal proof in the module header, sentences on two-variable
and iterated tensor descent (blueprint: lem-sfb-multivariable-derived-calculus).

Proof plan:
1. Apply `lem-sfb-product-localization` to the ambient and resolving categories,
   with the inverse-image classes on the latter. Use the products of the induced
   localized functors and comparison isomorphisms for the product square.
2. Resolutions assemble coordinatewise. The triple category testing finality is the
   finite product of the coordinate triple categories, since both equations for its
   arrows are coordinatewise. Choose an object in every nonempty factor. To join two
   tuples, concatenate coordinate zigzags, using identities in all other coordinates.
   Finiteness of `Fin n` makes this a finite zigzag. Thus the product triple category
   is nonempty and connected. This proves product left derivability.
3. For the identity inclusion, the identity resolves each object and `(X,id,b)` is
   terminal in each triple category, so it is a left derivability structure.
4. Factor each tuple of weak equivalences into arrows changing one coordinate at a
   time. The coordinate inversion hypothesis then inverts the entire product class.
   Apply `lem-sfb-unary-left-derived-calculus` to obtain the universal bijection,
   its candidate criterion, and invertibility of the counit on resolving tuples.
5. The comparison laws are stated in `multivariableDerivedComparisons` below.
6. Injectivity of the universal bijection gives cancellation against the counit.
7. By `lem-trf-localization-essentially-surjective`, each localized object is
   isomorphic to the image of an ambient object. Resolve that object in each coordinate;
   localization inverts the resolution arrows. Their product gives an isomorphism from
   a resolving tuple to the given tuple. Naturality of both transformations along this
   isomorphism and cancellation of its image show that their components agree there.
   Extensionality then gives equality of transformations.
-/
theorem multivariableDerivedCalculus
    (hn : 1 ≤ n ∧ n ≤ 4)
    (hP : ∀ i,
      (LocalizerMorphism.ofEq (F := I i) (W₂ := W i) rfl).IsLeftDerivabilityStructure)
    (F : (∀ i, A i) ⥤ H)
    (hF : ∀ (i : Fin n) (p q : ∀ j, P j)
      (f : (fun j ↦ (I j).obj (p j)) ⟶ (fun j ↦ (I j).obj (q j)))
      (h : ∀ j, j ≠ i → p j = q j),
      (∀ (j : Fin n) (hj : j ≠ i),
        f j = eqToHom (congrArg (fun x ↦ (I j).obj x) (h j hj))) →
      W i (f i) → IsIso (F.map f)) :
    (Functor.pi L).IsLocalization (MorphismProperty.pi W) ∧
    (LocalizerMorphism.ofEq (F := Functor.pi I)
      (W₂ := MorphismProperty.pi W) rfl).IsLeftDerivabilityStructure ∧
    (∀ i, (LocalizerMorphism.id (W i)).IsLeftDerivabilityStructure) ∧
    (∃ (LF : (∀ i, D i) ⥤ H) (ε : Functor.pi L ⋙ LF ⟶ F),
      (∀ V : (∀ i, D i) ⥤ H,
        Function.Bijective (fun γ : V ⟶ LF ↦ whiskerLeft (Functor.pi L) γ ≫ ε)) ∧
      (∀ p : ∀ i, P i, IsIso (ε.app (fun i ↦ (I i).obj (p i))))) ∧
    (∀ (T : (∀ i, D i) ⥤ H) (η : Functor.pi L ⋙ T ⟶ F),
      (∀ V : (∀ i, D i) ⥤ H,
        Function.Bijective (fun γ : V ⟶ T ↦ whiskerLeft (Functor.pi L) γ ≫ η)) ↔
      ∀ p : ∀ i, P i, IsIso (η.app (fun i ↦ (I i).obj (p i)))) ∧
    (∀ (V V' : (∀ i, D i) ⥤ H) (γ δ : V ⟶ V'),
      (∀ p : ∀ i, P i,
        γ.app (fun i ↦ (L i).obj ((I i).obj (p i))) =
          δ.app (fun i ↦ (L i).obj ((I i).obj (p i)))) → γ = δ) := by
  sorry

/-- Source: the derived-monoidal proof in the module header, sentences on descending
constraints and coherence (blueprint: lem-sfb-multivariable-derived-calculus).

Proof plan: for `τ : F ⟶ G`, apply the universal bijection of `(LG,εG)` with test
functor `LF` to `εF ≫ τ`. Its inverse is Mathlib's `leftDerivedNatTrans`. The
bijection gives its component equation and uniqueness. The identity satisfies the
identity equation; composition satisfies the composite equation. Uniqueness gives
both functoriality laws. Applying them to `τ` and its inverse proves preservation of
isomorphisms. Finally, injectivity of the universal bijection gives cancellation
against `εF`, for every test functor `V`.

The input functors and counits are arbitrary chosen total left derived functors;
the preceding theorem supplies these choices under the coordinate hypotheses.
-/
theorem multivariableDerivedComparisons
    (hn : 1 ≤ n ∧ n ≤ 4)
    (F G K : (∀ i, A i) ⥤ H) (LF LG LK : (∀ i, D i) ⥤ H)
    (εF : Functor.pi L ⋙ LF ⟶ F) (εG : Functor.pi L ⋙ LG ⟶ G)
    (εK : Functor.pi L ⋙ LK ⟶ K)
    [LF.IsLeftDerivedFunctor εF (MorphismProperty.pi W)]
    [LG.IsLeftDerivedFunctor εG (MorphismProperty.pi W)]
    [LK.IsLeftDerivedFunctor εK (MorphismProperty.pi W)] :
    (∀ τ : F ⟶ G,
      (∀ x : ∀ i, A i,
        (Functor.leftDerivedNatTrans LF LG εF εG (MorphismProperty.pi W) τ).app
            ((Functor.pi L).obj x) ≫ εG.app x = εF.app x ≫ τ.app x) ∧
      ∀ m : LF ⟶ LG,
        (∀ x : ∀ i, A i,
          m.app ((Functor.pi L).obj x) ≫ εG.app x = εF.app x ≫ τ.app x) →
        m = Functor.leftDerivedNatTrans LF LG εF εG (MorphismProperty.pi W) τ) ∧
    Functor.leftDerivedNatTrans LF LF εF εF (MorphismProperty.pi W) (𝟙 F) = 𝟙 LF ∧
    (∀ (τ : F ⟶ G) (σ : G ⟶ K),
      Functor.leftDerivedNatTrans LF LK εF εK (MorphismProperty.pi W) (τ ≫ σ) =
        Functor.leftDerivedNatTrans LF LG εF εG (MorphismProperty.pi W) τ ≫
          Functor.leftDerivedNatTrans LG LK εG εK (MorphismProperty.pi W) σ) ∧
    (∀ (τ : F ⟶ G), IsIso τ →
      IsIso (Functor.leftDerivedNatTrans LF LG εF εG (MorphismProperty.pi W) τ)) ∧
    (∀ (V : (∀ i, D i) ⥤ H) (γ₁ γ₂ : V ⟶ LF),
      whiskerLeft (Functor.pi L) γ₁ ≫ εF = whiskerLeft (Functor.pi L) γ₂ ≫ εF →
      γ₁ = γ₂) := by
  sorry

end CategoryTheory
