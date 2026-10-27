module

public import WeilConjectures.WeilSheaf.LowerShriek

/-! # Native Weil pullback and ordinary direct-image preservation

Source: the current blueprint, sec-six-functors-basics/sk-thm-sf-ctf-stability,
clauses (1) and (3) of sk-thm-sf-ctf-stability-direct-images; native
WeilSheaf/Category.lean and WeilSheaf/LowerStar.lean.
(blueprint: lem-sf-native-weil-pullback-star-preservation).

The ambient categories and operations are those of the native framework. The
last two equalities identify the restrictions on objects and morphisms via the
full-subcategory inclusions. No geometric-coefficient equivalence is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

/-- Termwise pullback and the total right derived ordinary direct image preserve
bounded constructible native Weil complexes. Their restrictions are the existing
`upperStar` and `derivedLowerStar` functors.

Source: current blueprint, sk-thm-sf-ctf-stability-direct-images, clauses (1),(3);
native WeilSheaf/Category.lean: WeilComplex.upperStar, and WeilSheaf/LowerStar.lean:
WeilComplex.objectProperty_rightDerivedLowerStar and WeilComplex.derivedLowerStar.
(blueprint: lem-sf-native-weil-pullback-star-preservation).

Proof:
1. Apply the existing restricted pullback `upperStar f` to the full-subcategory
object `(L, hL)`. Its membership witness proves preservation for the ambient
termwise pullback, since the restricted functor has that ambient object by
construction.
2. Apply the native theorem `objectProperty_rightDerivedLowerStar f`. Its
quasi-separatedness hypothesis follows from the assumed separatedness of f.
3. Both restricted functors are `ObjectProperty.liftFullSubcategory` constructions.
Their composites with the inclusions are definitionally the corresponding
ambient composites, on objects and morphisms. -/
theorem native_pullback_star_preservation
    (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    (∀ L : DerivedCategory (ProEtaleWeilSheaf k₀ l Y),
      objectProperty k₀ l Y L → objectProperty k₀ l X
        ((ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory.obj L)) ∧
    (∀ K : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
      objectProperty k₀ l X K → objectProperty k₀ l Y
        ((ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor.obj K)) ∧
    (upperStar (k₀ := k₀) (l := l) f ⋙ (objectProperty k₀ l X).ι =
      (objectProperty k₀ l Y).ι ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory) ∧
    (derivedLowerStar (k₀ := k₀) (l := l) f ⋙ (objectProperty k₀ l Y).ι =
      (objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor) := by
  refine ⟨?_, objectProperty_rightDerivedLowerStar f, ?_, ?_⟩
  · intro L hL
    exact ((upperStar (k₀ := k₀) (l := l) f).obj ⟨L, hL⟩).property
  · rfl
  · rfl

end AlgebraicGeometry.WeilComplex
