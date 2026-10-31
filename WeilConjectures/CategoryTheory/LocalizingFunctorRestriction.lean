/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Restricting exact functors to localizing closures

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-proper-image-localizing/sk-prop-proper-image-localizing-principle.md
and its proof (blueprint: det-proper-image-localizing-principle).

The coproduct indexing universe is independent of both categories' object and
morphism universes. The restriction is Mathlib's canonical full-subcategory lift,
with its induced shift comparison and triangulations.
-/

@[expose] public section

set_option autoImplicit false

universe w u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The inclusion and restriction clauses of the localizing principle, with the
inherited triangulations. The functor in the last two fields maps objects and
morphisms by `F`; its shift comparison is the one induced from `F` by `lift`.

Source: latest blueprint, sec-six-functors-basics/sk-prop-proper-image-localizing,
principle statement and proof, final paragraph
(blueprint: det-proper-image-localizing-principle). -/
structure LocalizingFunctorRestrictionOfSize
    (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D) [F.CommShift ℤ] : Prop where
  [sourceTriangulated : (localizingClosureOfSize.{w} S).IsTriangulated]
  [targetTriangulated : (localizingClosureOfSize.{w} T).IsTriangulated]
  maps : ∀ K : C, localizingClosureOfSize.{w} S K →
    localizingClosureOfSize.{w} T (F.obj K)
  exact : ((localizingClosureOfSize.{w} T).lift
    ((localizingClosureOfSize.{w} S).ι ⋙ F) (fun K ↦ maps K.obj K.property)).IsTriangulated
  sums : ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
    ((localizingClosureOfSize.{w} T).lift
      ((localizingClosureOfSize.{w} S).ι ⋙ F) (fun K ↦ maps K.obj K.property))

/-- Intersection closure, as in Step 1 of the localizing principle. -/
private theorem closure_isLocalizing
    {E : Type u₁} [Category.{v₁} E]
    [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (G : ObjectProperty E) :
    IsLocalizingSubcategoryOfSize.{w} (localizingClosureOfSize.{w} G) := by
  let L := localizingClosureOfSize.{w} G
  have hi : L.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX P hP hGP
    have := hP.2.1
    exact P.prop_of_iso e (hX P hP hGP)⟩
  have hz : L.ContainsZero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := E)
    refine ⟨Z, hZ, ?_⟩
    intro P hP hGP
    have := hP.1
    have := hP.2.1
    exact P.prop_of_isZero hZ
  have hs : L.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX P hP hGP
    have := hP.1
    exact P.le_shift n X (hX P hP hGP)⟩⟩
  have ht : L.IsTriangulatedClosed₂ := .mk' (by
    intro A hA h₁ h₃ P hP hGP
    have := hP.1
    have := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ A hA (h₁ P hP hGP) (h₃ P hP hGP))
  refine ⟨⟨⟩, hi, ?_⟩
  intro I A hA h
  dsimp only
  intro P hP hGP
  exact hP.2.2 A hA (fun i ↦ h i P hP hGP)

/-- An exact functor preserving small sums and mapping generators into the target
localizing closure restricts to an exact functor preserving small sums.

Source: latest blueprint, sec-six-functors-basics/sk-prop-proper-image-localizing,
principle statement and its proof
(blueprint: det-proper-image-localizing-principle).

Proof plan:
1. Both defining intersections contain their generators, are replete, contain zero,
   and are closed under integer shifts, distinguished triangles and ambient sums
   (`def-weil-triangulated-subcategory`). Thus they have induced triangulations.
2. In the source closure take the objects whose images lie in the target closure.
   The generator hypothesis puts the generators in this property. Exactness gives
   zero and shift closure, including negative shifts; functoriality gives repleteness.
   Images of distinguished triangles are distinguished, so the property is triangulated
   (`def-weil-triangulated-category`, `def-weil-triangulated-subcategory`).
3. Preservation of coproducts makes this property sum closed, including empty sums.
   Minimality of the defining intersection gives the asserted inclusion. The comparison
   is the canonical colimit comparison (`def-weil-pbc-category-colimit`).
4. Apply `lem-weil-pbc-triangulated-functor-restriction`, namely Mathlib's
   `ObjectProperty.isTriangulated_lift`, to get exactness with the inherited shifts.
5. Fullness identifies the restricted Hom sets with the ambient Hom sets, so the
   ambient coproduct universal properties give coproducts in both full subcategories
   and prove preservation by the lift (`def-weil-pbc-category-colimit`).
6. For the pro-etale specialization set the source category to the unbounded derived
   category of module objects and the generators to bounded constructible finite-Tor
   complexes (`sk-def-localizing-closure`). Clause 1 of
   `det-def-localizing-closure-existence` supplies its ambient coproducts. The same
   argument applies, with no derived-completeness or cohomological-dimension condition.
-/
theorem localizingFunctorRestrictionOfSize
    [IsTriangulated C] [IsTriangulated D]
    [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (h : ∀ K : C, S K → localizingClosureOfSize.{w} T (F.obj K)) :
    LocalizingFunctorRestrictionOfSize.{w} S T F := by
  have hS := closure_isLocalizing.{w} S
  have hT := closure_isLocalizing.{w} T
  let P := localizingClosureOfSize.{w} S
  let Q := localizingClosureOfSize.{w} T
  let : P.IsTriangulated := hS.1
  let : Q.IsTriangulated := hT.1
  let : P.IsClosedUnderIsomorphisms := hS.2.1
  let : Q.IsClosedUnderIsomorphisms := hT.2.1
  have hpre : IsLocalizingSubcategoryOfSize.{w} (Q.inverseImage F) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I A hA hQA
    let := hA
    exact Q.prop_of_iso (preservesColimitIso F A).symm
      (hT.2.2 (A ⋙ F) inferInstance hQA)
  have hm : ∀ K : C, P K → Q (F.obj K) := by
    intro K hK
    exact hK (Q.inverseImage F) hpre h
  refine ⟨hm, inferInstance, ?_⟩
  intro I
  let : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
      rintro _ ⟨A, hA⟩
      exact hS.2.2 A inferInstance (fun i ↦ hA ⟨i⟩))
  let R := Q.lift (P.ι ⋙ F) (fun K ↦ hm K.obj K.property)
  let : PreservesColimitsOfShape (Discrete I) (R ⋙ Q.ι) :=
    preservesColimitsOfShape_of_natIso (Q.liftCompιIso (P.ι ⋙ F) _).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves R Q.ι

end CategoryTheory
