/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus

/-! # Resolving roofs with an arbitrary ambient target

Source: Stacks Project, Derived Categories, Tags 0794 and 05T7; Categories,
Tags 04VI and 04VJ (blueprint: lem-trf-resolving-roof-ambient-compatibility).
-/

@[expose] public noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- The canonical restriction of localization from bounded above complexes to the
bounded above derived category. Its underlying object and arrow are exactly `Q.obj`
and `Q.map`; the upper bound is used only to certify membership.

Source: Stacks Project, Tag 0794, the bounded above derived category in the first
paragraph (blueprint: lem-trf-resolving-roof-ambient-compatibility). -/
def resolvingRoofQMinus (A : Type u₁) [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w} A] : CochainComplex.Minus A ⥤ DerivedCategory.Minus A where
  obj M := ⟨Q.obj M.obj, ⟨M.property.choose,
    ⟨⟨M.obj, Iso.refl _, M.property.choose_spec⟩⟩⟩⟩
  map f := ObjectProperty.homMk (Q.map f.hom)

/-- A derived isomorphism between bounded above complexes in an epimorphism-generating
class has a common roof in that class, compatible up to homotopy with augmentations
into any complex. Every specified natural comparison on that class respects this roof
and the augmentations after any additive functor preserving its quasi-isomorphisms.

Source: Stacks Project, Tag 0794, the common-roof argument and displayed cohomology
square; Tags 05T7, 04VI and 04VJ
(blueprint: lem-trf-resolving-roof-ambient-compatibility).

Proof plan:
1. By the right calculus of quasi-isomorphisms in the homotopy category
   (lem-pc-quasi-isomorphisms-multiplicative-system), represent `a` by a right fraction
   `T → E`, `T → G` (lem-pc-right-fraction-representation). Both maps are quasi-isomorphisms:
   the first by construction, the second because its localization is invertible.
2. The augmentation equality gives equality of the two maps `T → Y` after localization.
   Common refinement (lem-pc-right-fraction-common-refinement) supplies a quasi-isomorphism
   `U → T` making them equal in the homotopy category, hence chain-homotopic. This uses
   the ambient homotopy category and imposes no bound on `Y`.
3. The cohomology of `U` is bounded above. Apply the resolution clause of
   lem-trf-resolving-class-derived-descent (Stacks 05T7) to obtain `L → U`, with `L`
   bounded above and its terms in `P`. Composition gives quasi-isomorphisms `p,q`.
   Cancel the common denominator to obtain the roof equation and precompose the
   homotopy to obtain the augmentation homotopy.
4. Naturality of the specified `ρ` for `p,q`, and functoriality of `S` applied to the
   roof equation, give the first displayed compatibility after `F`.
5. Apply the additive functor `F` to the homotopy. Localization identifies the resulting
   composites. Substitute the first compatibility and cancel `Q.map (F.map p)`, which
   is invertible by the preservation hypothesis. This gives the second compatibility.
   Only quasi-isomorphisms between bounded above `P`-complexes were inverted after `F`. -/
theorem exists_resolving_roof_ambient_compatibility
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w} B]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (h_sum : ∀ (U V : A), P U → P V → P (U ⊞ V))
    (h_epi : ∀ X : A, ∃ (T : A) (_ : P T) (e : T ⟶ X), Epi e)
    (E G : CochainComplex.Minus A)
    (hE : ∀ j : ℤ, P (E.obj.X j)) (hG : ∀ j : ℤ, P (G.obj.X j))
    (Y : CochainComplex A ℤ) (b : E.obj ⟶ Y) (c : G.obj ⟶ Y)
    (a : Q.obj E.obj ≅ Q.obj G.obj) (ha : a.hom ≫ Q.map c = Q.map b) :
    ∃ (L : CochainComplex.Minus A) (p : L.obj ⟶ E.obj) (q : L.obj ⟶ G.obj),
      (∀ j : ℤ, P (L.obj.X j)) ∧ QuasiIso p ∧ QuasiIso q ∧
      Q.map p ≫ a.hom = Q.map q ∧ Nonempty (Homotopy (q ≫ c) (p ≫ b)) ∧
      ∀ (F : A ⥤ B) [F.Additive],
        (∀ (M N : CochainComplex.Minus A),
          (∀ j : ℤ, P (M.obj.X j)) → (∀ j : ℤ, P (N.obj.X j)) →
          ∀ f : M.obj ⟶ N.obj, QuasiIso f →
            QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)) →
        ∀ (S : DerivedCategory.Minus A ⥤ DerivedCategory B)
          (ρ : ∀ (M : CochainComplex.Minus A) (_ : ∀ j : ℤ, P (M.obj.X j)),
            S.obj ((resolvingRoofQMinus A).obj M) ≅
              Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj M.obj)),
          (∀ (M N : CochainComplex.Minus A)
            (hM : ∀ j : ℤ, P (M.obj.X j)) (hN : ∀ j : ℤ, P (N.obj.X j))
            (f : M.obj ⟶ N.obj),
            S.map ((resolvingRoofQMinus A).map (ObjectProperty.homMk f)) ≫ (ρ N hN).hom =
              (ρ M hM).hom ≫ Q.map ((F.mapHomologicalComplex (.up ℤ)).map f)) →
          (Q.map ((F.mapHomologicalComplex (.up ℤ)).map p) ≫
              (ρ E hE).inv ≫ S.map (ObjectProperty.homMk
                (X := (resolvingRoofQMinus A).obj E)
                (Y := (resolvingRoofQMinus A).obj G) a.hom) ≫ (ρ G hG).hom =
            Q.map ((F.mapHomologicalComplex (.up ℤ)).map q)) ∧
          ((ρ E hE).inv ≫ S.map (ObjectProperty.homMk
                (X := (resolvingRoofQMinus A).obj E)
                (Y := (resolvingRoofQMinus A).obj G) a.hom) ≫ (ρ G hG).hom ≫
              Q.map ((F.mapHomologicalComplex (.up ℤ)).map c) =
            Q.map ((F.mapHomologicalComplex (.up ℤ)).map b)) := by
  sorry

end DerivedCategory
