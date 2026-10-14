/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Normalized comparison on the K-flat resolving class

Source: Stacks Project, Tag 06YJ, representative computation, and the
supplied-tensorator normalization in the parent node, step 2 (agent expansion).
(blueprint: lem-sc-normalized-kflat-representative-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Homotopy objects which are K-flat representatives or their translates by one.
This predicate records actual representatives and contains no choice of data.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-normalized-kflat-representative-comparison). -/
def kFlatShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
    CochainComplex.IsKFlat (R := Y.sheaf) P ∧
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X ∨
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦(1 : ℤ)⟧ = X)

/-- A jointly normalized comparison on K-flat homotopy representatives and their
one-fold translates. Naturality is required only between objects of this class;
there is no natural transformation on the entire homotopy category here.

Source: Stacks Project, Tag 06YJ, K-flat computation; the tensorator coherence
part is the agent expansion of step 2 of the parent node, not an assertion of 06YJ.

Proof. Use the degree-zero structure-sheaf complex and its translate as the two
unit representatives. Termwise pullback identifies their images with the units
over Z. Compare the unshifted representative using the supplied monoidal unit
map. On a K-flat P, the first-variable Koszul comparison followed by the shifted
left unitor identifies O_Y[1] tensor P with P[1]. Define the comparison on this
translated tensor representative by applying the supplied inverse tensorator,
the comparison on the shifted unit, and the comparison on P, followed by the
corresponding Koszul comparison over Z. The shifted-unit comparison e and these
representative comparisons are constructed together. Associativity of the
supplied tensorator identifies the two rewrites of a translated tensor product;
the left and right unit equations identify the rewrites with a unit factor.
Consequently these formulas agree on overlapping representative descriptions,
and their translation equation is the displayed square. The termwise Koszul
maps, unitors, tensorator, and representative maps are natural, giving naturality
for every homotopy morphism between resolving objects. Inverting a replacement
quasi-isomorphism preserves these equations, so each object of the indicated
class has a well-defined comparison independent of its representative. Each
factor is an isomorphism on a K-flat representative, so the components are
isomorphisms. This constructs only the comparison on the resolving class;
extension to arbitrary homotopy objects is a separate right-fraction argument.
For zero complexes all maps are the unique zero-object maps. The identity
morphism is normalized using the same tensorator, and e is never arbitrary.
(blueprint: lem-sc-normalized-kflat-representative-comparison). -/
theorem exists_normalized_kFlat_representative_comparison
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        kFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : kFlatShiftRepresentative Y X) (hX' : kFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsKFlat (R := Y.sheaf) P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, hP, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, hP, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧' := by sorry

end AlgebraicGeometry
