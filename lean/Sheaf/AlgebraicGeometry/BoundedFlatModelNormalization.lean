/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift

/-! # Bounded flat model normalization

Source: Stacks Tags 06YS and 06YJ. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Bounded-above flat complex presentations, including their one-fold translates.
Source: Stacks Tag 06YS (blueprint: def-sc-bounded-flat-shift-representative). -/
def boundedFlatShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
    (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) ∧
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X ∨
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦(1 : ℤ)⟧ = X)

/-- Joint translated-unit normalization on bounded-above flat stages only.
Source: steps 1--2 of lem-sc-flat-telescope-model-shift-gauge. Stacks Tags 06YS
and 06YJ supply K-flat computation, not the supplied-tensorator normalization.

Proof. Compute pullback on the bounded-above flat complex itself, which is K-flat.
Use the structure sheaf concentrated in degree zero and its translate for the unit
models. Normalize the degree-zero identification using the supplied monoidal unit.
For each stage rewrite its translate by the first-variable Koszul isomorphism and
translated left unitor. Compose the inverse source rewrite, supplied inverse
pullback tensorator, translated-unit identification tensor the stage comparison,
and target rewrite. The two monoidal unit equations identify the unit normalizations;
associativity identifies repeated rewrites. The maps are invertible and natural
for cochain maps, preserve homotopies, and commute with quasi-isomorphisms between
flat presentations. Transport along the localization comparisons to the indicated
homotopy objects; common flat resolutions identify the transported components.
This gives naturality and the displayed shift equation. This construction does
not take countable sums or transition cones. Zero complexes, arbitrary upper bounds,
and empty schemes require no cancellation of noninvertible maps.
(blueprint: lem-sc-bounded-flat-model-normalization). -/
theorem exists_bounded_flat_model_normalization
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        boundedFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : boundedFlatShiftRepresentative Y X) (hX' : boundedFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
        (hf : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, hb, hf, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, hb, hf, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧' := by sorry

end AlgebraicGeometry
