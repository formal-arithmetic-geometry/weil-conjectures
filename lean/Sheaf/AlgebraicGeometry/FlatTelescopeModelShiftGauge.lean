/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian


/-! # Local shift gauge on flat telescope models

Source: the supplied-tensorator calculation in steps 1–2 of
lem-sc-normalized-flat-telescope-stage-comparison; Stacks Tags 06YS and 06YJ
for the model constructions, not for the supplied-tensorator assertion.
(blueprint: lem-sc-flat-telescope-model-shift-gauge).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- The supplied-tensorator gauge on concrete models, natural only for stage maps.
No transformation on the entire homotopy category is supplied.

Source: steps 1–2 and the model-ratio clause of step 3 of
lem-sc-flat-telescope-shift-gauge; the agent expansion of the parent's
supplied-tensorator normalization. Stacks Tags 06YS and 06YJ supply the models.

Proof. Represent a telescope by the cone of one minus transition on a sum of
bounded-above flat stages. Represent the unit in degree zero and its translate
in degree minus one. Identify the unshifted unit using the supplied monoidal
unit map. Rewrite translation on each stage by the first-variable Koszul map
followed by the translated left unitor. Apply the inverse supplied tensorator
and the translated unit comparison e. The two monoidal unit identities identify
the degree-zero normalizations, and tensorator associativity identifies repeated
tensor rewrites. Apply the calculation to both summands of the transition cone;
naturality makes it commute with the transition and hence the cone differential.
Take its ratio with the supplied original shift-compatible comparison. Each ratio
is a composite of isomorphisms, with inverse the reverse ratio. These ratios give
the displayed equation. The same calculation commutes with tower maps and their
sum and cone maps. Transport along the homotopy presentation isomorphisms used
in the definition of a stage map. Comparing presentations through common flat
refinements identifies the resulting ratios, so they depend on the indicated
homotopy object rather than its presentation. This gives the stage-map naturality
asserted here. Naturality for arbitrary homotopy morphisms and extension to all
objects are separate arguments. Zero towers and empty schemes satisfy the same
identities, without cancellation of any noninvertible map.
(blueprint: lem-sc-flat-telescope-model-shift-gauge). -/
theorem exists_flat_telescope_model_shift_gauge
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    [(derivedPullback f).CommShift ℤ] [NatTrans.CommShift ε ℤ] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ a : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            (DerivedCategory.Qh ⋙ derivedPullback f).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X)
          (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X'),
          flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (a X' hX').hom =
            (a X hX).hom ≫ (DerivedCategory.Qh ⋙ derivedPullback f).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
          (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        (a (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩).hom ≫
            ((DerivedCategory.Qh ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            ((a X ⟨P, htel, Or.inl rfl⟩).hom)⟦(1 : ℤ)⟧' := by sorry

end AlgebraicGeometry
