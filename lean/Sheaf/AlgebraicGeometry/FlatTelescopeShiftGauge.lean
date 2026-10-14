/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian


/-! # Shift gauge on flat telescope models

Source: the supplied-tensorator calculation in steps 1–2 of
lem-sc-normalized-flat-telescope-stage-comparison; Stacks Tags 06YS and 06YJ
for the model constructions, not for the supplied-tensorator assertion.
(blueprint: lem-sc-flat-telescope-shift-gauge).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Normalize the source shift comparison, without asserting a comparison to the
termwise pullback functor or invertibility of any counit component.

Source: parent lem-sc-normalized-flat-telescope-stage-comparison, steps 1–2;
Stacks Tags 06YS and 06YJ for flat models. The gauge calculation is the parent's
agent expansion, rather than an assertion of those tags.

Proof. Use bounded-above flat resolutions and the cone of one minus transition
on their countable sum. Compute the canonical shift on these models by translation
of complexes. Represent the unit in degree zero and its translate in degree minus
one. Normalize the unit comparison by the supplied monoidal unit map. On a stage,
rewrite translation as tensor with the translated unit by the first-variable
Koszul map followed by the translated left unitor. Use the supplied inverse
tensorator to compare this rewrite with its counterpart after pullback. The two
unit equations identify the degree-zero unit normalizations; associativity
identifies the rewrites on iterated tensors. Apply these equations to both cone
summands: they commute with the sum inclusions and the transition, hence with
the cone differential. Their ratio with the original representative comparison
is invertible and natural in the model. The right Kan universal property of the
supplied counit descends the ratio to an automorphism of its source functor;
the reverse ratio gives its inverse by Kan uniqueness. At a telescope, composing
this ratio with the original translated comparison gives exactly the displayed
shift gauge equation. Only this equation on telescopes is retained here.
The zero tower gives zero maps, so needs no cancellation of a scalar; on an empty
scheme the same identities hold in the zero category. This statement supplies no
chosen data for a definition.
(blueprint: lem-sc-flat-telescope-shift-gauge). -/
theorem exists_flat_telescope_shift_gauge
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
      ∃ a : (DerivedCategory.Qh ⋙ derivedPullback f) ≅
          (DerivedCategory.Qh ⋙ derivedPullback f),
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
          (_ : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        a.hom.app (X⟦(1 : ℤ)⟧) ≫
            ((DerivedCategory.Qh ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (a.hom.app X)⟦(1 : ℤ)⟧' := by sorry

end AlgebraicGeometry
