/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.Algebra.Homology.KFlatPullback

/-! # Left-derived universal property after localization transport

Source: Stacks Project, Tags 06YJ and 05RU.
(blueprint: lem-sc-derived-pullback-across-universes-left-derived).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The transported pullback remains a left derived functor of the concrete tensor
pullback. Source: Stacks Project, Tags 06YJ and 05RU.
(blueprint: lem-sc-derived-pullback-across-universes-left-derived).

Proof: the object and morphism formulas identify P with scheme tensor pullback.
In the standard localization, unfold derivedPullback and take the counit and its
left-derived universal property from exists_derivedPullback. Precompose and
postcompose by the localization equivalences defining derivedPullbackAcrossUniverses.
Use the canonical factorization isomorphisms Qh ⋙ E ≅ Qh_standard for both schemes
and the associators of functor composition to transport the counit to the displayed
source and target. For any competing counit, precompose and postcompose by the inverse
 equivalences, apply the standard left-derived universal property, and transport the
unique resulting natural transformation back. Cancellation of the equivalence unit
and counit proves both factorization and uniqueness. Thus the transported comparison
is left derived without a common localization universe. This applies also to empty
schemes, zero complexes, and identity morphisms. -/
theorem exists_derivedPullbackAcrossUniverses_leftDerived
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y.toRingedSpace),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap f.base X.sheaf Y.sheaf ⟨f.c⟩)
        (TopCat.Sheaf.inverseImageModule f.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap f.base X.sheaf Y.sheaf ⟨f.c⟩)
        (TopCat.Sheaf.inverseImageModule f.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap f.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
    ∃ ε : DerivedCategory.Qh ⋙ derivedPullbackAcrossUniverses f ⟶
        P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh,
      (derivedPullbackAcrossUniverses f).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (ComplexShape.up ℤ)) := by sorry

end AlgebraicGeometry
