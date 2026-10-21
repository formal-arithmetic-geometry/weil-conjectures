/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison

/-! # Native morphisms of raw cohomology classes

Source: Stacks Project, Tags 03FD and 03Q8; the existing raw Yoneda presheaves.
(blueprint: def-sbc-raw-class-native-morphisms).

These identity functions expose the derived Hom types recorded by the raw presheaves.
They keep those types available without repeatedly unfolding the additive group structures.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Read a module raw class as its existing derived morphism.
Source: Stacks Project, Tags 03FD and 03Q8; `higherDirectImageRawOverFunctor` and
`higherDirectImageRawOverComplex`.

Construction: the raw functor is the represented derived Hom presheaf. Its value at
`A` is definitionally this Hom type. Return the supplied class itself; no morphism,
comparison, coefficient object or choice is introduced. This includes every integer
shift, zero classes and identity geometric arrows.
(blueprint: def-sbc-raw-class-native-morphisms). -/
noncomputable def rawModuleClassMorphism
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale)
    (A : Over W)
    (z : (higherDirectImageRawOverFunctor Λ k G q U).obj (op A)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k)).obj ((freeSheaf Λ S).obj U)) ⟶
      (higherDirectImageRawOverComplex Λ G A)⟦q⟧ := z

/-- The native module view is the supplied class itself.
Source: Stacks Project, Tags 03FD and 03Q8; the raw Yoneda definition.
Proof: the function returns its input, so heterogeneous reflexivity proves the equation.
(blueprint: def-sbc-raw-class-native-morphisms). -/
theorem rawModuleClassMorphism_heq
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale)
    (A : Over W) (z : (higherDirectImageRawOverFunctor Λ k G q U).obj (op A)) :
    HEq (rawModuleClassMorphism Λ k G q U A z) z := by
  rfl

/-- Read an abelian raw class as its existing derived morphism.
Source: Stacks Project, Tags 03FD and 03Q8; `abelianHigherDirectImageRawPresheaf`.

Construction: unfold the represented raw presheaf and the concrete free abelian
represented sheaf. Its value is definitionally the displayed derived Hom group.
Return the supplied element itself. This introduces no new datum and applies in
all natural degrees, including zero, to zero classes and empty test schemes.
(blueprint: def-sbc-raw-class-native-morphisms). -/
noncomputable def rawAbelianClassMorphism
    {Y S : Scheme.{u}} (h : Y ⟶ S)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : S.Etale)
    (x : (abelianHigherDirectImageRawPresheaf h q G).obj (op U)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj
          (RawModuleScalarComparison.freeAbelian S U)) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)⟦(q : ℤ)⟧ := x

end AlgebraicGeometry.Etale
