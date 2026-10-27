/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Algebra.Tower

/-! # The coefficient action on Tor

Source: Stacks Project, Algebra, section Functorialities for Tor, Tag 00M7,
item (1), and section Tor, Tag 00LY.
(blueprint: def-trf-tor-coefficient-module).

## Main definitions

* `ModuleCat.torCoefficientModule`: Mathlib's Tor with its coefficient action.
* `ModuleCat.torCoefficientLinearMap`: the coefficient-induced map on Tor.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
/-- Tor is additive in the coefficient maps.
Source: Stacks Project, Algebra, Tags 00LY and 00M7.
Proof: choose one projective resolution of `M`. Tensoring its terms with a sum of
coefficient maps is the sum of the two chain maps. The homology functor is additive.
Conjugate by the canonical resolution-computation isomorphism for `Tor'`.
This proves additivity in every degree, including zero.
(blueprint: def-trf-tor-coefficient-module). -/
theorem torCoefficientFunctor_additive (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) n).obj M).Additive := by
  constructor
  intro X Y f g
  change (NatTrans.leftDerived
      ((MonoidalCategory.tensoringRight (ModuleCat R)).map (f + g)) n).app M =
    (NatTrans.leftDerived
      ((MonoidalCategory.tensoringRight (ModuleCat R)).map f) n).app M +
    (NatTrans.leftDerived
      ((MonoidalCategory.tensoringRight (ModuleCat R)).map g) n).app M
  simp only [Functor.map_add]
  let P := projectiveResolution M
  rw [P.leftDerived_app_eq _ n, P.leftDerived_app_eq _ n, P.leftDerived_app_eq _ n]
  have h : (NatTrans.mapHomologicalComplex
      ((MonoidalCategory.tensoringRight (ModuleCat R)).map f +
        (MonoidalCategory.tensoringRight (ModuleCat R)).map g)
      (ComplexShape.down ℕ)).app P.complex =
      (NatTrans.mapHomologicalComplex
        ((MonoidalCategory.tensoringRight (ModuleCat R)).map f)
        (ComplexShape.down ℕ)).app P.complex +
      (NatTrans.mapHomologicalComplex
        ((MonoidalCategory.tensoringRight (ModuleCat R)).map g)
        (ComplexShape.down ℕ)).app P.complex := by
    ext i
    rfl
  rw [h, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

attribute [instance] torCoefficientFunctor_additive

/-- The coefficient ring acts through functorial images of multiplication maps.
Source: Stacks Project, Algebra, Tag 00M7, item (1).
(blueprint: def-trf-tor-coefficient-module). -/
noncomputable def torCoefficientAction (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{u} R) (B : Type u) [CommRing B]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (n : ℕ) :
    A →+* End ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).obj
      (((Tor' (ModuleCat.{u} R) n).obj M).obj (ModuleCat.of R B))) :=
  { __ := (Functor.mapEnd (ModuleCat.of R B)
        (((Tor' (ModuleCat.{u} R) n).obj M) ⋙ forget₂ _ AddCommGrpCat)).comp
      (((ModuleCat.endRingEquiv (ModuleCat.of R B)).symm.toRingHom.comp
        (Module.toModuleEnd R B)).toMonoidHom)
    __ := ((((Tor' (ModuleCat.{u} R) n).obj M) ⋙
        forget₂ _ AddCommGrpCat).mapAddHom).comp
      (((ModuleCat.endRingEquiv (ModuleCat.of R B)).symm.toRingHom.comp
        (Module.toModuleEnd R B)).toAddMonoidHom) }

/-- The existing Tor group, with the canonical action of the coefficient algebra.
Its underlying additive group is exactly Mathlib's `Tor'` group, not a replacement.
Source: Stacks Project, Algebra, Tag 00M7, item (1).
(blueprint: def-trf-tor-coefficient-module). -/
noncomputable def torCoefficientModule (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{u} R) (B : Type u) [CommRing B]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.mkOfSMul (torCoefficientAction R A M B n)

/-- The functorial map on Tor respects the coefficient action.
Source: Stacks Project, Algebra, Tag 00M7, item (1).
Proof: multiplication by `a` commutes with an `A`-algebra homomorphism. Applying
`Tor'` preserves this commuting square. Evaluating the square at `t` gives the
claimed equality, since the action was defined by these multiplication maps.
(blueprint: def-trf-tor-coefficient-module). -/
theorem torCoefficientLinearMap_smul (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{u} R) (B C : Type u) [CommRing B] [CommRing C]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (n : ℕ) (f : B →ₐ[A] C) (a : A) (t : torCoefficientModule R A M B n) :
    (((Tor' (ModuleCat.{u} R) n).obj M).map
      (ModuleCat.ofHom (f.restrictScalars R).toLinearMap)).hom (a • t) =
      a • @id (torCoefficientModule R A M C n)
        ((((Tor' (ModuleCat.{u} R) n).obj M).map
          (ModuleCat.ofHom (f.restrictScalars R).toLinearMap)).hom t) := by
  let F := (Tor' (ModuleCat.{u} R) n).obj M
  let mB : ModuleCat.of R B ⟶ ModuleCat.of R B :=
    ModuleCat.ofHom (Module.toModuleEnd R B a)
  let mC : ModuleCat.of R C ⟶ ModuleCat.of R C :=
    ModuleCat.ofHom (Module.toModuleEnd R C a)
  let fR : ModuleCat.of R B ⟶ ModuleCat.of R C :=
    ModuleCat.ofHom (f.restrictScalars R).toLinearMap
  have h : mB ≫ fR = fR ≫ mC := by
    ext b
    exact f.toLinearMap.map_smul a b
  change (F.map fR).hom ((F.map mB).hom t) =
    (F.map mC).hom ((F.map fR).hom t)
  have hf := congrArg (fun k ↦ (F.map k).hom t) h
  simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using hf

/-- The canonical map on coefficient Tor is literally the map of `Tor'` induced
by the algebra homomorphism, equipped with its coefficient linearity.
Source: Stacks Project, Algebra, Tag 00M7, item (1).
(blueprint: def-trf-tor-coefficient-module). -/
noncomputable def torCoefficientLinearMap (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{u} R) (B C : Type u) [CommRing B] [CommRing C]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (n : ℕ) (f : B →ₐ[A] C) :
    torCoefficientModule R A M B n →ₗ[A] torCoefficientModule R A M C n where
  toFun := (((Tor' (ModuleCat.{u} R) n).obj M).map
    (ModuleCat.ofHom (f.restrictScalars R).toLinearMap)).hom
  map_add' := (((Tor' (ModuleCat.{u} R) n).obj M).map
    (ModuleCat.ofHom (f.restrictScalars R).toLinearMap)).hom.map_add
  map_smul' := torCoefficientLinearMap_smul R A M B C n f

end ModuleCat
