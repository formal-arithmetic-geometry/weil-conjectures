/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Sheaf.RingTheory.TorCoefficientModule
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Coefficient actions in the resolution computation of Tor

Source: Stacks Project, Algebra, Tags 00LY, 00LZ and 00M7, item (1).
(blueprint: lem-trf-tor-resolution-coefficient-actions).

The first statement applies to either coefficient ring in a tower `R → A → B`.
The homology action is explicitly the map induced by `1 ⊗ multiplication by s`.
The second statement identifies the two existing actions on Tor with coefficients in `B`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace ModuleCat

/-- The canonical resolution-computation isomorphism intertwines the coefficient action
with multiplication on the coefficient factor of the tensor complex. In particular it
is linear for that action on homology. The chain endomorphism on the right sends every
finite tensor sum `∑ pᵢ ⊗ sᵢ` to `∑ pᵢ ⊗ s * sᵢ`, so this is also the cycle formula.
Source: Stacks Project, Algebra, Tags 00LY/00LZ and 00M7, item (1).
Proof: a basis lifts maps through surjections, so each free term is projective.
Multiplication by `s` is R-linear. Tensoring it with the identity commutes with the
resolution differentials, since both composites send `p ⊗ x` to `d p ⊗ s * x`.
It therefore preserves cycles and boundaries and induces the displayed map on homology.
The tensor relations give the unit, sum and product identities for these maps.
Apply clause (2) of lem-weil-pbc-tor-map-via-resolution-lift, namely
ProjectiveResolution.leftDerived_app_eq, to this multiplication map. Its Tor map is
precisely the action specified by def-trf-tor-coefficient-module. The comparison is
already additive and R-linear by def-weil-pbc-tor-modules, so the formula gives
coefficient linearity. No exactness after tensoring, and no flatness, is used.
(blueprint: lem-trf-tor-resolution-coefficient-actions). -/
theorem tor_resolution_coefficient_smul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    [∀ j : ℕ, Module.Free R (P.complex.X j)] (n : ℕ)
    (s : S) (t : torCoefficientModule R S M S n) :
    (P.isoLeftDerivedObj (tensorRight (ModuleCat.of R S)) n).hom.hom (s • t) =
      (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((tensoringRight (ModuleCat.{u} R)).map (ofHom (LinearMap.mulLeft R s)))
          (ComplexShape.down ℕ)).app P.complex) n).hom
        ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of R S)) n).hom.hom t) := by
  have h := P.leftDerived_app_eq
    ((tensoringRight (ModuleCat.{u} R)).map (ofHom (LinearMap.mulLeft R s))) n
  have hc :
      (((Tor' (ModuleCat.{u} R) n).obj M).map
        (ofHom (LinearMap.mulLeft R s))) ≫
        (P.isoLeftDerivedObj (tensorRight (ModuleCat.of R S)) n).hom =
      (P.isoLeftDerivedObj (tensorRight (ModuleCat.of R S)) n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex
            ((tensoringRight (ModuleCat.{u} R)).map (ofHom (LinearMap.mulLeft R s)))
            (ComplexShape.down ℕ)).app P.complex) n := by
    rw [Tor'_obj_map, h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  exact ConcreteCategory.congr_hom hc t

/-- The A-action on Tor with coefficients in B is restriction of the B-action, and
multiplication in B satisfies the stated scalar associativity formula.
Source: Stacks Project, Algebra, Tag 00M7, item (1).
Proof: for `a : A`, the endomorphism of B defining the A-action is multiplication by
`algebraMap A B a`. This is the identical R-linear endomorphism defining the B-action
of that element. Applying Tor to identical maps proves the first clause. Applying
functoriality to the composite of multiplication by `b` and by `algebraMap A B a`
(or using B-module associativity) proves the second clause. These are the existing
actions of def-trf-tor-coefficient-module, with no choice of a replacement action.
(blueprint: lem-trf-tor-resolution-coefficient-actions). -/
theorem tor_resolution_coefficient_actions (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (M : ModuleCat.{u} R) (n : ℕ) :
    (∀ (a : A) (t : torCoefficientModule R A M B n),
      a • t = (algebraMap A B a) • @id (torCoefficientModule R B M B n) t) ∧
    (∀ (a : A) (b : B) (t : torCoefficientModule R B M B n),
      (algebraMap A B a * b) • t =
        a • @id (torCoefficientModule R A M B n) (b • t)) := by
  have restrict (a : A) (t : torCoefficientModule R A M B n) :
      a • t = (algebraMap A B a) • @id (torCoefficientModule R B M B n) t := by
    change
      ((((Tor' (ModuleCat.{u} R) n).obj M).map
        (ofHom (Module.toModuleEnd R B a))).hom t) =
      ((((Tor' (ModuleCat.{u} R) n).obj M).map
        (ofHom (Module.toModuleEnd R B (algebraMap A B a)))).hom t)
    have hm : Module.toModuleEnd R B a =
        Module.toModuleEnd R B (algebraMap A B a) := by
      ext b
      exact Algebra.smul_def a b
    rw [hm]
  refine ⟨restrict, ?_⟩
  intro a b t
  rw [restrict]
  exact mul_smul (algebraMap A B a) b t

end ModuleCat
