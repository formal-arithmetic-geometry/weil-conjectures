/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Eventual vanishing of constant-module direct-image germs

Source: Stacks Project, Tag 09Z1, degree zero.
(blueprint: lem-weil-pbc-constant-module-pushforward-germ-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A germ of a constant-module direct image which vanishes at the limit already
vanishes after one transition of the inverse system.

Source: Stacks Project, Tag 09Z1, degree-zero injectivity in the proof; Tag 09YQ,
degree-zero continuity on affine etale test schemes.
(blueprint: lem-weil-pbc-constant-module-pushforward-germ-vanishing).

Proof: Represent the germ on an affine etale neighborhood U of the geometric point
of X. The hypothesis says that its restriction to U times_X Y is zero after shrinking
U; choose an affine etale refinement of that neighborhood. All U times_X D_i are
qcqs, their transition maps are affine, and their limit is U times_X Y. The canonical
pullback of a constant module sheaf is the same constant module sheaf. Degree-zero
continuity (Tag 09YQ, as used in Tag 09Z1) implies that a section which is zero on
U times_X Y is zero at a later stage. For a general cofiltered category, use the
final directed reindexing of Tag 0032; a common refinement supplies an arrow to the
original stage. The canonical transition is restriction of sections: the adjunction
unit, constant-sheaf comparison and direct-image composition in
constantModulePushforwardMap give exactly this restriction. Thus the section zero
equality gives the displayed equality of germs. Coefficients can be forgotten to
abelian groups, since constant sheaves, pullbacks, direct images and their canonical
maps commute with forgetting; zero and equality are reflected by that faithful
functor. This proves the assertion for any module, with no finiteness assumption.
The zero module is immediate; an empty limit still gives eventual zero by the same
qcqs continuity. A singleton system has an invertible transition to its limit. -/
theorem exists_constantModulePushforward_germ_eq_zero
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ X)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiCompact (p i)] [∀ i : I, QuasiSeparated (p i)]
    {Y : Scheme.{u}} (ν : Y ⟶ X)
    (π : (Functor.const I).obj Y ⟶ D) (hπ : ∀ i, π.app i ≫ p i = ν)
    [QuasiCompact ν] [QuasiSeparated ν]
    (hc : IsLimit (Cone.mk Y π))
    (s : X) (i : I)
    (x : ((X.uliftPointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) (p i)).obj
          ((constantSheaf (D.obj i).smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).obj M)))
    (hx : ((X.uliftPointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map
        (constantModulePushforwardMap Λ M (p i) ν (π.app i) (hπ i)) x = 0) :
    ∃ (j : I) (g : j ⟶ i),
      ((X.uliftPointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map
          (constantModulePushforwardMap Λ M (p i) (p j) (D.map g) (hp g)) x = 0 := by
  sorry

end AlgebraicGeometry.Etale
