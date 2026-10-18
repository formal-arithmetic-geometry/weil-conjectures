/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Finite projective dimension of a perfect module
Source: Stacks Project, Algebra, Tags 00O4 and 065R.
(blueprint: lem-weil-pbc-perfect-module-finite-projective-dimension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A module whose degree-zero complex is perfect has finite projective dimension.
Source: Stacks Project, Algebra, Tags 00O4 and 065R.
(blueprint: lem-weil-pbc-perfect-module-finite-projective-dimension)

Proof: Choose a bounded projective complex representing the module, supported in `[a,b]`.
It is K-projective, so its morphisms in the derived category are represented by cochain
maps. A module shifted by `i > max(-a,0)` is supported in degree `-i < a`, so every
cochain map to it is zero. Thus Ext in all degrees greater than `max(-a,0)` vanishes.
The Ext definition of projective dimension gives the asserted finite bound. This also
covers the zero module and models supported in positive degrees. -/
theorem finite_projectiveDimension_of_perfect_single
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] (M : ModuleCat.{u} R)
    (h : DerivedCategory.IsPerfect ((DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ d : ℕ, HasProjectiveDimensionLE M d := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := h
  have := ha
  have := hb
  have (i : ℤ) : Projective (P.X i) := by
    have := (hP i).1
    infer_instance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let := HasExt.standard (ModuleCat.{u} R)
  refine ⟨(-a).toNat, HasProjectiveDimensionLT.mk ?_⟩
  intro i hi Y ξ
  let L := ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj Y)⟦(i : ℤ)⟧
  have hL : L.IsStrictlyLE (-(i : ℤ)) :=
    CochainComplex.isStrictlyLE_shift _ 0 _ _ (by omega)
  have : Subsingleton (P ⟶ L) := by
    constructor
    intro f g
    ext j : 1
    by_cases hj : j < a
    · exact (P.isZero_of_isStrictlyGE a j hj).eq_of_src _ _
    · exact (L.isZero_of_isStrictlyLE (-(i : ℤ)) j (by omega)).eq_of_tgt _ _
  let H := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  have : Subsingleton (H.obj P ⟶ H.obj L) :=
    Function.Surjective.subsingleton H.map_surjective
  have hss : Subsingleton (DerivedCategory.Qh.obj (H.obj P) ⟶
      DerivedCategory.Qh.obj (H.obj L)) :=
    Function.Surjective.subsingleton
      (CochainComplex.IsKProjective.Qh_map_bijective P (H.obj L)).surjective
  dsimp only [H] at hss
  have hssQ : Subsingleton (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) := by
    have : Subsingleton
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh).obj P ⟶
          (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh).obj L) := hss
    exact (Iso.homCongr ((DerivedCategory.quotientCompQhIso _).app P)
      ((DerivedCategory.quotientCompQhIso _).app L)).symm.subsingleton
  apply Abelian.Ext.homEquiv.injective
  have he := Iso.homCongr e
    ((DerivedCategory.Q.commShiftIso (i : ℤ)).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj Y)).symm
  exact he.injective (hssQ.elim _ _)

end ModuleCat
