/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Residue cohomology of an affine bounded free representative

Source: Stacks Project, Tags 0BCD, 064K, 06YB and 0098.
(blueprint: lem-sc-affine-free-residue-sections-cohomology)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Residue extension of the section complex computes the derived residue fibre
cohomology by a linear equivalence.
Source: Stacks Project, Tags 0BCD (minimal free models), 064K (bounded free
K-flatness), 06YB (stalkwise K-flatness), 06YI and 06YJ (derived pullback),
and 0098 (stalks of pullback).
(blueprint: lem-sc-affine-free-residue-sections-cohomology)

Proof: The localized-site equivalence transports K to a bounded finite free
complex on U. On an affine scheme, finite free sheaves are the sheaves associated
to their finite free section modules. Evaluation of the given term isomorphisms
therefore gives section modules of ranks r j. Tensor these free modules along
W.evaluation U w hwU; their residue extensions are finite dimensional of the
same ranks, including rank zero. The bounded free complex is K-flat, so its
termwise pullback to the residue-field point represents the derived pullback
of Q(K). The residue point factors through U. Compatibility of derived pullback
with this factorization and exact open restriction identifies this derived
object with the derived fibre of E, using he. On the one-point residue spectrum,
sections are exact, and GammaSpecIso transports scalars to W.residueField w.
The affine module/sheaf tensor comparison identifies these sections termwise
with the explicitly displayed scalar extension of the section complex, and
naturality makes this a chain comparison. Homology thus has a linear equivalence
with derivedFiberCohomology W E j w, as asserted.
No vanishing of any differential or choice of a section frame is used. -/
theorem affineFree_residueSections_cohomologyLinearEquiv
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (r : ℤ → ℕ)
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (r j)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _
      (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    ∀ j : ℤ, Nonempty (derivedFiberCohomology W E j w ≃ₗ[W.residueField w]
      C.homology j) := by
  sorry

end AlgebraicGeometry.Scheme
