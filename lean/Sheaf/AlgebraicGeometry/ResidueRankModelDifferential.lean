/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Residue vanishing of the differential in a Betti-rank model

Source: Stacks Project, Tag 0BCD, minimal free model; Tag 0BF2, first source complex.
(blueprint: lem-sc-residue-rank-model-differential)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Every degree-zero differential coordinate of a bounded Betti-rank model has zero residue.
Source: Stacks Project, Tag 0BCD and Tag 0BF2, first displayed source complex.
(blueprint: lem-sc-residue-rank-model-differential)

Proof: Restrict E to U using the given derived comparison with Q(K). The bounded
finite free complex K is K-flat. Pull it termwise to Spec kappa(w) and evaluate
its sections, using the canonical factorization of the residue point through U.
Exact open restriction, pullback composition and GammaSpecIso identify this
complex's cohomology with derivedFiberCohomology W E j w. Its term in degree j
has dimension derivedFiberBetti W E j w by the given free isomorphism. All terms
and all cohomology vector spaces are finite dimensional. In each degree, the
term dimension equals the cohomology dimension plus the ranks of the incoming
and outgoing differentials. Equality with the Betti number forces both ranks
zero. In particular the outgoing differential in degree zero is the zero map.
The linear frame e1 becomes an invertible frame over kappa(w) by base change.
For any section t, the coordinates of d(t) reduce to the coordinates of the
zero residue vector. The coefficient map is exactly W.evaluation U w hwU.
This also covers rank-zero degree-one terms, and uses no negative vanishing,
rank-one degree-zero hypothesis, geometry of a direct image, or choice of e0. -/
theorem residueRankModel_differential_eval_eq_zero
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (hfin : ∀ j : ℤ, Module.Finite (W.residueField w) (derivedFiberCohomology W E j w))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W E j w)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K))
    (m : ℕ)
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (t : (K.X 0).val.obj (.op (Over.mk (𝟙 U)))) :
    ∀ i, W.evaluation U w hwU
      (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) t) i) = 0 := by sorry

end AlgebraicGeometry.Scheme
