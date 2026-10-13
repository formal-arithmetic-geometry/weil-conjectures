/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Fixed-affine models used in the Picard comparison

Source: Stacks Project, Tag 0BF2.
(blueprint: lem-sc-picard-affine-target-normalization)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- A universally trivial structure H-zero gives a normalized target on the entire affine.
Source: Stacks Project, Tag 0BF2, target complexes; Tags 08CR, 08EB and 0B91.
(blueprint: lem-sc-picard-affine-target-normalization)

Proof: The given trivialization identifies the restricted derived image with that of
O on the base-changed proper flat finitely presented morphism. Perfect direct-image
base change makes it perfect and universally connective. Use the affine derived
sheafification equivalence and the bounded-projective characterization to represent
it by a bounded finite projective complex on the supplied affine, without shrinking.
Cancel negative terms starting at the lowest degree. Each bottom differential is
injective on every residue field by universal connectiveness. The local-ring residue
split-injection criterion makes its finitely presented cokernel locally free; on an
affine this cokernel is finite projective, so the differential splits globally.
For degree zero use the derived structure unit and its universal H-zero isomorphism.
Represent the unit by a chain map. Its degree-zero cycle is unimodular at every prime,
so its quotient is locally free and the unit summand splits off globally. On the
remaining degree-zero summand the outgoing differential is residue-injective at
every prime, hence again has finite projective cokernel. Split and cancel this pair.
Sheafifying the resulting bounded projective complex gives C, with no negative terms
and zero degree-zero differential. All cancellations are homotopy equivalences,
which give the stated derived isomorphism. The empty affine gives the zero complex. -/
theorem picard_affine_target_normalization
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    ∃ C : CochainComplex
        (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ,
      IsStrictlyPerfect W U C ∧ (∀ j : ℤ, j < 0 → IsZero (C.X j)) ∧
      C.d 0 1 = 0 ∧
      Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
          DerivedCategory.Q.obj C) := by sorry

end AlgebraicGeometry.Scheme
