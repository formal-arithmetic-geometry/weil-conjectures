/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Picard affine structure projective homology

Source: Stacks Project, Tags 0BF2, 0B91, 08EB and 06Z0.
(blueprint: lem-sc-picard-affine-structure-projective-homology).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A representing bounded projective model has the required universal low homology.
Source: Stacks Project, Tags 0B91(2), 06Z0 and the structure-image argument in 0BF2.
(blueprint: lem-sc-picard-affine-structure-projective-homology).

Proof: Exact restriction and the trivialization identify the image represented
by P with R(f_U)_*O. For a ring map R -> B, form Spec B -> Spec R -> U -> S.
Proper relatively flat base change (0B91(2)) identifies the derived pullback of
that image with R(f_B)_*O. The bounds and projective terms make P K-flat, so its
ordinary termwise scalar extension PB computes this derived pullback. A right
derived direct image of a sheaf in degree zero has no negative cohomology and
has zeroth cohomology equal to the ordinary direct image. Apply hO to the map
Spec B -> S: the ordinary tensor-pullback adjunction unit identifies this
ordinary image of O with O on Spec B. The exact affine tilde/Gamma equivalence
(06Z0) identifies these homology sheaves with the tilde of the homology modules
of PB, reflects zero objects, and carries O to the free B-module B. Hence the
negative homology is zero and H0 is isomorphic to B. If B is the zero ring all
modules vanish. The representing isomorphism hrep is essential: the other
conditions on P alone cannot identify its higher cohomology with the image. -/
theorem picard_affine_structure_projective_homology
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
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf))
    (P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ)
    (hb : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)))
    (hp : (∀ n : ℤ, Module.Projective (W.presheaf.obj (.op U)) (P.X n)))
    (hrep : Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P))) :
    (∀ (B : Type v) [CommRing B] (φ : W.presheaf.obj (.op U) →+* B),
        let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
        (∀ i : ℤ, i < 0 → IsZero (PB.homology i)) ∧
          Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) := by sorry

end AlgebraicGeometry.Scheme
