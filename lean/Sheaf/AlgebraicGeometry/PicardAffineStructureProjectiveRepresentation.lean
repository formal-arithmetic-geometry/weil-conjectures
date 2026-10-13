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

/-! # Picard affine structure projective representation

Source: Stacks Project, Tags 0BF2, 0B91, 08EB and 06Z0.
(blueprint: lem-sc-picard-affine-structure-projective-representation).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A bounded finite-projective model of the restricted trivialized coefficient image.
Source: Stacks Project, Tags 0BF2 (perfect-image paragraph), 0B91(2), 08EB and 06Z0.
(blueprint: lem-sc-picard-affine-structure-projective-representation).

Proof: Write R = Gamma(W,U). Exact open restriction and open base change identify
this image on U with the derived direct image along X times S U -> U of the
pulled-back M in degree zero. The given isomorphism replaces that coefficient
by the structure sheaf. This sheaf is finitely presented and flat over U, since
f is flat; properness and finite presentation persist under base change.
Tag 0B91(2) makes its derived image perfect. Transport to Spec R using isoSpec
and the equivalence of modules on U with modules on its localized open site.
The affine derived quasi-coherent equivalence (06Z0) and perfectness criterion
(08EB) give a bounded finite-projective R-complex P representing this image.
Transport its representing isomorphism back through those exact equivalences;
the termwise transport is precisely affinePerfectSheafification W U hU.
The zero ring and empty affine open use the zero complex. No universal H0
hypothesis is needed, and no terms or differentials are normalized. -/
theorem picard_affine_structure_projective_representation
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    ∃ P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (W.presheaf.obj (.op U)) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (W.presheaf.obj (.op U)) (P.X n)) ∧
      Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P)) := by sorry

end AlgebraicGeometry.Scheme
