/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # A perfect nonnegative flat cohomology model on a specified affine open -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a specified affine base open, an alternating affine Cech model of a proper
relatively flat finitely presented sheaf is bounded, nonnegative and termwise flat,
and represents a perfect object. Its terms need not be finitely presented.
Source: Stacks Project, Tags 01XB, 0A1D and 0B91(2), and the proof of Tag 0A1H.
(blueprint: lem-pc-proper-flat-affine-cech-perfect-model).

Proof: Restrict f and F to U by the standard cartesian square. Quasi-compactness
provides a finite affine cover of f inverse U. Separatedness makes its finite
intersections affine. Form the alternating complex of section modules indexed by
strictly increasing tuples and associate sheaves over U. Negative terms are zero
and terms above the size of the cover are zero. Relative flatness makes every
section module flat over Gamma(U,O); finite sums and associated sheaves preserve
this, and the terms are quasi-coherent. Affine acyclicity (01XB) and Cech comparison
identify the derived object with the restricted derived direct image of F.
Tag 0B91(2), whose approximation proof is Tag 0A1H, makes that object perfect.
For an affine new base the sections on each pulled-back intersection are tensor
products over the base ring. The entire alternating differential base-changes,
so affine acyclicity identifies its homology with the higher direct images after
base change. Restricting to affine opens of an arbitrary new base gives compatible
identifications from the same augmentation, which glue as sheaf isomorphisms.
Equivalently use Tag 0A1D and the bounded flat derived-pullback comparison.
Transport from the standard fibre product to any supplied cartesian square by
its unique isomorphism. No termwise finite-presentation assertion is made for the
Cech section modules. An empty inverse image uses the zero complex with d = 0.
The model is asserted existentially, not defined from an unproved choice. -/
theorem exists_proper_flat_affine_cech_perfect_model
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    ∃ (D : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE d ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      U.toScheme.IsPerfect ((DerivedCategory.Q
        (C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))).obj D) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj D).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by sorry

end AlgebraicGeometry.Scheme.Modules
