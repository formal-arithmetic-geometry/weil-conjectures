/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Bounded flat models for quasi-compact separated cohomology -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite affine alternating complex gives a bounded flat universal cohomology model.
Properness and finite presentation are not needed for this construction.
Source: Stacks Project, Tags 0A1D and 01XK; the construction preceding Tag 0A1H.
(blueprint: lem-pc-proper-flat-cohomology-model-data).
Proof: choose an affine neighbourhood U of t. Quasi-compactness gives a finite affine
cover of its inverse image; separatedness makes all its nonempty finite intersections
affine. In degree n take the finite direct sum of sections of F on increasing
(n+1)-tuples of members of the cover, with signed restriction differential, and associate
sheaves over U. Above the number of cover members there are no such tuples; negative
terms are zero. The affine local flatness criterion makes the section modules flat over
Gamma(U,O), so their associated sheaves are flat and quasi-coherent. On any affine new
base the inverse-image affine cover has section modules obtained by tensoring these
modules with the new base ring. The alternating complex and its differential therefore
base-change termwise. Affine acyclicity and Cech comparison identify its homology with
higher direct images. These identifications are induced by the Cech augmentation and
hence agree on overlaps, giving the assertion for arbitrary new bases. Transport the
standard fibre-product result along the unique isomorphism associated to the given
cartesian square. An empty inverse image uses the zero complex and d=0. -/
theorem exists_proper_flat_cohomology_model_data {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsSeparated f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsQuasicoherent]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ IsAffine U.toScheme ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by sorry

end AlgebraicGeometry.Scheme.Modules
