/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatPullback

/-! # Scalar extension of derived fibre cohomology

Source: Stacks Project, Tag 0BDI, base-change paragraph; Tag 06YJ.
(blueprint: lem-sc-derived-fiber-cohomology-base-change).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The cohomology vector space of a derived fibre after pullback is the scalar
extension of the original fibre cohomology. No pseudo-coherence or finiteness is needed.

Source: Stacks Project, Tag 0BDI, base-change paragraph; Tag 06YJ.
(blueprint: lem-sc-derived-fiber-cohomology-base-change).

Proof: Put x = g(y), k = kappa(x), and l = kappa(y). The residue-field square
Spec l -> Y -> X = Spec l -> Spec k -> X commutes, by the residue-field map identity.
Represent E by a K-flat resolution. Pullback preserves K-flatness, so the
recorded derived-pullback counits compute both composites termwise. The ordinary
tensor-pullback composition isomorphism and the residue-field square identify the
fibre over y with the derived extension of the fibre over x along k -> l.
Since k is a field, l is flat over k, so extension of scalars is exact and commutes
with cohomology in every degree, including unbounded complexes. Evaluation on the
one-point spectra and transport of scalars along GammaSpecIso identify this
cohomology comparison with the displayed ModuleCat isomorphism. For the zero or
infinite-dimensional cohomology vector space the same argument applies. -/
theorem derivedFiberCohomology_baseChange_iso (X Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    [∀ y : Y, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (Y.residueField y)).toRingedSpace))]
    (E : schemeDerivedCategory X) (g : Y ⟶ X) (i : ℤ) (y : Y) :
    Nonempty (derivedFiberCohomology Y ((derivedPullback g).obj E) i y ≅
      (ModuleCat.extendScalars (g.residueFieldMap y).hom).obj
        (derivedFiberCohomology X E i (g y))) := by sorry

end AlgebraicGeometry.Scheme
