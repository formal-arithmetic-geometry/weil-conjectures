/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.Topology.OpenModuleCohomology

import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.Topology.RestrictInjectiveResolution
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective

/-! # Quasi-coherent vanishing over inverse images of affine opens

Source: Stacks Project, Tags 08D4 (3), 08D5 and 01F4 (2).
(blueprint: new-qcoh-inverse-affine-open-vanishing).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Positive module cohomology vanishes on inverse images of affine opens
when higher direct image vanishes on quasi-coherent modules.
Source: Stacks Project, Tags 08D5, 01F4 (2), 01XJ and 01XB.
(blueprint: new-qcoh-inverse-affine-open-vanishing).

Proof:
1. Put U = f inverse-image V. The restriction F|U is quasi-coherent.
Restriction of an injective resolution remains injective, so the cohomology
in the conclusion computes H^p(U,F|U).
2. Open restriction commutes with derived direct image, including on F[0].
The bounded-below/unbounded derived comparison and the single-object
homology comparison identify H^q(Rf_*(F[0])) with the ordinary R^q f_*F
for q in the natural numbers. Exact open restriction commutes with homology,
so hacyc makes the ordinary R^q(f|V)_*(F|U) zero for q > 0. All higher direct images
are quasi-coherent since f|V is quasi-compact and quasi-separated, by the
quasi-coherence clause of finite-support-hi, without using its support bound.
3. Since V is affine, affine vanishing kills positive cohomology of each
of these quasi-coherent higher direct images. The canonical Leray edge
is consequently an isomorphism. In degree p > 0 its target is sections
of the zero higher direct image from step 2. The source, and hence the
stated open module cohomology, is zero. The empty affine open gives the
zero sections complex, so is included without an extra hypothesis. -/
theorem qcoh_acyclic_inverse_affine_open_vanishing {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (V : Y.Opens) (hV : IsAffineOpen V)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : F.IsQuasicoherent) (p : ℕ) (hp : 0 < p) :
    IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace p (f ⁻¹ᵁ V)).obj F) := by sorry

end AlgebraicGeometry
