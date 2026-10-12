/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-!
# Cohomology of affine derived direct image

Source: Stacks Project, Derived Categories of Schemes, Tag 0AVW,
Lemma 36.5.4, proof (blueprint: lem-sc-affine-derived-cohomology).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For an affine morphism, the cohomology sheaves of the unbounded derived direct image
of an object with quasi-coherent cohomology are the ordinary direct images of its
cohomology sheaves, and these direct images are quasi-coherent.
Source: Stacks Project, Tag 0AVW, Lemma 36.5.4, proof
(blueprint: lem-sc-affine-derived-cohomology).

Proof:
1. Affine higher-direct-image vanishing (`lem-pc-affine-morphism-hi`) gives
   R^p f_* F = 0 for p > 0 for every quasi-coherent module F. Apply
   `lem-sc-qcoh-acyclic-derived-pushforward-cohomology` to obtain the cohomology
   comparison for every integer i, using the derived direct image of
   `def-pc-derived-direct-image`. For unbounded objects this uses Stacks Tag 08D4
   on sections over inverse images of affine opens (the small detail of Tag 0AVW);
   one cannot simply push forward an arbitrary representative termwise.
2. By `lem-pc-affine-morphism-hi`, ordinary direct image along an affine morphism
   preserves quasi-coherence. Apply this to H^i(E), which is quasi-coherent by
   the assumption that E belongs to D_QCoh(X). -/
theorem schemeHigherDirectImage_of_affine
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsAffineHom f]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) (i : ℤ) :
    Nonempty ((schemeHigherDirectImage f i).obj E ≅
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) ∧
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)).IsQuasicoherent := by
  sorry

end AlgebraicGeometry
