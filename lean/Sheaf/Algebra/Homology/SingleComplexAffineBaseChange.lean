/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.SingleComplexQcqsInduction

/-! # The affine single-complex base-change criterion

The public affine statement is obtained by specializing the closed qcqs induction
criterion to the four maps between affine spectra. The original coordinate proof
is retained as singleComplexAffineBaseChangeCore in the lower homology module;
it supplies the affine case used by the open-source induction without creating an
import cycle.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks, Tag 0DJ8, affine proof (and the affine case of Tag 0DJ9).
The public root is the affine specialization of the qcqs induction theorem. -/
theorem singleComplexAffineBaseChange
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (K' : schemeDerivedCategory (Spec (.of A')))
    (hK' : schemeDerivedQCohProperty (Spec (.of A')) K')
    (φ : (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition (Spec.map (CommRingCat.ofHom φf))
      (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
      (Spec.map (CommRingCat.ofHom φg')) sq K K' φ) :
    IsIso (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K ≫
      (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).map φ) := by
  exact singleComplexBaseChangeQcqsInduction
    (Spec.map (CommRingCat.ofHom φf))
    (Spec.map (CommRingCat.ofHom φf'))
    (Spec.map (CommRingCat.ofHom φg))
    (Spec.map (CommRingCat.ofHom φg'))
    sq K hK K' hK' φ h_stalk

end AlgebraicGeometry
