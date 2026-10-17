/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.ZetaSeries
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel
import Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import Mathlib.RingTheory.KrullDimension.Zero
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility

/-! # Strict localization at a generic point of polynomial affine space

Source: blueprint `thm-sc-affine-torsion-cd`, exceptional generic degree-two case.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- At a point of polynomial affine m-space whose residue transcendence degree is at
least m, the strict localization is the spectrum of a separably closed field.
Source: blueprint `thm-sc-affine-torsion-cd`, proof step 10 (generic degree two).
(blueprint: lem-sc-polynomial-generic-strict-localization-field)

Proof: finite type makes the residue transcendence degree a finite natural number a.
The polynomial ring has dimension m and is smooth and integral over K. Apply the smooth
strict-local field model, with the canonical scalar structures induced by the structural
maps. Its strict-local ring is a regular local domain of dimension m-a. The hypothesis
m<=a makes this zero. A reduced zero-dimensional local ring is a field, so its residue
map is bijective. The residue field is separably closed, and the resulting ring
isomorphism gives the claimed scheme isomorphism. This also covers m=0. -/
theorem polynomial_generic_strictLocalization_field
    (K : Type u) [Field K] [IsAlgClosed K] (m : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin m) K)))
    (hs : (m : Cardinal.{u}) ≤ residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K))))
      (s (IsLocalRing.closedPoint Ω))) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L),
      Nonempty (strictHenselizationScheme s ≅ Spec (.of L)) := by
  sorry

end AlgebraicGeometry.Scheme
