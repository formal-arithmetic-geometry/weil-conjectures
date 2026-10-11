/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# The right adjoint of proper flat derived direct image preserves direct sums

Source: Stacks Project, Duality for Schemes, Lemma 48.12.1, Section Tag 0E4H
(blueprint: lem-sc-proper-flat-right-adjoint-direct-sums).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The right adjoint of proper, flat, finitely presented derived direct image commutes
with every set-indexed direct sum. The natural isomorphism `hF` identifies `F` with the
restriction of the shared ambient `schemeDerivedDirectImage f` to quasi-coherent objects.
Source: Stacks Project, Duality for Schemes, Lemma 48.12.1, Section Tag 0E4H
(blueprint: lem-sc-proper-flat-right-adjoint-direct-sums).

Proof:
1. Properness over qcqs Y makes X qcqs. For every perfect P on X, apply
   `lem-pc-proper-support-perfect-direct-image` with E = P and G = O_X in degree zero.
   O_X is finitely presented and flat over Y, with proper support X, so Rf_*P is perfect.
   By `lem-pc-perfect-object-compact` on Y, Hom(Rf_*P, -) commutes with direct sums.
2. For a family K_i on Y, let v be the canonical map from the sum of a(K_i) to
   a of the sum of K_i. Adjunction identifies Hom(P, a(-)) with Hom(Rf_*P, -).
   Compactness of P (`lem-pc-perfect-object-compact` on X) and Step 1 show that
   Hom(P, v) is an isomorphism for every perfect P.
3. The cone C of v has Hom(P[n], C) = 0 for every perfect P and integer n, by the
   long exact Hom sequence. The objects A with Hom(A[n], C) = 0 for all n form a class
   closed under shifts, cones, retracts and arbitrary sums and containing the perfects.
   By `lem-pc-derived-qcoh-perfect-generation`, this class contains every object,
   in particular C. Thus its identity is zero, C is zero, and v is an isomorphism. -/
theorem proper_flat_rightAdjoint_preservesDirectSums
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : F ⊣ a) :
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I) a := by
  sorry

end AlgebraicGeometry
