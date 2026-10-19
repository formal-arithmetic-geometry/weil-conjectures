/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.LocalCohomology
import Sheaf.Algebra.Homology.LocalCohomologyDerivedTorsion
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedHOneDerivedTorsion

/-! # PuncturedHOneLocalCohomologyComparison

Source: Stacks Project, Tags 0AVY and 0BK0.
-/

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- Comparison from punctured-spectrum cohomology to local cohomology.

Source: Stacks Project, Tag 0BK0, Lemma 51.8.2(2), Tag 0A6T, Lemma 51.2.1,
and Tag 0AVY, Lemma 47.11.1 (the Ext-colimit description).
(blueprint: lem-sbc-depth-three-puncture-h-one-comparison)

Proof: Put X = Spec R and m = the maximal ideal. Any prime containing m is
m, so V(m) consists precisely of the closed point. The hypothesis hW thus
identifies W with X minus V(m). Apply the affine comparison of 0BK0 to the
finite R-module R and its associated structure sheaf. The localization long
exact sequence, together with positive-degree acyclicity of that sheaf on
X, identifies H^1(W, O_W) with H^2_{V(m)}(X, O_X). For the finitely generated
ideal m, the latter is the ideal local cohomology H^2_m(R), computed as the
filtered colimit of Ext^2_R(R/m^n, R), as in Mathlib's localCohomology. The
underlying additive sheaf of the unit structure module is O_W, so the
left group is precisely Modules.H in the conclusion. Transport hzero along
this additive equivalence. If W is empty its positive cohomology is zero,
and the same comparison still applies. No depth hypothesis is used here. -/
theorem punctured_h_one_subsingleton_of_local_cohomology_vanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (hzero : Subsingleton ((localCohomology (IsLocalRing.maximalIdeal R) 2).obj
      ((ModuleCat.of R R : ModuleCat.{u} R))).carrier) :
    Subsingleton (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1) := by
  obtain ⟨e⟩ := ModuleCat.nonempty_localCohomology_iso_derived_torsion
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    (ModuleCat.of R R : ModuleCat.{u} R) 2
  obtain ⟨d⟩ := nonempty_punctured_h_one_addEquiv_derived_torsion R W hW
  refine ⟨fun x y ↦ d.injective ?_⟩
  apply e.toLinearEquiv.symm.injective
  exact hzero.elim _ _

end AlgebraicGeometry.Scheme
