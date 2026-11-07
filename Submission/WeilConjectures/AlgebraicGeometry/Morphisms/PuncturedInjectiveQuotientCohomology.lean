/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Submission.WeilConjectures.Algebra.Homology.IdealPowerTorsionCocomplexInclusion
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedFlasqueResolutionCohomology
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedSectionsTorsionQuotient

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Computing puncture cohomology by the quotient of an injective resolution

Source: Stacks Project, Tags 0BK0, 0A6T, and 09T2.
-/

@[expose] public section

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The quotient of a module injective resolution by its maximal-ideal-power torsion
subcomplex computes cohomology on the puncture, in every degree.
Source: Stacks Project, Tag 0BK0, Lemma 51.8.2; Tag 0A6T, Lemma 51.2.1;
and Tag 09T2, Lemma 36.8.1.
(blueprint: lem-sbc-punctured-injective-quotient-cohomology).

Proof: The maximal ideal is maximal among prime ideals, so hW identifies W with
Spec R minus V(m). Choose finitely many generators f_i of m. For each injective
module E^k, its associated sheaf is flasque by 09T2, so restriction of its global
sections to W is surjective. Its kernel consists exactly of m-power torsion:
vanishing on each D(f_i) gives f_i^(e_i) x = 0, and every monomial of total degree
sum e_i has some factor f_i^(e_i), so m^(sum e_i) kills x. Conversely m^N x = 0
forces x to vanish in every localization at f_i. These identifications commute
with the resolution differentials, so the restriction complex is the degreewise
quotient E/Gamma_m(E), hence the categorical cokernel of the explicit inclusion.
Sheafification of the resolution is exact, since localization is exact; it resolves
the restricted structure sheaf. Its terms on W are flasque and therefore acyclic
for global sections. The acyclic-resolution comparison identifies the cohomology
of its sections complex with sheaf cohomology, defined as Ext from the constant
integer sheaf. The underlying additive sheaf of the unit structure module is the
additive structure sheaf, giving Modules.H. This works in degree zero as well.
For m=0 the torsion functor is the identity and the puncture is empty: the quotient
complex and all the cohomology groups in question are zero. More generally an
empty puncture has zero restriction complex, so the same argument applies.
The argument uses neither the localization connecting isomorphism nor derived
ideal torsion. -/
theorem nonempty_punctured_h_addEquiv_injective_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) (n : ℕ) :
    Nonempty (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) n ≃+
      ((cokernel (ModuleCat.idealPowerTorsionCocomplexι
        (IsLocalRing.maximalIdeal R) I.cocomplex)).homology n).carrier) := by
  obtain ⟨e⟩ := nonempty_open_h_addEquiv_injective_sections R W I n
  obtain ⟨q⟩ := nonempty_injective_quotient_iso_punctured_sections R W hW I
  let h := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso q
  exact ⟨e.trans h.symm.toLinearEquiv.toAddEquiv⟩

end AlgebraicGeometry.Scheme
