/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleCompletionPointSystem
public import WeilConjectures.Mathlib.RingTheory.Henselian


/-! # Strict-local congruences at one admissible blowup

Source: ILO, Travaux de Gabber, XX 2.4.4 proof, p.365 and XX 4.4 final Note,
p.374; Stacks Project, Tag 05WS
(blueprint: lem-per-admissible-completion-strict-local-congruence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical comparison at a single compatible geometric point is bijective
modulo the extended power of I. The map here is the actual component of the specified
strict-local comparison, and the base map is the actual stage structural map.

Source: ILO XX 2.4.4 proof, p.365; XX 4.4 final Note, p.374; Stacks, Tag 05WS
(blueprint: lem-per-admissible-completion-strict-local-congruence).

Proof: apply admissibleCompletion_fiber_iso to the ideal at J and the power n. The
closed-point condition S.closed places both compatible geometric points on these
infinitesimal fibres: I^n lies in I for n ≥ 1, and the completed structural square
places the second point on the completed fibre. Pass to the ordinary local rings
at these points. The maps to the local rings of the fibres are the surjective
quotients by the extended I^n, whose kernels are in the respective maximal ideals.
Identify the geometric strict local rings with the pointed-etale algebraic colimits
by etale_local_ring_triples and etaleResidueTriples_localized_isStrictHenselization.
The surjective-quotient theorem identifies their quotients by I^n with the strict
henselizations of the fibre local rings. Use the fibre isomorphism and the same
separable residue closure inside Ω to identify those pointed colimits. Their
universal property and pointed functoriality identify this isomorphism with the
map induced by pointedStrictLocalRingMap. Finally transport along S.rings_obj,
S.completedRings_obj, S.base_app and S.comparison_app. This proves bijectivity
of the displayed quotientMap itself, including its stated extension ideal. The
argument works equally for n = 1 and for a zero ideal; the existence of the
geometric point excludes the zero local ring. -/
theorem admissibleCompletion_strictLocal_congruence
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I] (hI : I.FG)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (S : AdmissibleCompletionPointSystem I Ω) (J : AdmissibleBlowupIndex I)
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective
      (Ideal.quotientMap (((I ^ n).map (S.base.app J).hom).map (S.comparison.app J).hom)
        (S.comparison.app J).hom Ideal.le_comap_map) := by sorry

end AlgebraicGeometry
