/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Submission.WeilConjectures.RingTheory.Depth
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionSurjective
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionInjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Full faithfulness on the punctured zero section of a power-series open

Source: Stacks Project, Tag 0EY9 (Lemma 58.26.1).
(blueprint: lem-sbc-power-series-punctured-section-fully-faithful)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Restricting finite etale covers to the punctured zero section is fully faithful.
The hypothesis on V says exactly that its intersection with the zero section is
Spec A minus its closed point. Bijectivity on every morphism set expresses full
faithfulness of the actual finite-etale pullback functor, without choosing lifts.

Source: Stacks Project, Tag 0EY9; its proof uses Tags 0BK0, 0EKP and 0EL8.
(blueprint: lem-sbc-power-series-punctured-section-fully-faithful)

Proof: Write B = A[[x_1,...,x_d]], I = (x_1,...,x_d) and U = Spec A minus m.
The zero-section immersion identifies Spec A with Spec(B/I), and its inverse
image of V is U. Depth at least two gives Gamma(U,O_U) = A by local cohomology
(0BK0). Each B/I^n is finite free over A on the monomials of degree less than n,
so Gamma(U,O_U[x]/(x)^n) = A[x]/(x)^n. Taking the inverse limit gives B.
The same calculation computes sections of all infinitesimal neighbourhoods of
the zero section inside V. To check the omitted injectivity detail in 0EY9, let a section on V have
zero formal restriction. At every point of V_0 its germ belongs to all powers
of I in a Noetherian local ring, so Krull intersection makes that germ zero.
Every associated prime q of B is pB for an associated prime p of A: apply the
flat local depth formula to A_p -> B_q; its fibre is a localization of the
domain (A/p)[[x]], so depth zero in the fibre forces q = pB. As depth A is
positive, p is not m. The prime pB + I therefore lies in V_0 and specializes
from q. The section is zero at q, since it is zero at this specialization.
The associated-prime criterion for injectivity of restriction now makes the
section zero on V. Hence Gamma(V,O_V) -> lim Gamma(V_0,O/I^n) is injective.
Its composition with B -> Gamma(V,O_V) is the canonical identification with
B computed above, so both maps are isomorphisms. V is quasi-affine and
Noetherian; apply 0EKP as follows. For any finite locally free module E on V,
global generation on a quasi-affine scheme embeds E into O^r with locally
free cokernel Q; embed Q into O^s in the same way. The resulting sequence
0 -> E -> O^r -> O^s stays exact on every infinitesimal neighbourhood.
Take sections and inverse limits (both left exact). The already established
comparison for O identifies the two kernels, so it gives the comparison for
E. Apply this to the locally free internal Hom of two vector bundles to get
faithfulness of completion on finite locally free modules. For any two finite
etale covers, a morphism on V_0 lifts uniquely to every nilpotent thickening
by formal etaleness. Their finite locally free direct-image algebras therefore
have a unique completed algebra map. Fullness of completion lifts its
underlying module map; faithfulness, applied also to tensor squares and the
unit module, verifies multiplication and the unit. Relative Spec gives the
unique morphism of covers on V. This is the argument of 0EL8, and proves
surjectivity and injectivity on morphism sets. No normality, integrality or
connectedness is assumed. Empty covers are included. The case d = 0 is
excluded here as in 0EY9 (it is the identity restriction separately). -/
theorem finiteEtale_powerSeries_punctured_section_fully_faithful
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    let z := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))
    ∀ P Q : V.toScheme.FiniteEtale,
      Function.Bijective ((FiniteEtale.pullback (z ∣_ V)).map (X := P) (Y := Q)) := by
  dsimp
  intro P Q
  exact ⟨finiteEtale_powerSeries_punctured_section_restriction_injective
      A hdepth d hd V hV P Q,
    finiteEtale_powerSeries_punctured_section_restriction_surjective
      A hdepth d hd V hV P Q⟩

end AlgebraicGeometry.Scheme
