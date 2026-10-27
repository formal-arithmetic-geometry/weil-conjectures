module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.RegularSequenceFlatClosedFiber
import WeilConjectures.RingTheory.OpenFlatLocus

/-!
# A flat principal quotient near a closed-fibre regular element

Source: Stacks Project, More on Morphisms, Tag 056Y, lemma-slice-given-element,
proof, final paragraph, flat quotient part
(blueprint: lem-trf-noetherian-fibre-regular-quotient-neighbourhood).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- A closed-fibre regular singleton gives a flat localized principal quotient and a
principal neighbourhood on which the quotient is flat over the original base.
Source: Stacks Project, More on Morphisms, Tag 056Y, lemma-slice-given-element,
proof, final paragraph, flat quotient part
(blueprint: lem-trf-noetherian-fibre-regular-quotient-neighbourhood).

Proof:
1. Set `p = q.under A`, `R = A_p` and `S = B_q`. By
   lem-weil-pbc-flat-local-ring-maps, `R → S` is flat and local and both rings
   are Noetherian. Its closed fibre is `S/pS`.
2. Apply lem-weil-pbc-grothendieck-regular-sequence-flat to the singleton `[a/1]`.
   Its quotient `Q = S/(a/1)` is flat over `R`.
3. By lem-weil-pbc-flat-over-localization, `Q` is also flat over `A`.
   Put `T = B/(a)` and let `qbar` be the image of `q` in `T`. The canonical
   fraction map identifies `Q` with `T_qbar`, preserving the base action, by
   lem-weil-pbc-localization-at-prime-of-quotient.
4. A finite presentation of `B` over `A` gains one relation to present `T`.
   Apply lem-weil-pbc-openness-of-flatness to `T` as its own finitely presented
   module. By lem-weil-pbc-spec-localization-away-basic-open, choose a basic
   open `D(gamma)` containing `qbar` inside its flat locus. Lift `gamma` to
   `g ∉ q` in `B`.
5. Put `H = T_gamma`. For each prime `P` of `H`, its contraction `r` avoids
   `gamma`. The canonical fraction maps identify `H_P` with `T_r`, as
   `A`-algebras, by lem-weil-pbc-ring-localization-universal-property.
6. Every `H_P` is therefore flat over `A`, and hence over the corresponding
   localization of `A`, by lem-weil-pbc-flat-over-localization. Apply
   lem-weil-pbc-flat-map-local-criterion to conclude that `H` is flat over `A`.
7. By lem-weil-pbc-localization-quotient-commute, the canonical fraction map
   identifies `H` with `B_g/(a/1)`, preserving the `A`-action. This gives the
   required neighbourhood quotient and the two local flatness assertions.
-/
theorem flat_quotient_neighbourhood_of_closedFiber_regular
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.FinitePresentation A B]
    (hflat : (algebraMap A B).Flat) (q : Ideal B) [q.IsPrime]
    (a : B) (ha : a ∈ q)
    (hreg : RingTheory.Sequence.IsRegular
      (Localization.AtPrime q ⧸ (q.under A).map (algebraMap A (Localization.AtPrime q)))
      [Ideal.Quotient.mk ((q.under A).map (algebraMap A (Localization.AtPrime q)))
        (algebraMap B (Localization.AtPrime q) a)]) :
    ((Ideal.Quotient.mk
        (Ideal.span {algebraMap B (Localization.AtPrime q) a})).comp
      (Localization.localRingHom (q.under A) q (algebraMap A B) rfl)).Flat ∧
    Module.Flat A
      (Localization.AtPrime q ⧸ Ideal.span {algebraMap B (Localization.AtPrime q) a}) ∧
    ∃ g : B, g ∉ q ∧ Module.Flat A
      (Localization.Away g ⧸ Ideal.span {algebraMap B (Localization.Away g) a}) := by
  sorry

end RingTheory
