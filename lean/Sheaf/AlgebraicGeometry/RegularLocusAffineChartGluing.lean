module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Comparison and gluing of regular loci on affine charts

Source: Stacks Project, Morphisms, Tag 07R4 (lemma-J), proof, second and final paragraphs;
Schemes, Tag 01HV (lemma-spec-sheaves), parts (1) and (6)
(blueprint: lem-trf-regular-locus-affine-chart-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AlgebraicGeometry

/-- On each affine chart the regular locus is the inverse image of the ring regular locus.
Its openness is equivalent to openness of the ring loci on any affine open cover. On
`Spec B` the scheme and ring loci are equal subsets of `PrimeSpectrum B`, so their
openness is equivalent. Empty schemes and arbitrarily indexed covers are included.

Source: Stacks Project, Morphisms, Tag 07R4 (lemma-J), proof, second and final paragraphs;
Schemes, Tag 01HV (lemma-spec-sheaves), parts (1) and (6)
(blueprint: lem-trf-regular-locus-affine-chart-gluing).

Proof:
1. For an affine open `W` and `z : W`, the canonical chart sends `z` to
   `W.2.primeIdealOf z`. Its inverse is `W.2.fromSpec`, by `fromSpec_primeIdealOf`.
   The affine-stalk localization theorem `lem-weil-pbc-affine-open-stalk-localization`
   identifies the stalk at `z` with the localization of `Γ(Y,W)` at that prime.
   Apply `lem-trf-regular-local-ring-isomorphism` to this ring isomorphism and its
   inverse. Regularity on the two sides is equivalent, proving equality of subsets.
2. If the regular locus is open, its restriction to every open chart is open; the
   canonical chart homeomorphism then makes the corresponding ring locus open.
   Conversely, inverse images of open ring loci are open in each chart and hence
   in `Y`. The covering condition expresses the regular locus as the union of
   these open subsets, so it is open. Arbitrary unions require no finite-cover
   hypothesis, and this also covers an empty index set on an empty scheme.
3. On `Spec B`, points are primes of `B` and the stalk at `p` is canonically
   isomorphic to `Localization.AtPrime p.asIdeal` (Tag 01HV (6)). Apply the same
   ring-isomorphism invariance in both directions to obtain equality of subsets
   and therefore equivalence of openness. The zero ring has no primes, so both
   loci are empty in that case.
-/
theorem regularLocus_affine_chart_gluing (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    (∀ W : Y.affineOpens,
      (fun z : (W : Y.Opens) ↦ (z : Y)) ⁻¹'
          {z : Y | IsRegularLocalRing (Y.presheaf.stalk z)} =
        W.2.primeIdealOf ⁻¹' {q : PrimeSpectrum Γ(Y, W) |
          IsRegularLocalRing (Localization.AtPrime q.asIdeal)}) ∧
    (∀ (J : Type v) (W : J → Y.affineOpens),
      (⨆ j : J, (W j : Y.Opens)) = ⊤ →
      (IsOpen {z : Y | IsRegularLocalRing (Y.presheaf.stalk z)} ↔
        ∀ j : J, IsOpen {q : PrimeSpectrum Γ(Y, W j) |
          IsRegularLocalRing (Localization.AtPrime q.asIdeal)})) ∧
    (∀ (B : Type w) [CommRing B] [IsNoetherianRing B],
      {p : PrimeSpectrum B |
          IsRegularLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk p)} =
        {p : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime p.asIdeal)} ∧
      (IsOpen {p : PrimeSpectrum B |
          IsRegularLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk p)} ↔
        IsOpen {p : PrimeSpectrum B |
          IsRegularLocalRing (Localization.AtPrime p.asIdeal)})) := by
  sorry

end AlgebraicGeometry
