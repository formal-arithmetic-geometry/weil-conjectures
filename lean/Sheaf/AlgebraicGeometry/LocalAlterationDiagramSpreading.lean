module

public import Sheaf.AlgebraicGeometry.IntegralAlterationDiagram
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.FiniteDiagramLiftOfModels
import WeilConjectures.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Spreading a local alteration diagram with its proper witness

Source: Kurano--Shimomoto, Lemma 4.4, first proof paragraph, printed p. 5;
Stacks Project, Limits, Tags 01ZM, 0EUU, 07RR and 081F
(blueprint: lem-per-local-alteration-diagram-spreading).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Spread the specified finite alteration diagram, retaining its proper covering witness,
indexed open cover and all arrows. Every smaller principal neighbourhood outside the
prime has the same properties and recovers the same diagram.

Source: Kurano--Shimomoto, Lemma 4.4, first proof paragraph, printed p. 5,
with the diagram in Definition 3.2, printed p. 3
(blueprint: lem-per-local-alteration-diagram-spreading).

Proof:
1. Principal localizations away from the prime form a filtered system with colimit B_q
   [lem-weil-pbc-localization-colimit-principal-localizations]; their spectra form the
   affine inverse limit [lem-weil-pbc-limit-affine-transition]. Localization preserves
   Noetherianity [lem-weil-pbc-localization-noetherian]. All vertices, including the
   open-cover vertices, are quasi-compact and locally Noetherian, hence quasi-separated
   [lem-weil-pbc-locally-noetherian-quasi-separated]. The open inclusions are
   quasi-compact and finite type [lem-sfb-noetherian-open-immersion-qc,
   lem-weil-pbc-qc-open-immersion-finite-type]. The structure maps are finitely presented
   [pqf-lem-lft-fp-locnoeth, lem-weil-pbc-qcqs-morphism-permanence].
2. Descend the finitely many vertices [thm-pd-spreading-out] and their arrows and
   relations [lem-weil-pbc-finite-diagram-lift-of-models] to one common stage.
   Finite type over a Noetherian base gives Noetherian models
   [lem-weil-pbc-finite-type-over-noetherian].
3. Descend the open immersions [lem-weil-pbc-descend-open-immersion-qcqs], joint
   surjectivity of the finite family [lem-weil-pbc-finite-family-joint-surjectivity-stage],
   properness [lem-weil-pbc-eventually-proper] and surjectivity of the witness
   [lem-weil-pbc-descend-surjective]. Take a common later stage.
4. Shrink again to make the models integral [lem-per-integrality-prime-neighbourhood].
   On affine domain charts localization into the prime-local model is injective and
   preserves the zero prime. Generic points and fraction fields therefore identify
   [lem-sc-integral-function-field-affine-fraction,
   lem-weil-pbc-spec-domain-stalks-function-field], retaining dominance and finite
   generic field extensions.
5. Restriction to any smaller principal neighbourhood outside the prime preserves the
   open cover, properness, surjectivity and finite type by base change
   [lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-proper-fp-permanence,
   lem-weil-pbc-base-change-image, lem-sfb-finite-type-composition-base-change].
   The restrictions contain the generic points, so remain integral with unchanged
   function fields. Associativity of fibre products [def-pc-fibre-product] recovers
   the original entire specified diagram, including its open members and arrows.
-/
theorem exists_localAlterationDiagram_spreading
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (q : Ideal B) [q.IsPrime] (I : Type w) [Finite I]
    (D : IntegralAlterationDiagram I (Spec (.of (Localization.AtPrime q)))) :
    ∃ (a : B) (ha : a ∉ q)
      (E : IntegralAlterationDiagram I (Spec (.of (Localization.Away a)))),
      D.IsCartesianOver E
        (Spec.map (CommRingCat.ofHom (Localization.awayLift
          (algebraMap B (Localization.AtPrime q)) a
          (IsLocalization.map_units (M := q.primeCompl)
            (Localization.AtPrime q) ⟨a, ha⟩)))) ∧
      ∀ (b : B) (hb : b ∉ q), PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a →
        ∃ (r : Spec (.of (Localization.Away b)) ⟶ Spec (.of (Localization.Away a)))
          (F : IntegralAlterationDiagram I (Spec (.of (Localization.Away b)))),
          r ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a))) =
            Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ∧
          F.IsCartesianOver E r ∧
          D.IsCartesianOver F
            (Spec.map (CommRingCat.ofHom (Localization.awayLift
              (algebraMap B (Localization.AtPrime q)) b
              (IsLocalization.map_units (M := q.primeCompl)
                (Localization.AtPrime q) ⟨b, hb⟩)))) := by
  sorry

end AlgebraicGeometry
