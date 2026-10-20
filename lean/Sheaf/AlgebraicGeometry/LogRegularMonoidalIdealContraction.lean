/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.RingTheory.FiniteType
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.TraceFormula.KatoTorIndependenceChart

/-!
# Contraction of monoidal ideals in a log regular sharp chart

Source: ILO, Travaux de Gabber, Exposé VIII, 3.4.1--3.4.3, printed p. 110
(blueprint: lem-trf-log-regular-monoidal-ideal-contraction).

The chart monoid is written additively. The structural map is transported from the
ring-valued geometric stalk to the recorded affine-neighbourhood strict henselization
by the canonical cofinality isomorphism.

## Main declarations

* `strictLocalRingIsoStrictHenselization`: canonical comparison of the two colimits.
* `EtaleLogStructure.chartStrictHenselizationMap`: the chart's structural map to that ring.
* `FineSaturatedLogScheme.monoidalIdeal_contraction`: recovery of every monoid ideal.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical identification of the ring-valued geometric stalk with the affine
pointed-neighbourhood strict henselization. It is induced by the final inclusion of
opposite affine pointed neighbourhoods, so it respects the prescribed ring germs.
Source: ILO VIII 3.4.1--3.4.3, at the geometric stalk
(blueprint: lem-trf-log-regular-monoidal-ideal-contraction). -/
noncomputable def strictLocalRingIsoStrictHenselization {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    strictLocalRing X x ≅ Scheme.strictHenselizationRing x :=
  let F := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods x)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion x ⋙ ObjectProperty.ι
      (fun n : (Scheme.pointSmallEtale x).fiber.Elements ↦ IsAffine n.1.left)
  letI : F.Initial := (Scheme.strictHenselization_properties x).1
  (Functor.Final.colimitIso F.op
    ((CategoryOfElements.π (Scheme.pointSmallEtale x).fiber).op ⋙
      X.etaleStructurePresheaf)).symm ≪≫
    Scheme.strictHenselizationRepresentativeIso x (CategoryTheory.Equivalence.refl)
      (F.op ⋙ (CategoryOfElements.π (Scheme.pointSmallEtale x).fiber).op ⋙
        X.etaleStructurePresheaf)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl))

/-- The structural map of a chart to the strict henselization: chart, monoid germ,
structural map on stalks, and the canonical affine-neighbourhood colimit identification.
Source: ILO VIII 3.4.1--3.4.3, printed p. 110
(blueprint: lem-trf-log-regular-monoidal-ideal-contraction). -/
noncomputable def EtaleLogStructure.chartStrictHenselizationMap {X : Scheme.{u}}
    (M : EtaleLogStructure X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (W : X.Etale)
    (w : (Scheme.pointSmallEtale x).fiber.obj W) {P : Type u} [AddCommMonoid P]
    (c : Multiplicative P →* M.monoidSheaf.obj.obj (op W)) :
    Multiplicative P →* Scheme.strictHenselizationRing x :=
  ((strictLocalRingIsoStrictHenselization x).hom.hom.toMonoidHom).comp
    ((M.toEtalePrelogStructure.stalkAlpha x).comp
      ((M.toEtalePrelogStructure.germ x W w).hom.comp c))

/-- A monoid ideal is recovered by contraction of its generated ring ideal in a sharp
chart of a locally Noetherian log regular fs log scheme, including the empty ideal.
Source: ILO VIII, Lemma 3.4.3 and conventions 3.4.1, printed p. 110
(blueprint: lem-trf-log-regular-monoidal-ideal-contraction).

Proof: (1) Put R = Z[P] and K = a⁻¹(JA). Multiplicativity makes K a monoid ideal
containing J. Apply `lem-trf-log-regular-sharp-chart` for finite generation, integrality
and sharpness; nonzero chart elements map to nonunits, so the ideal m_P A is proper.
(2) If J is properly contained in K, tensor JR → KR → KR/JR → 0 with A.
Apply `lem-trf-kato-tor-independence-chart` to identify IR ⊗_R A with IA for I = J,K.
Since JA = KA, right exactness forces (KR/JR) ⊗_R A = 0.
(3) The monomial basis identifies IR with the integer span of I. Finite generation
of P and `lem-weil-pbc-finite-type-algebra-noetherian` make Z[P] Noetherian, hence K
has finitely many monomial generators. Choose one outside J minimal under translation
by P. Sharpness and cancellation imply it is outside K + (P minus {0}).
The coefficient at this monomial gives an R-linear surjection KR/JR → R/m_P R = Z,
where nonzero monomials act by zero. Tensoring gives a surjection onto A/m_P A.
(4) This quotient is nonzero by properness, contradicting (2). Thus K = J.
For J empty the same argument applies with JR = 0; it excludes a(p) = 0 as well. -/
theorem FineSaturatedLogScheme.monoidalIdeal_contraction
    (X : FineSaturatedLogScheme.{u}) (hregular : X.IsLogRegular)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme)
    {P : Type u} [AddCommMonoid P] (W : X.scheme.Etale)
    (w : (Scheme.pointSmallEtale x).fiber.obj W)
    (c : Multiplicative P →* X.logStructure.monoidSheaf.obj.obj (op W))
    (hc : X.logStructure.IsChart W c)
    (hsharp : Function.Bijective (fun p : P ↦
      (Associates.mk (X.logStructure.toEtalePrelogStructure.germ x W w
        (c (Multiplicative.ofAdd p))) : X.logStructure.characteristic x)))
    (J : Set P) (hJ : ∀ j ∈ J, ∀ p : P, j + p ∈ J) :
    (fun p : P ↦ X.logStructure.chartStrictHenselizationMap x W w c
      (Multiplicative.ofAdd p)) ⁻¹'
        (Ideal.span ((fun p : P ↦ X.logStructure.chartStrictHenselizationMap x W w c
          (Multiplicative.ofAdd p)) '' J) : Set (Scheme.strictHenselizationRing x)) = J := by
  sorry

end AlgebraicGeometry
