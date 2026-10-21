/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.TraceFormula.StrictSemistableCurve
public import Sheaf.TraceFormula.Modification
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.FieldTheory.IsSepClosed

import WeilConjectures.Blowup.Affine.ChartAlgebra
import Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal
import Sheaf.SecTraceFormula.RationalValuationLinearResidue
import Sheaf.TraceFormula.FiniteFibreValuationDomination
import Sheaf.TraceFormula.ResidualCurveValueGroup
import Sheaf.TraceFormula.ValuationHorizontalCurveModels

/-!
# Single valuation semistable extraction

Source: Temkin, *Stable modification of relative curves*, Proposition 4.3.1,
pp. 27--29 (blueprint: lem-trf-single-valuation-semistable-extraction).

Strict semistable charts and schematic modifications reuse the published interfaces.
The valuation is on the residue field of an actual component generic point; its residual
transcendence degree uses the canonical inclusion of the restricted valuation ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Inclusion of the restricted valuation ring `O ∩ K` into `O`.
Source: Temkin, Proposition 4.3.1, p. 28
(blueprint: lem-trf-single-valuation-semistable-extraction). -/
def valuationRestrictionHom {K L : Type u} [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring L) : O.comap (algebraMap K L) →+* O :=
  ((algebraMap K L).comp (O.comap (algebraMap K L)).subtype).codRestrict
    O.toSubring (fun x ↦ x.property)

/-- Inclusion of the base valuation ring into a component-field valuation ring.
The membership proof supplies a codomain restriction of the given field inclusion.
Source: Temkin, Proposition 4.3.1, p. 28
(blueprint: lem-trf-single-valuation-semistable-extraction). -/
def valuationBaseHom {K L : Type u} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (O : ValuationSubring L)
    (h : ∀ v : V, algebraMap K L (v : K) ∈ O) : V →+* O :=
  ((algebraMap K L).comp V.subtype).codRestrict O.toSubring h

/-- A specified centred valuation on the function field of a component of a strict curve.
`componentField` identifies the field with the residue field at the component generic
point. For the reduced curve this is precisely the function field of its reduced component.
`generic_comm` prescribes the entire morphism from `Spec L`, including its field map.
`base_comm` makes the valuation map a morphism over `Spec V` for the given field inclusion.
The restriction-locality proof is the usual fact that a valuation ring dominates its
restriction to a subfield; it permits the canonical map on residue fields to be used below.
Source: Temkin, Proposition 4.3.1, pp. 27--28
(blueprint: lem-trf-single-valuation-semistable-extraction). -/
structure CenteredValuation {K : Type u} [Field K] (V : ValuationSubring K)
    (C : StrictSemistableCurve (Spec (.of V))) (L : Type u) [Field L] [Algebra K L] where
  O : ValuationSubring L
  extends_base : ∀ v : V, algebraMap K L (v : K) ∈ O
  restriction_local : IsLocalHom (valuationRestrictionHom (K := K) O)
  map : Spec (.of O) ⟶ C.Y
  base_comm : map ≫ C.structureMap =
    Spec.map (CommRingCat.ofHom (valuationBaseHom V O extends_base))
  component : Set C.Y
  component_mem : component ∈ irreducibleComponents C.Y
  componentGeneric : C.Y
  component_generic : IsGenericPoint componentGeneric component
  componentField : C.Y.residueField componentGeneric ≃+* L
  generic_comm : Spec.map (CommRingCat.ofHom (algebraMap O L)) ≫ map =
    Spec.map (CommRingCat.ofHom componentField.toRingHom) ≫
      C.Y.fromSpecResidueField componentGeneric
  centre_closed : IsClosed ({map (IsLocalRing.closedPoint O)} : Set C.Y)

/-- The canonical residue field inclusion `κ(O ∩ K) → κ(O)`.
Source: Temkin, Proposition 4.3.1, p. 28
(blueprint: lem-trf-single-valuation-semistable-extraction). -/
def CenteredValuation.residueMap {K : Type u} [Field K] {V : ValuationSubring K}
    {C : StrictSemistableCurve (Spec (.of V))} {L : Type u} [Field L] [Algebra K L]
    (ν : CenteredValuation V C L) :
    IsLocalRing.ResidueField (ν.O.comap (algebraMap K L)) →+* IsLocalRing.ResidueField ν.O :=
  @IsLocalRing.ResidueField.map (ν.O.comap (algebraMap K L)) ν.O _ _ _ _
    (valuationRestrictionHom ν.O) ν.restriction_local

/-- Residual transcendence degree with respect to the restricted valuation `O ∩ K`.
The algebra structure is induced by `residueMap`, not an independently chosen field map.
Source: Temkin, Proposition 4.3.1, pp. 27--28
(blueprint: lem-trf-single-valuation-semistable-extraction). -/
def CenteredValuation.residualTrdeg {K : Type u} [Field K] {V : ValuationSubring K}
    {C : StrictSemistableCurve (Spec (.of V))} {L : Type u} [Field L] [Algebra K L]
    (ν : CenteredValuation V C L) : Cardinal.{u} :=
  @Algebra.trdeg (IsLocalRing.ResidueField (ν.O.comap (algebraMap K L)))
    (IsLocalRing.ResidueField ν.O) _ _ ν.residueMap.toAlgebra

/-- The unique lift of the specified valuation has a generic centre in its base fibre.
The base point is the image of the original centre; it need not be the generic point of T.
Source: Temkin, Proposition 4.3.1, pp. 28--29
(blueprint: lem-trf-single-valuation-semistable-extraction). -/
def IsGenericValuationCentre {K : Type u} [Field K] {V : ValuationSubring K}
    {C C' : StrictSemistableCurve (Spec (.of V))} {L : Type u} [Field L] [Algebra K L]
    (ν : CenteredValuation V C L) (b : C'.Y ⟶ C.Y) : Prop :=
  ∃ lift : Spec (.of ν.O) ⟶ C'.Y,
    lift ≫ b = ν.map ∧
      (∃ z : C'.structureMap.fiber (C.structureMap (ν.map (IsLocalRing.closedPoint ν.O))),
        ∃ Z : Set (C'.structureMap.fiber
          (C.structureMap (ν.map (IsLocalRing.closedPoint ν.O)))),
          Z ∈ irreducibleComponents (C'.structureMap.fiber
            (C.structureMap (ν.map (IsLocalRing.closedPoint ν.O)))) ∧
          IsGenericPoint z Z ∧
          lift (IsLocalRing.closedPoint ν.O) =
            C'.structureMap.fiberι (C.structureMap (ν.map (IsLocalRing.closedPoint ν.O))) z) ∧
      ∀ lift' : Spec (.of ν.O) ⟶ C'.Y, lift' ≫ b = ν.map → lift' = lift

/-- Single-valuation semistable extraction.
Source: Temkin, *Stable modification of relative curves*, Proposition 4.3.1,
proof pp. 27--29 (blueprint: lem-trf-single-valuation-semistable-extraction).

Proof, following the node's seven steps:
1. Put x = ν(closed point), s = image(x), and R = V_s. The specified T-morphism
   identifies R with O ∩ K: elements outside s are units in O, while if c is outside
   R its inverse belongs to the maximal ideal of R and hence to that of O. Work in
   a smooth or nodal chart at x using elementary-semistable-chart-globalization.
   Strict semistability and smooth generic fibre imply normality of C. The empty
   marking case of valuation-horizontal-curve-models gives finitely many components.
2. Flat going-down sends a component generic point to the generic point of its
   rational chart. The etale residue-field theorem therefore makes L finite separable
   over K(t) or K(u). Restricting O to this rational subfield preserves residual
   transcendence degree: normalize a polynomial relation by a coefficient of least
   valuation and reduce to obtain algebraicity of the residue extension.
3. At a nodal centre uv=c, residual-curve-value-group gives a nonzero π in m_R
   with u/π a unit of O, and c/π lies in R. Apply the globalized blowup operation
   for (u,π). Its two charts have equations vw=c/π, u=πw, and uz=π,
   v=(c/π)z. The specified valuation map lifts to the first chart.
4. The lift has unit coordinate w and lies on the smooth multiplicative-group locus.
   Etale base change and composition supply an affine-line chart there. The
   finite-fibre-valuation-domination lemma says its centre is fibre-generic or closed.
   Stop in the former case; in the latter case use the smooth chart. If the original
   centre was smooth, start this step with the identity modification.
5. The image of the remaining closed centre in the affine-line fibre is closed by
   Zariski's lemma. Rational-valuation-linear-residue supplies a in R and nonzero
   π in m_R with w=(t-a)/π a unit having transcendental residue. Thus the pointed
   hypothesis for the smooth chart operation is satisfied.
6. Globalize the blowup of (t-a,π). The π-chart is R[w], t=a+πw, and the other
   chart is R[q,z]/(qz-π). The specified map lifts to the first. Transcendence of
   the residue of w makes its model centre fibre-generic. After etale base change
   it remains generic: localization at the model generic point is etale over a field,
   hence a finite product of fields, with all primes minimal.
7. Compose the two proper generic-fibre isomorphisms. Finiteness of Spec V makes
   its generic point open, and flatness makes the entire generic fibres schematically
   dense. This gives an eta-modification. The valuative criterion for its proper,
   hence separated, morphism gives uniqueness of the lift of the original specified
   valuation map. Its centre has the fibre-generic property proved in step 6.
-/
theorem exists_singleValuationSemistableExtraction
    {K : Type u} [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)] (C : StrictSemistableCurve (Spec (.of V)))
    (hCη : Smooth (pullback.snd C.structureMap (Spec.map (CommRingCat.ofHom V.subtype))))
    {L : Type u} [Field L] [Algebra K L] (ν : CenteredValuation V C L)
    (hν : ν.residualTrdeg = (1 : Cardinal.{u})) :
    ∃ (C' : StrictSemistableCurve (Spec (.of V))) (b : C'.Y ⟶ C.Y),
      C'.structureMap = b ≫ C.structureMap ∧
      EtaModification (Spec.map (CommRingCat.ofHom V.subtype)) b C.structureMap ∧
      IsGenericValuationCentre ν b := by
  sorry

end AlgebraicGeometry
