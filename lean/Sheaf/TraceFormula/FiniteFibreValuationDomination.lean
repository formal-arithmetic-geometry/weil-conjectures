/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Sheaf.TraceFormula.ValuationHorizontalCurveModels
public import Sheaf.AlgebraicGeometry.CenteredValuation
public import Sheaf.TraceFormula.Modification
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.ClosedPointsProduct
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension
import Sheaf.Compactification.NagataSketchClosure
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite

/-!
# Finite fibre-valuation tests for domination

Source: Temkin, *Stable modification of relative curves*, Lemmas 4.2.1--4.2.2,
Proposition 4.2.3, and the first paragraph of the proof of Proposition 4.3.1,
pp. 26--27 (blueprint: lem-trf-finite-fibre-valuation-domination).

The component valuations bundle the existing `IsCenteredValuation` condition.
The base residue field at the image of the centre canonically equals the residue
field of the restricted valuation ring: if that image is s, then O intersect K
is V localized at s. Thus residual transcendence degree is computed through the
actual residue-field map of the composite valuation morphism to Spec V.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A centred valuation on an actual irreducible component, with its specified morphism.
At a component generic point of a reduced scheme, the residue field is canonically
its reduced component's function field. There is no closed-centre requirement here.
Source: Temkin, §4.2, p. 26
(blueprint: lem-trf-finite-fibre-valuation-domination). -/
structure ComponentCenteredValuation (C : Scheme.{u}) where
  generic : C
  component_generic : ∃ Z ∈ irreducibleComponents C, IsGenericPoint generic Z
  ring : ValuationSubring (C.residueField generic)
  map : Spec (.of ring) ⟶ C
  centered : IsCenteredValuation generic ring map

/-- The centre of the specified valuation morphism.
Source: Temkin, §4.2, p. 26
(blueprint: lem-trf-finite-fibre-valuation-domination). -/
def ComponentCenteredValuation.centre {C : Scheme.{u}} (ν : ComponentCenteredValuation C) : C :=
  ν.map (IsLocalRing.closedPoint ν.ring)

/-- Genericity in the fibre through a point, rather than genericity in the total scheme.
Source: Temkin, §4.2, the set (C/S)^0
(blueprint: lem-trf-finite-fibre-valuation-domination). -/
def IsFibreGenericPoint {T C : Scheme.{u}} (c : C ⟶ T) (x : C) : Prop :=
  ∃ Z ∈ irreducibleComponents (c.fiber (c x)), IsGenericPoint (c.asFiber x) Z

/-- Residual transcendence degree with the canonical base residue-field inclusion.
For a relative curve over the valuation base, the restriction O intersect K is V_s,
where s is the base image of the centre. Its residue field is therefore κ(s);
the residue field of Spec O at its closed point is canonically O/m_O.
The algebra structure below is precisely the map induced by the specified morphism.
Source: Temkin, §4.2, definition of the residual-degree-one valuation subset
(blueprint: lem-trf-finite-fibre-valuation-domination). -/
def ComponentCenteredValuation.residualDegree {T C : Scheme.{u}} (c : C ⟶ T)
    (ν : ComponentCenteredValuation C) : Cardinal.{u} :=
  @Algebra.trdeg (T.residueField ((ν.map ≫ c) (IsLocalRing.closedPoint ν.ring)))
    ((Spec (.of ν.ring)).residueField (IsLocalRing.closedPoint ν.ring)) _ _
    ((ν.map ≫ c).residueFieldMap (IsLocalRing.closedPoint ν.ring)).hom.toAlgebra

/-- A finite valuation test for domination, unique lifting, the closed-centre dichotomy,
and persistence of fibre-generic centres under modifications of normal curves.
Source: Temkin, Lemmas 4.2.1--4.2.2, Proposition 4.2.3 and proof of Proposition 4.3.1
(blueprint: lem-trf-finite-fibre-valuation-domination).

Proof, following the node's nine steps:
1. The empty-marking case of valuation-horizontal-curve-models makes every reduced
modification a relative curve and an isomorphism on the generic fibre. Apply the
proper separated valuation extension theorem to lift each specified valuation uniquely.
2. In the common component valuation spaces take F = Gamma_0(W). The
modification-fibre-centre-finite lemma gives finiteness, residual degree one and
closed original centres.
3. The hypothesis is F contained in Gamma(C'). Generalization stability and the
formula Gamma(W) = gen(F) union Gamma(C) give Gamma(W) contained in Gamma(C').
4. Take the schematic closure Z of the common dense isomorphism open in W times_C C'.
The closure theorem makes it schematically dense, and the affine kernel construction
makes Z reduced. Both projections are proper by proper base change and properness
of closed immersions, and are modifications. Horizontal-curve-models makes Z a curve.
5. A valuation in Gamma(Z) outside Gamma(C') has nongeneric, hence fibre-closed,
centres on both W and C'. The closed-points-of-product lemma and the injectivity
of the graph immersion make its centre on Z fibre-closed, contradicting genericity.
6. Thus the projection Z to C' contracts no fibre component. A positive-dimensional
fibre over a closed point would contain such a component. Over a generic point only
finitely many generic points can occur, by the closed-point residue-field criterion.
All fibres have dimension zero, so the relative-dimension-zero criterion makes the
projection locally quasi-finite. Proper locally quasi-finite morphisms are finite.
7. Apply finite-birational-normal-iso on the disjoint normal components of C'. The
projection is an isomorphism. Compose its inverse with Z to W to obtain h, a
modification. Dense-open uniqueness for separated W to C makes every C-map equal to h.
8. A lifted centre which is not fibre-generic is fibre-closed. Its residue field is
finite over the base residue field and hence over that of the original centre.
The closed-point criterion makes it closed in the fibre over the original centre;
if that original centre is closed in C, it is closed in the entire modification.
9. The modification locus for a normal base curve is closed and quasi-finite over T
by modification-fibre-centre-finite. It cannot contain any fibre component generic
point. The complementary isomorphism neighbourhood preserves such points, and the
unique valuation lift has the resulting fibre-generic centre.
-/
theorem finite_fibre_valuation_domination (A : HorizontalValuationBase.{u})
    {C W : Scheme.{u}} (c : C ⟶ A.T) (hcurve : RelativeCurve c)
    (hnormal : ∀ x : C, IsDomain (C.presheaf.stalk x) ∧
      IsIntegrallyClosed (C.presheaf.stalk x))
    (hsmooth : Smooth (pullback.snd c A.genericMap))
    (hcomponents : (irreducibleComponents C).Finite)
    (q : W ⟶ C) (hq : SchemeModification q) (hW : IsReduced W) :
    (∃ F : Set (ComponentCenteredValuation C), F.Finite ∧
      (∀ ν ∈ F, ν.residualDegree c = 1 ∧ IsClosed ({ν.centre} : Set C)) ∧
      ∀ {C' : Scheme.{u}} (p : C' ⟶ C), SchemeModification p →
        (∀ x : C', IsDomain (C'.presheaf.stalk x) ∧
          IsIntegrallyClosed (C'.presheaf.stalk x)) →
        (∀ ν ∈ F, ∃ l : Spec (.of ν.ring) ⟶ C', l ≫ p = ν.map ∧
          IsFibreGenericPoint (p ≫ c) (l (IsLocalRing.closedPoint ν.ring))) →
        ∃ h : C' ⟶ W, h ≫ q = p ∧ SchemeModification h ∧
          ∀ h' : C' ⟶ W, h' ≫ q = p → h' = h) ∧
    (∀ {C' : Scheme.{u}} (p : C' ⟶ C), SchemeModification p → IsReduced C' →
      ∀ ν : ComponentCenteredValuation C,
        (∃! l : Spec (.of ν.ring) ⟶ C', l ≫ p = ν.map) ∧
        ∀ l : Spec (.of ν.ring) ⟶ C', l ≫ p = ν.map →
          IsClosed ({ν.centre} : Set C) →
          IsFibreGenericPoint (p ≫ c) (l (IsLocalRing.closedPoint ν.ring)) ∨
            IsClosed ({l (IsLocalRing.closedPoint ν.ring)} : Set C')) ∧
    (∀ {B B' : Scheme.{u}} (b : B ⟶ A.T), RelativeCurve b →
      (∀ x : B, IsDomain (B.presheaf.stalk x) ∧
        IsIntegrallyClosed (B.presheaf.stalk x)) →
      Smooth (pullback.snd b A.genericMap) →
      ∀ r : B' ⟶ B, SchemeModification r → IsReduced B' →
        (∀ x : B, IsFibreGenericPoint b x →
          ∃ U : B.Opens, x ∈ U ∧ IsIso (r ∣_ U)) ∧
        ∀ (ν : ComponentCenteredValuation B) (l : Spec (.of ν.ring) ⟶ B'),
          l ≫ r = ν.map → IsFibreGenericPoint b ν.centre →
            IsFibreGenericPoint (r ≫ b) (l (IsLocalRing.closedPoint ν.ring))) := by
  sorry

end AlgebraicGeometry
