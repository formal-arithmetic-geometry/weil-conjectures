/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.ZariskiLogStructure

/-!
# Characteristic stalks of a fixed fs chart

Source: ILO, Exposé VIII 3.1.1--3.1.2 and 3.3.2--3.3.4(ii), 3.3.12.
(blueprint: lem-trf-chart-characteristic-stalk-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The face of chart elements whose structural germ is a unit in the ordinary local
ring. The top-open section is transported by the canonical ring isomorphism `topIso`.
Source: ILO VIII 3.1.2, 3.3.2 (blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def EtaleLogStructure.globalChartUnitFace {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Q : Type u} [CommMonoid Q]
    (c : Q →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (⊤ : X.Opens).ι)))
    (x : X) : Submonoid Q :=
  (IsUnit.submonoid (X.presheaf.stalk x)).comap
    (((X.presheaf.germ ⊤ x (by trivial)).hom.toMonoidHom.comp
      (⊤ : X.Opens).topIso.hom.hom.toMonoidHom).comp
      ((M.alpha.app (op (Scheme.Etale.mk (⊤ : X.Opens).ι))).hom.comp c))

/-- The monoidal space of the characteristic sheaf of a Zariski log structure.
Its sheaf is the existing sheafification of the quotient by units, not a new quotient.
Source: ILO VIII 3.1.1, 3.3.12 (blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def ZariskiLogStructure.characteristicMonoidalSpace {X : Scheme.{u}}
    (Z : ZariskiLogStructure X) : SheafedSpace CommMonCat.{u} where
  carrier := X.carrier
  presheaf := (FineFan.sharpSheaf Z.monoidSheaf.obj).obj
  IsSheaf := (FineFan.sharpSheaf Z.monoidSheaf.obj).property

/-- The actual characteristic class of a log section, using the unit quotient and
its sheafification unit. Source: ILO VIII 3.1.1, 3.3.12
(blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def ZariskiLogStructure.characteristicSection {X : Scheme.{u}}
    (Z : ZariskiLogStructure X) (V : X.Opens) :
    Z.monoidSheaf.obj.obj (op V) →*
      Z.characteristicMonoidalSpace.presheaf.obj (op V) :=
  (((toSheafify (Opens.grothendieckTopology X.carrier)
    (FineFan.sharpPresheaf Z.monoidSheaf.obj)).app (op V)).hom).comp
      Associates.mkMonoidHom

/-- Descent and the normalized ordinary/geometric characteristic identifications.
Source: ILO VIII 3.1.1--3.1.2, 3.3.2--3.3.4(ii), 3.3.12; Steps 1 and 3 of
lem-trf-monoid-chart-characteristic-fan.

Proof. Sheafify the constant Zariski prelog chart and apply
`zariski_prelog_logification_comparison`. The inverse-image adjunction and the
constant-sheaf universal property identify compatible maps out of its etale
logification with compatible maps from Q to global sections. Apply
`associatedLog_universal_stalks` to identify that logification with the given
chart: the extensions in both directions fix Q and units, so uniqueness makes
their composites identities. This supplies Z, e, z and the chart condition.
At x, write E for the preimage of the local ring units. In the pushout stalk,
send the characteristic class of [q,u] to the class of q in Associates(Q_E).
The relation [qe,u]=[q,beta(e)u] kills exactly E and hence its group completion.
The inverse sends q/e to the class of [q,beta(e)^(-1)]; the pushout relations
show that it is well defined and that both composites are identities. The same
formulas at a geometric point give b. The ordinary-to-strict-local ring map
reflects units, so the face is identical, and change of site fixes q and extends
u. Thus both maps agree on every local section germ, as displayed. On a chart
numerator the formula gives the actual completion element of q, proving the
numerator equation. The empty scheme is vacuous, and E=Q gives the trivial
characteristic monoid, so neither case needs an exclusion.
(blueprint: lem-trf-chart-characteristic-stalk-comparison). -/
theorem chart_characteristic_stalk_comparison
    (X : FineSaturatedLogScheme.{u}) (Q : Type u) [CommMonoid Q]
    (hQ : IsFineSaturatedMonoid Q)
    (c : Q →* X.logStructure.monoidSheaf.obj.obj
      (op (Scheme.Etale.mk (⊤ : X.scheme.Opens).ι)))
    (hc : X.logStructure.IsChart (Scheme.Etale.mk (⊤ : X.scheme.Opens).ι) c) :
    ∃ (Z : ZariskiLogStructure X.scheme)
      (e : Z.toZariskiPrelogStructure.EtaleMap X.logStructure)
      (z : Q →* Z.monoidSheaf.obj.obj (op ⊤))
      (a : ∀ x : X.scheme,
        FineFan.stalk Z.characteristicMonoidalSpace.presheaf x ≃*
          Associates (Algebra.faceLocalization Q (X.logStructure.globalChartUnitFace c x)))
      (b : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
        X.logStructure.characteristic t ≃*
          Associates (Algebra.faceLocalization Q
            (X.logStructure.globalChartUnitFace c (t default)))),
      e.IsAssociation ∧ Z.IsChart ⊤ z ∧ (e.sectionMap ⊤).comp z = c ∧
      (∀ (x : X.scheme) (q : Q),
        ∃ r : Algebra.faceLocalization Q (X.logStructure.globalChartUnitFace c x),
          r.val = Algebra.GrothendieckGroup.of q ∧
          a x (FineFan.germ Z.characteristicMonoidalSpace.presheaf ⊤ x (by trivial)
            (Z.characteristicSection ⊤ (z q))) = Associates.mk r) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
        (V : X.scheme.Opens)
        (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk V.ι))
        (hx : t default ∈ V) (s : Z.monoidSheaf.obj.obj (op V)),
        b Ω t (Associates.mk (X.logStructure.toEtalePrelogStructure.germ t
          (Scheme.Etale.mk V.ι) w (e.sectionMap V s))) =
          a (t default) (FineFan.germ Z.characteristicMonoidalSpace.presheaf
            V (t default) hx (Z.characteristicSection V s)))  := by
  sorry

end AlgebraicGeometry
