/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.RingTheory.CompleteToricModel
public import Sheaf.AlgebraicGeometry.LogInfinitesimalLifting
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.CohenRing
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.FormalMonoidRingDimension
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Completed sharp charts at one log regular point

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI 1.1--1.2 and
1.6(i)--(ii), printed pp.69--70 (blueprint: lem-per-pointwise-log-regular-completion).

Only the chosen geometric point is assumed log regular. The strict pullback map
and its chart on `Spec A` retain the actual chart sections. The completion models,
monomials and boundary ideals use the published `ToricMonoid` notation for the
`AddMonoidAlgebra` constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- An fs log scheme log regular at the chosen geometric point has a prescribed
sharp chart and the two chart-compatible completed local presentations.
Source: ILO VI 1.1--1.2 and 1.6(i)--(ii), printed pp.69--70
(blueprint: lem-per-pointwise-log-regular-completion).

Proof:
1. Choose a Noetherian affine open at the image of the point. Restricting pointed
neighbourhoods to this open is cofinal. The ordinary stalk is a localization of
its coordinate ring and is Noetherian. The geometric strict-henselization local
presentation and strict-henselization Noetherianity make A Noetherian; the strict
local structure gives locality and nonzeroness. Uses pqf-def-locnoeth,
lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian,
lem-sbc-geometric-strict-henselization-local-presentation,
lem-sc-strict-henselization-noetherian and
lem-weil-pbc-strict-henselization-local-structure.
2. Choose an fs chart Q and its face F mapping to A-units. The face-localized
chart identifies the log stalk with the pushout of Q_F and A-units over F^gp,
and its characteristic with the prescribed P, not an unspecified isomorphic
monoid. Uses def-trf-fs-log-blowup and lem-trf-chart-face-localization-logification.
3. Face sharpening makes P sharp fs with finite free group completion. The
integral-monoid free-sharpening splitting gives a section P -> Q_F, even with
torsion in F^gp. Its stalk map h gives P times A-units isomorphic to the log stalk;
nonidentity elements have nonunit images, and the characteristic map is the identity.
Uses lem-trf-fs-face-sharpening, lem-trf-integral-monoid-free-sharpening-splitting
and lem-trf-chart-face-localization-logification.
4. Spread h to an affine pointed etale chart, preserving its germ. Under the
canonical map Spec A -> W, the integral chart logification universal property
identifies the associated pulled-back chart with the pullback log structure:
for any target log structure, maps out of either correspond to the same
structurally compatible maps from P, fixing the generators. This gives the
strict log morphism and its global chart on Spec A below. Uses
lem-trf-fine-log-stalk-chart-spreading and lem-sfb-fine-chart-logification-thickening.
5. The stalk splitting identifies I with the ideal of nonidentity chart images.
Choose n parameters of the regular local ring A/I and lift them to A. The
completed-chart coefficient-surjection lemma gives a surjection B_L(P,n) -> S,
where S is the maximal-ideal completion of A and L is k in equal characteristic
and a Cohen ring C otherwise. It sends monomials to the completed chart images,
and its boundary ideal J onto the maximal ideal of S. Moreover S is nonzero
Noetherian local and has dimension n + rank(P^gp). Uses def-weil-regular-scheme,
def-weil-pbc-regular-system-of-parameters and
lem-trf-completed-chart-coefficient-surjection.
6. In the field case put D = k[[t_1,...,t_n]]. Power-series regularity makes D
complete regular Noetherian local of dimension n. The polynomial/power-series
monoid-completion comparison identifies B_k(P,n) with the monoid completion over D,
fixing monomials. Formal-monoid-ring dimension makes this a Noetherian local domain
of dimension n + rank(P^gp). Uses
lem-weil-pbc-power-series-field-cohen-regular-complete,
lem-trf-polynomial-power-series-monoid-completion and lem-trf-formal-monoid-ring-dimension.
7. If the kernel of the surjection in the field case were nonzero, lift a maximal
prime chain of its finite-dimensional target to the domain source. Every lifted
prime contains that nonzero kernel. Prepend the zero prime to contradict equality
of the finite dimensions. The surjection is therefore an isomorphism. Uses
def-weil-pbc-krull-dimension-ring; the chain argument is elementary.
8. In the Cohen case lift the image of p to j in J. The Cohen-monoid principal-kernel
lemma applies to the sharp fs monoid, the nonzero Noetherian local target of dimension
n + rank(P^gp), and the equality of the image of J with its maximal ideal. It gives
kernel (theta), theta = p-j, and theta-p in J, with the specified monomial formula.
Uses lem-trf-cohen-monoid-surjection-principal-kernel.
9. Invert either isomorphism to get the direction below. Their defining monomial
formulas give chart compatibility. Retain the chart and its strict pullback from
Step 4. No other point's log regularity or excellence was used. For P trivial,
I is zero; for n=0 there are no parameter generators. If both vanish, A and S
are the residue field and B_k(0,0)=k. Nonzeroness and locality were checked above.
-/
theorem exists_completed_chart_of_logRegularAt
    (X : FineSaturatedLogScheme.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (_hreg : IsRegularLocalRing
      (strictLocalRing X.scheme t ⧸ X.logStructure.nonunitIdeal t))
    (_hdim : ringKrullDim (strictLocalRing X.scheme t) =
      ringKrullDim (strictLocalRing X.scheme t ⧸ X.logStructure.nonunitIdeal t) +
        (X.logStructure.characteristicRank t : WithBot ℕ∞)) :
    ∃ (_ : Nontrivial (strictLocalRing X.scheme t))
      (_ : IsNoetherianRing (strictLocalRing X.scheme t))
      (_ : IsLocalRing (strictLocalRing X.scheme t)),
      IsFineSaturatedMonoid (X.logStructure.characteristic t) ∧
      (∀ q : X.logStructure.characteristic t, IsUnit q → q = 1) ∧
      ∃ (W : X.scheme.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (_ : IsAffine W.left)
        (β : X.logStructure.characteristic t →*
          X.logStructure.monoidSheaf.obj.obj (op W)),
        X.logStructure.IsChart W β ∧
        (∀ q : X.logStructure.characteristic t,
          Associates.mk (X.logStructure.toEtalePrelogStructure.germ t W w (β q)) = q) ∧
        (∃ (L : EtaleLogStructure (Spec (strictLocalRing X.scheme t)))
          (f : EtaleLogMap L X.logStructure)
          (hf : (Spec.map (strictLocalGerm X.scheme t W w) ≫ W.left.isoSpec.inv) ≫
            W.hom = 𝟙 (Spec (strictLocalRing X.scheme t)) ≫ f.base),
          f.IsStrict ∧
          L.IsChart (Scheme.Etale.mk (𝟙 (Spec (strictLocalRing X.scheme t))))
            ((f.sectionMap W (Scheme.Etale.mk (𝟙 (Spec (strictLocalRing X.scheme t))))
              (Spec.map (strictLocalGerm X.scheme t W w) ≫ W.left.isoSpec.inv) hf).comp β)) ∧
        Nontrivial (AdicCompletion (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
          (strictLocalRing X.scheme t)) ∧
        IsNoetherianRing
          (AdicCompletion (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
            (strictLocalRing X.scheme t)) ∧
        IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
          (strictLocalRing X.scheme t)) ∧
        ∃ n : ℕ,
          ((∃ (K : Type u) (_ : Field K), Nonempty (K →+* strictLocalRing X.scheme t)) →
            ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
                (strictLocalRing X.scheme t) ≃+*
                ToricMonoid.Complete
                  (IsLocalRing.ResidueField (strictLocalRing X.scheme t))
                  (Additive (X.logStructure.characteristic t)) n,
              ∀ q : X.logStructure.characteristic t,
                e (algebraMap _ _ (X.logStructure.toEtalePrelogStructure.stalkAlpha t
                  (X.logStructure.toEtalePrelogStructure.germ t W w (β q)))) =
                    ToricMonoid.monomial _ _ n (Additive.ofMul q)) ∧
          ((¬ ∃ (K : Type u) (_ : Field K), Nonempty (K →+* strictLocalRing X.scheme t)) →
            ∃ p : ℕ, Nat.Prime p ∧
              CharP (IsLocalRing.ResidueField (strictLocalRing X.scheme t)) p ∧
              ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C), IsCohenRing p C ∧
                Nonempty ((C ⧸ IsLocalRing.maximalIdeal C) ≃+*
                  IsLocalRing.ResidueField (strictLocalRing X.scheme t)) ∧
                ∃ θ : ToricMonoid.Complete C
                    (Additive (X.logStructure.characteristic t)) n,
                  θ - (p : ToricMonoid.Complete C
                      (Additive (X.logStructure.characteristic t)) n) ∈
                    ToricMonoid.completedChartIdeal C
                      (Additive (X.logStructure.characteristic t)) n ∧
                  ∃ e : AdicCompletion
                      (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
                      (strictLocalRing X.scheme t) ≃+*
                      (ToricMonoid.Complete C
                        (Additive (X.logStructure.characteristic t)) n ⧸ Ideal.span {θ}),
                    ∀ q : X.logStructure.characteristic t,
                      e (algebraMap _ _ (X.logStructure.toEtalePrelogStructure.stalkAlpha t
                        (X.logStructure.toEtalePrelogStructure.germ t W w (β q)))) =
                          Ideal.Quotient.mk (Ideal.span {θ})
                            (ToricMonoid.monomial C _ n
                              (Additive.ofMul q))) := by
  sorry

end AlgebraicGeometry
