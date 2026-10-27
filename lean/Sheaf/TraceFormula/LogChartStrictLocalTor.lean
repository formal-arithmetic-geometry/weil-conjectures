module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction
public import Sheaf.TraceFormula.LogChartFaceTorComparison
import Sheaf.TraceFormula.KatoTorIndependenceChart
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Sheaf.AlgebraicGeometry.PointedEtaleStalk

/-!
# Monomial quotient Tor vanishing for an arbitrary fs chart

Source: ILO, Travaux de Gabber, Exposé VIII, proof of Lemma 3.4.3, printed p. 110,
citing Kato (1994), 6.1(ii); Exposé VI 1.6 and 3.7(a), printed pp. 70 and 75
(blueprint: lem-trf-log-chart-strict-local-tor).

The chart monoid is written additively using `Multiplicative P` in monoid maps.
The existing `chartStrictHenselizationMap` gives its structural map to the recorded
strict henselization. The existing `LogChartFaceTor.tor` is first Tor of the quotient
by the span of the indicated monomials, with precisely this coefficient action.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An arbitrary fs chart on an affine locally Noetherian log regular fs log scheme
has monomial quotient Tor vanishing at every geometric point. No identification
of the chart monoid with the characteristic monoid is assumed.
Source: ILO VIII, proof of Lemma 3.4.3, printed p. 110 (Kato 1994, 6.1(ii));
VI 1.6 and 3.7(a), printed pp. 70 and 75
(blueprint: lem-trf-log-chart-strict-local-tor).

Proof:
1. The geometric structure-ring stalk is the colimit over pointed étale
neighbourhoods (`def-weil-pbc-geometric-stalks`). Restriction to affine ones is
cofinal (`lemma-weil-pbc-affine-neighbourhood-cofinal`), identifying it canonically
with `def-weil-pbc-strict-henselization-limit`, compatibly with the chart map.
By `lem-weil-pbc-strict-henselization-local-structure` it is strictly henselian
local. The chart condition of `def-trf-fs-log-blowup` identifies the log stalk
with the pushout of the original chart monoid and the ring units.
2. Apply `lem-trf-chart-face-localization-logification` to the face F of chart
elements mapping to units. The quotient Q of the face localization by its units
is the original characteristic monoid. By `lem-trf-fs-face-sharpening`, the
localized monoid is integral fs and Q is sharp fs with finite free group completion.
3. Apply `lem-trf-integral-monoid-free-sharpening-splitting`: choose a monoid
section Q into the face localization, splitting it as Q times its unit group.
Only the characteristic group is required to be free; units may have torsion.
4. By `lem-trf-log-regular-sharp-chart`, choose an affine pointed étale sharp chart
with monoid Q and the same characteristic identification at the original point.
5. The map P to Q is surjective, so the image of H is again a monoid ideal.
Apply `lem-trf-log-chart-face-tor-comparison` with the splitting and sharp chart:
it identifies first Tor for the original chart with first Tor for the sharp chart,
including the unit-character twist between their structural maps.
6. Apply `lem-trf-kato-tor-independence-chart` to the sharp chart and the image ideal.
Its generated monomial ideal is exactly the integer span of that monoid ideal.
The comparison therefore gives the claimed vanishing. Both comparisons include
empty and total monoid ideals. Transport through the canonical ring-colimit
identification in step 1 gives exactly the coefficient action displayed here.
-/
theorem logChart_strictLocal_torOne_isZero
    (X : FineSaturatedLogScheme.{u}) (A : Type u) [CommRing A]
    (eA : X.scheme ≅ Spec (.of A)) (hlog : X.IsLogRegular)
    (P : Type u) [AddCommMonoid P] (hP : IsFineSaturatedMonoid (Multiplicative P))
    (α : Multiplicative P →* A)
    (c : Multiplicative P →* X.logStructure.monoidSheaf.obj.obj
      (op (Scheme.Etale.mk (𝟙 X.scheme))))
    (hc : X.logStructure.IsChart (Scheme.Etale.mk (𝟙 X.scheme)) c)
    (hα : ∀ p : P,
      X.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 X.scheme)))
        (c (Multiplicative.ofAdd p)) =
      eA.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (α (Multiplicative.ofAdd p))))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (H : Set P) (hH : ∀ h ∈ H, ∀ p : P, h + p ∈ H) :
    IsZero (LogChartFaceTor.tor
      (X.logStructure.chartStrictHenselizationMap t
        (Scheme.Etale.mk (𝟙 X.scheme)) (Over.homMk t (Category.comp_id t)) c)
      (Multiplicative.ofAdd '' H)) := by
  sorry

end AlgebraicGeometry
