module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.StrictlySemistableCurve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart
import Sheaf.TraceFormula.ValuationSymmetricNodalBlowup
import WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete

/-! # Marked strictification of a semistable curve model

Source: Temkin, *Stable modification of relative curves*, Remark 4.5.2, printed p. 33
(strict semistable cofinality of modifications; strict pair charts at §4.3, p. 27)
(blueprint: lem-trf-valuation-marked-strictification).

The strictly semistable pair `(Z,F)` is rendered as `IsStrictlySemistableCurve Z.x ∧
Z.IsSemistable`: strict curve charts together with an etale marking in the relative smooth
locus. Near a marked point the etale marking is locally cut out by one function `t`, which
is an etale coordinate there, so this gives the pair chart `(Spec A[t], {t=0})`; away from
the closed marking the curve charts are pair charts with empty marking.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A semistable marked curve over a valuation base admits a strict semistable
marked refinement through an eta-modification.

Source: Temkin, *Stable modification of relative curves*, Remark 4.5.2, printed p. 33;
the strict pair charts are those of §4.3, printed p. 27
(blueprint: lem-trf-valuation-marked-strictification).

The proof is postponed. Proof plan:
1. The first-Fitting singular subscheme `N` of `Y/S` has support the nonsmooth locus and is
   unramified over `S`; each fibre `N_s` is discrete and quasi-compact, hence finite, and
   `S` is finite, so `N` is finite. For a semistable curve `X` let `d(X)` be the number of
   nonsmooth points at which some reduced fibre component is not smooth.
2. If `d(X) > 0`, choose a counted point `z` and take the symmetric nodal blowup of `X`
   along the whole closure `C` of `z` (ideal `Fit₁(Ω¹) + (π)` near `C`, unit off `C`). It
   is proper and semistable, every fibre component over `C` is smooth, and the centre
   misses the marking, which is unchanged.
3. Off `C` the blowup is an isomorphism, so `d` strictly drops; induction on `d(Y)` gives
   a semistable pair `(Z,F)` with `d(Z) = 0`, marking `F ≅ E`, generic identity, and a
   proper composite `Z → Y` by permanence of properness.
4. Every reduced component of every fibre of `Z` is smooth, so the smooth-branches chart
   criterion gives a Zariski strict pair chart at every point: `(Z,F)` is strictly
   semistable.
5. `F → E` is an isomorphism and `Z → Y` is proper; both are the identity generically,
   and the generic fibre is schematically dense in each flat `V`-scheme by torsion-freeness,
   so `(Z,F) → (Y,E)` is an eta-modification. This covers `d(Y) = 0`, the empty marking and
   the empty curve. -/
theorem exists_valuation_marked_strictification
    (K : Type u) [Field K] [IsSepClosed K]
    (V : ValuationSubring K) [Finite (PrimeSpectrum V)]
    (Y : MultipointedCurve (Spec (.of V)))
    (hY : Y.IsSemistable)
    (hgeneric : Smooth (pullback.snd Y.x
      (Spec.map (CommRingCat.ofHom V.subtype))))
    (hmarking : Etale (pullback.snd Y.d
      (Spec.map (CommRingCat.ofHom V.subtype)))) :
    ∃ (Z : MultipointedCurve (Spec (.of V))) (f : Z.Hom Y),
      IsStrictlySemistableCurve Z.x ∧
      Z.IsSemistable ∧
      f.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)) := by
  sorry

end AlgebraicGeometry
