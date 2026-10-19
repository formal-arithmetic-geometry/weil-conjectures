/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension
public import Sheaf.AlgebraicGeometry.AdaptedNormalCrossingsCenter
public import Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import WeilConjectures.RingTheory.KoszulBaseChangeIso
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import WeilConjectures.Algebra.Homology.FreeResolutionSesSplit
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Blowup.FiniteDegree.Algebra
import Sheaf.RingTheory.NoetherianLocalKoszulCriterion

/-!
# Tor-independent base change of regular blowups and strict transforms

Source: ILO, Expose X, Lemma 1.6 and its proof, printed pp. 142--143, and the
1.7 Claim with adapted coordinates, printed pp. 144--145
(blueprint: lem-per-tor-independent-blowup-transform).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map from the tensor pullback of an ideal power to the structure sheaf.
It is the adjoint of the ideal inclusion followed by the actual structure-sheaf map;
the section-normalized adjunction sends `1 ⊗ s` to `g♯(s)`. Source: ILO X 1.6 proof,
p. 143 (blueprint: lem-per-tor-independent-blowup-transform). -/
def idealPowerPullbackToStructure {X X' : Scheme.{u}} (g : X' ⟶ X)
    (I : X.IdealSheafData) (a : ℕ) :
    (Scheme.Modules.tensorPullback g).obj (I ^ a).toModules ⟶
      SheafOfModules.unit X'.ringCatSheaf :=
  ((Scheme.Modules.tensorPullbackSectionAdjunction g).homEquiv _ _).symm
    ((I ^ a).toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)

/-- The strict-transform comparison, including its ambient blowup comparison. Both
isomorphisms commute with the projections to `X'`, and the transform isomorphism commutes
with the maps to the old ambient blowup. Thus this is an equality of closed subschemes
after the canonical ambient base change, rather than merely an abstract scheme isomorphism.
The blowup map to the old blowup is the unique universal lift over `X`. Source: ILO X 1.6
and 1.7 Claim (blueprint: lem-per-tor-independent-blowup-transform). -/
def HasStrictTransformBaseChange {X X' : Scheme.{u}} (g : X' ⟶ X)
    (I W : X.IdealSheafData) : Prop :=
  ∃ eB : (I.comap g).blowup ≅ pullback g I.blowupMap,
    eB.hom ≫ pullback.fst g I.blowupMap = (I.comap g).blowupMap ∧
    ∃ eW : (I.comap g).strictTransform (W.comap g).subschemeι ≅
      pullback g (strictTransformToSource W.subschemeι I.blowupMap I.support.compl ≫
        W.subschemeι),
      eW.hom ≫ pullback.fst g
          (strictTransformToSource W.subschemeι I.blowupMap I.support.compl ≫ W.subschemeι) =
        strictTransformToSource (W.comap g).subschemeι (I.comap g).blowupMap
          (I.comap g).support.compl ≫ (W.comap g).subschemeι ∧
      eW.hom ≫ pullback.snd g
          (strictTransformToSource W.subschemeι I.blowupMap I.support.compl ≫ W.subschemeι) ≫
          strictTransformMap W.subschemeι I.blowupMap I.support.compl =
        strictTransformMap (W.comap g).subschemeι (I.comap g).blowupMap
          (I.comap g).support.compl ≫ eB.hom ≫ pullback.snd g I.blowupMap

/-- Tor-independent base change preserves a regular center, every ideal power, its blowup,
and the two strict-transform comparisons, including the whole adapted reduced boundary.
Tor independence is the published stalkwise predicate, equivalent to affine Tor vanishing.
The ideal-power isomorphisms are pinned to the canonical maps into the structure sheaf.
The boundary is the Cartier sum of its labelled distinct integral components, so its ideal
is their product; finite intersections are represented by finite suprema of ideals.
Source: ILO X 1.6, pp. 142--143, and 1.7 Claim, pp. 144--145
(blueprint: lem-per-tor-independent-blowup-transform).

Proof:
1. Locally write the center ideal as I=(f). By
   `lem-weil-pbc-regular-sequence-koszul-regular`, its finite free Koszul complex resolves
   A/I. Tor vanishing and `lem-weil-pbc-tor-symmetry` make its tensor with C acyclic in
   positive degrees. `lem-sc-koszul-base-change-iso` identifies this with K_C(g(f)).
   At points of the pulled-back center apply `lem-per-noetherian-local-koszul-criterion`
   and spread by `lem-exc-regular-sequence-principal-neighbourhood`. This proves regularity.
2. For a short exact sequence use `lem-weil-pbc-free-resolution-ses-split`; tensor the
   degreewise splittings and apply `lem-weil-pbc-complex-ses-homology-long-exact`.
   Acyclicity of the outer terms gives acyclicity of the middle. Finite direct sums
   are handled by the direct sums of free resolutions.
3. `lem-pur-regular-sequence-graded-polynomial` makes I^a/I^(a+1) finite free over A/I.
   Apply Step 2 inductively to 0 → I^a/I^(a+1) → A/I^(a+1) → A/I^a → 0.
   `lem-weil-pbc-tor-long-exact-first-variable` applied to 0 → I^a → A → A/I^a → 0
   then identifies C tensor I^a with (IC)^a by the actual multiplication map. For a=0
   this is the identity. The maps glue and respect the products of the Rees algebra.
4. `lemma-nagata-relative-proj-base-change-arbitrary` applied to this Rees isomorphism
   identifies the actual blowups canonically over X'.
5. Write B=A/J for W and D=A/(I+J) for its center. Resolve D by the finite free
   B-Koszul complex of a regular sequence generating the restricted I. Its terms are
   Tor-acyclic over A by the assumption for W. By
   `lem-pc-termwise-tor-acyclic-derived-tensor`, its ordinary tensor with C computes
   the derived tensor of D with C, whose positive homology vanishes by hypothesis.
   It is also the Koszul complex over B tensor_A C, giving Tor independence over B.
   Apply Steps 1--4 over W to get the regular pulled-back intersection and blowup.
6. `lemma-nagata-strict-transform-ambient-closed` identifies each strict transform
   with the blowup of the restricted center. Step 5 and associativity of pullbacks
   give the strict-transform isomorphism compatibly with the ambient blowup maps.
7. In adapted coordinates the center tuple together with each remaining boundary
   parameter is regular, by `lem-weil-pbc-regular-local-generators-regular-sequence`
   and `lem-weil-pbc-regular-sequence-permutation-noetherian-local`. The Tor assumptions
   for every nonempty component intersection and its intersection with the center,
   together with Step 1, give regularity of all the pulled-back tuples.
8. On a pivot-a chart `lem-trf-blowup-chart-regular-sequence-presentation` gives
   A[T_f]/(a T_f-f). Omit the pivot boundary component; replace the other center
   boundary coordinates by their ratio variables, and retain untouched boundary
   coordinates. Modulo each surviving boundary equation the pivot is a nonzerodivisor,
   by `def-nagata-blowup-chart-ring` for the shortened regular tuple. Thus each such
   principal boundary ideal is saturated by a, on both sides of base change.
9. By `lem-sc-regular-local-domain` the local chart is a domain. If a b lies in the
   product of the surviving boundary equations, saturation for the first factor
   makes b divisible by it. Cancel and repeat to remove each factor. Iteration
   removes every power of a. Thus the product ideal itself is saturated and defines
   the schematic closure of the whole boundary. The canonical chart map preserves
   all these equations. `prop-nagata-affine-blowup-chart-cover` glues the comparisons.
   With no center generators the positive Rees grading is zero: its Proj and all
   strict transforms are empty. The unit center ideal gives the identity blowup. -/
theorem torIndependent_blowup_transform {X X' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] (g : X' ⟶ X) (I : X.IdealSheafData)
    (hI : ∃ c : I.subscheme → ℕ, IsRegularClosedImmersionWithCodimension I.subschemeι c)
    (hTor : PullbackStalkTensor.IsTorIndependent I.subschemeι g) :
    (∃ c : (I.comap g).subscheme → ℕ,
      IsRegularClosedImmersionWithCodimension (I.comap g).subschemeι c) ∧
    (∀ a : ℕ, ∃ e : (Scheme.Modules.tensorPullback g).obj (I ^ a).toModules ≅
        ((I.comap g) ^ a).toModules,
      e.hom ≫ ((I.comap g) ^ a).toModulesι = idealPowerPullbackToStructure g I a) ∧
    (∃ e : (I.comap g).blowup ≅ pullback g I.blowupMap,
      e.hom ≫ pullback.fst g I.blowupMap = (I.comap g).blowupMap) ∧
    (∀ W : X.IdealSheafData,
      (∃ c : W.subscheme → ℕ, IsRegularClosedImmersionWithCodimension W.subschemeι c) →
      (∃ c : (I.comap W.subschemeι).subscheme → ℕ,
        IsRegularClosedImmersionWithCodimension (I.comap W.subschemeι).subschemeι c) →
      PullbackStalkTensor.IsTorIndependent W.subschemeι g →
      PullbackStalkTensor.IsTorIndependent
        ((I.comap W.subschemeι).subschemeι ≫ W.subschemeι) g →
      (∃ c : ((I.comap g).comap (W.comap g).subschemeι).subscheme → ℕ,
        IsRegularClosedImmersionWithCodimension
          ((I.comap g).comap (W.comap g).subschemeι).subschemeι c) ∧
      HasStrictTransformBaseChange g I W) ∧
    (IsRegularScheme X → IsRegularScheme X' → ∀ (r : ℕ) (W : Fin r → X.IdealSheafData),
      (∀ j : Fin r, IsIntegral (W j).subscheme) → Function.Injective W →
      (∏ j : Fin r, W j).IsNormalCrossingsDivisor →
      ((∏ j : Fin r, W j).comap g).IsNormalCrossingsDivisor →
      HasAdaptedNormalCrossingsCenter I W →
      (∀ s : Finset (Fin r), s.Nonempty →
        (∃ c : (s.sup W).subscheme → ℕ,
          IsRegularClosedImmersionWithCodimension (s.sup W).subschemeι c) ∧
        (∃ c : (I.comap (s.sup W).subschemeι).subscheme → ℕ,
          IsRegularClosedImmersionWithCodimension (I.comap (s.sup W).subschemeι).subschemeι c) ∧
        PullbackStalkTensor.IsTorIndependent (s.sup W).subschemeι g ∧
        PullbackStalkTensor.IsTorIndependent
          ((I.comap (s.sup W).subschemeι).subschemeι ≫ (s.sup W).subschemeι) g) →
      HasStrictTransformBaseChange g I (∏ j : Fin r, W j)) ∧
    (I = ⊥ → IsEmpty I.blowup ∧
      ∀ (Z : Scheme.{u}) (j : Z ⟶ X), IsEmpty (I.strictTransform j)) := by
  sorry

end AlgebraicGeometry
