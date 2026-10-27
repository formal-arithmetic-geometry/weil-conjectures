/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings
public import Sheaf.TraceFormula.StrictSemistableCurve
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RingHom.StandardSmooth
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import Sheaf.TraceFormula.GenericFibrePointsSmooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Étale local equations of nodal curves over a DVR

Source: Stacks Project, models.tex, Tag 0CDD, lemma-etale-local-at-worst-nodal;
curves.tex, Tag 0C5A for the geometric-fibre hypotheses
(blueprint: lem-sfb-dvr-nodal-etale-local-form).

The existing nodal quotient and its coefficient projection give the two models
by taking the parameter to be zero or a nonnegative power of a uniformizer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A flat locally finitely presented nodal curve over a DVR has, around every
special-fibre point, an étale chart with equation `uv=0` or `uv=π^n` after an
étale extension of DVRs. The exponent zero includes smooth points.

Source: Stacks Project, models.tex, Tag 0CDD, lemma-etale-local-at-worst-nodal;
curves.tex, Tags 0C5A and 0CBY.

Proof:
1. Finite-presentation affine charts over the Noetherian DVR have Noetherian
   geometric fibres (lem-weil-pbc-finite-type-over-noetherian). In a reduced pure
   one-dimensional fibre every nonclosed point is generic on a component and
   is smooth by lem-trf-generic-fibre-points-smooth. Thus the hypothesis about
   closed nonsmooth points supplies the all-point hypothesis of the nodal chart.
2. If f is smooth at x, lem-sc-fibre-dimension-after-base-change gives fibre
   dimension one. By sbc-lem-smooth-relative-dimension-locally-constant, shrink to
   pure relative dimension one. Use lem-sc-standard-smooth-local-relative-dimension
   and lem-sc-standard-smooth-etale-polynomial-chart to get an étale chart to R[t].
   The base open contains the closed point of Spec R, hence equals Spec R.
3. Replace t by t+1 if necessary, then restrict to D(t). Étaleness is preserved
   by base change and composition (lem-weil-pbc-etale-base-change-finite-limits,
   lem-weil-pbc-etale-composition-cancellation). The isomorphism
   R[u,v]/(uv-1) ≅ R[t,t⁻¹] gives the model with R'=R and n=0.
4. If f is nonsmooth at x, apply lem-trf-nodal-family-etale-local-model to get
   an étale base V and a chart uv=h. The image of the chosen point lies above
   the closed point of Spec R. Choose an affine neighbourhood Spec B in V.
   By lem-sfb-etale-dvr-principal-neighbourhood shrink it to D(b)=Spec R', where
   R' is a DVR and R→R' is injective, local and étale.
5. Restrict U and the model along D(b). The chosen point remains, the maps
   remain étale by the base-change and composition lemmas just cited, and the
   model becomes Spec R'[u,v]/(uv-h'). Both triangles still commute.
6. Choose a uniformizer π of R'. If h'=0 use the zero model. Otherwise
   lem-weil-pbc-dvr-unit-times-uniformizer-power writes h'=επ^n for a unit ε.
   The R'-algebra isomorphism sending the normalized coordinate u₀ to ε⁻¹u
   and v₀ to v, with inverse u↦εu₀, identifies this with uv=π^n.
   Composing with this isomorphism preserves the structural map and étaleness.
No properness, connectedness, excellence or completeness is needed.
(blueprint: lem-sfb-dvr-nodal-etale-local-form) -/
theorem exists_dvr_nodal_etale_local_form
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [Flat f] [LocallyOfFinitePresentation f]
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec R),
      IsReduced (pullback (C := Scheme) f g) ∧
        (pullback (C := Scheme) f g).IsPureDimension 1 ∧
        ∀ z : pullback (C := Scheme) f g,
          IsClosed ({z} : Set (pullback (C := Scheme) f g)) →
          ¬ ((NodalFiber.projection f Ω g).stalkMap z).hom.FormallySmooth →
          Nonempty (NodalFiber.completedLocalRing z ≃+* NodalFiber.powerSeriesQuotient Ω))
    (x : X) (hx : f x = IsLocalRing.closedPoint R) :
    ∃ (R' : CommRingCat.{u}) (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (φ : R →+* R') (π a : R') (U : Scheme.{u}) (p : U ⟶ X)
      (q : U ⟶ (StrictSemistableModel.nodal a).scheme) (x' : U),
      Function.Injective φ ∧ IsLocalHom φ ∧ Etale (Spec.map (CommRingCat.ofHom φ)) ∧
        Irreducible π ∧ (a = 0 ∨ ∃ n : ℕ, a = π ^ n) ∧
        Etale p ∧ Etale q ∧ p x' = x ∧
        p ≫ f = q ≫ (StrictSemistableModel.nodal a).baseMap ≫
          Spec.map (CommRingCat.ofHom φ) := by
  sorry

end AlgebraicGeometry
