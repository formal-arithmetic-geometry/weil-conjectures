/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.TraceFormula.StrictSemistableCurve
public import Sheaf.AlgebraicGeometry.NodalPointEtaleLocality
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Pointed nodal charts over a DVR with a fixed uniformizer

Source: Stacks Project, models.tex, Tag 0CDD, lemma-etale-local-at-worst-nodal,
and Tag 0CDE, first proof paragraph (blueprint: lem-sfb-trait-nodal-etale-dvr-model).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nodal family over a DVR has pointed étale charts with parameter zero or a power of
its fixed uniformizer. When its generic fibre is smooth, the same chart can have nonzero
parameter; at a nonsmooth special-fibre point its exponent is positive. The structure map
of `U` to `Spec R'` is the displayed map `q` followed by the standard model projection.

Source: Stacks Project, models.tex, Tag 0CDD, lemma-etale-local-at-worst-nodal,
and Tag 0CDE, first proof paragraph (blueprint: lem-sfb-trait-nodal-etale-dvr-model).

Proof:
1. Apply lem-sfb-dvr-nodal-etale-local-form at `x`. The geometric hypotheses imply its
   condition at closed geometric points. Obtain an injective local étale DVR extension,
   a pointed common étale neighbourhood, and parameter zero or a power of a uniformizer
   `π'` of the extension. No quasi-compactness is required.
2. By lem-weil-pbc-etale-prime-generates-maximal, localizing at the maximal ideal of
   `R'` gives its maximal ideal as the extension of the maximal ideal of `R`. Since
   localization of a local ring at its maximal ideal is itself, the image of `π`
   generates this ideal and is a uniformizer (def-sc-discrete-valuation-ring).
3. The two uniformizers satisfy `π' = ε * φ π` for a unit `ε`. Rescale the first
   coordinate by `ε⁻ⁿ` to turn `ab = π'^n` into `ab = (φ π)^n`. The inverse rescales
   by `ε^n`. Composition with this model isomorphism preserves étaleness by
   lem-weil-pbc-etale-composition-cancellation. The zero parameter is unchanged.
4. In the model `ab = c`, the opens `D(a)` and `D(b)` are Laurent affine lines:
   eliminate one coordinate using the other. They are smooth over `R'`. Directly,
   lifting a unit across a square-zero ideal lifts a map from the Laurent algebra;
   if lifts satisfy `t₀s₀ = 1+i`, replace `s₀` by `s₀(1-i)`. This is the lifting
   condition of def-sbc-smooth-morphisms. For `c=1` these opens cover the model.
5. The extension `Spec R' → Spec R` is smooth by
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres. Composition is smooth by
   lem-trf-smooth-composition. Apply lem-trf-etale-source-smoothness to `q` and `p`.
   If `x` is nonsmooth, its image avoids both coordinate opens, so an exponent
   zero is impossible. The image is the origin of the special fibre.
6. In the persistent model `ab=0`, the point `(a,b)` on the generic fibre is not
   smooth. Over `F=Frac R'`, map both coordinates to `e` in `F[e]/(e²)`. This map
   does not lift to `F[e]/(e³)`, since any lifts have nonzero product `e²`.
   The same obstruction works on every neighbourhood of `(a,b)`.
7. Suppose the generic fibre is smooth. If the image of `u` in a zero-parameter
   model is in a coordinate open, restrict to it and replace the chart by `ab=1`.
   Otherwise it is the special origin. The open image of `q` contains its
   generization `(a,b)`, by lem-weil-pbc-flat-lfp-open. Lift that point to `U`.
   The generic-fibre maps are étale by lem-weil-pbc-etale-base-change-finite-limits.
   Apply lem-trf-etale-source-smoothness twice: smoothness of the generic fibre
   of `X` would imply smoothness of the model at `(a,b)`, contradicting step 6.
   Thus a nonzero parameter can be chosen; step 5 gives positive exponent at a
   nonsmooth `x`. Restrictions preserve the chosen point and compatibility maps.
-/
theorem exists_trait_nodal_etale_dvr_model
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [Flat f] [LocallyOfFinitePresentation f]
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback f g) ∧ (pullback f g).IsPureDimension 1)
    (hnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)) (z : ↥(pullback (C := Scheme.{u}) f g)),
      z ∉ (pullback.snd f g).smoothLocus →
        Nonempty
          (@AlgEquiv Ω
            (AdicCompletion (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk z))
              ((pullback f g).presheaf.stalk z))
            (MvPowerSeries (Fin 2) Ω ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})
            _ _ _ ((pullback.snd f g).completedLocalScalarMap z).toAlgebra inferInstance))
    (x : X) (hx : f x = IsLocalRing.closedPoint R) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (φ : R →+* R'),
      Function.Injective φ ∧ IsLocalHom φ ∧ Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      Irreducible (φ π) ∧
      ∃ (c : R') (U : Scheme.{u}) (p : U ⟶ X)
        (q : U ⟶ (StrictSemistableModel.nodal (A := .of R') c).scheme) (u : U),
        Etale p ∧ Etale q ∧ p u = x ∧
        p ≫ f = q ≫ (StrictSemistableModel.nodal (A := .of R') c).baseMap ≫
          Spec.map (CommRingCat.ofHom φ) ∧
        (c = 0 ∨ ∃ n : ℕ, c = (φ π) ^ n) ∧
        (Smooth (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) →
          ∃ n : ℕ, c = (φ π) ^ n ∧ (x ∉ f.smoothLocus → 1 ≤ n)) := by
  sorry

end AlgebraicGeometry
