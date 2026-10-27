/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus
public import Sheaf.AlgebraicGeometry.SurfacePointBlowupData
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.ProjectiveNodalTower
public import WeilConjectures.Blowup.Gluing

/-! # Étale descent of one nodal point blowup

Source: Stacks Project, models.tex, Tag 0CDE (lemma-blowup-at-worst-nodal),
second and last paragraphs; Tag 0CDC (example-blowup); divisors.tex, Tag 0805.
(blueprint: lem-sfb-nodal-point-blowup-local-descent).

The stopping cases are exponents two and three. No connectedness, nonemptiness,
excellence, completeness, perfection or characteristic assumption is made.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SurfacePointBlowup

namespace AlgebraicGeometry.DvrNodal

/-- A pointed étale nodal model computes the blowup of the reduced singular point.
The equations on the two comparison squares determine the comparison maps; the
covering assertion includes every exceptional point, also for unequal residue fields.

Source: Stacks Project, models.tex, Tags 0CDE and 0CDC; divisors.tex, Tag 0805
(blueprint: lem-sfb-nodal-point-blowup-local-descent).

Proof, following the eight steps of the node:
1. The étale fibre theorem (lem-weil-pbc-etale-fibre-discrete-separable-points)
   makes u open in each reduced fibre. Intersect neighbourhoods isolating it in
   both fibres. Their inverse-image ideals are exactly the reduced point ideal.
   Restrictions remain étale by lem-weil-pbc-etale-composition-cancellation.
2. Apply thm-nagata-blowup-flat-base-change and its canonical comparison map to
   both ideals. Base change preserves étaleness. The exceptional fibre on U is
   the exceptional fibre on X tensored with κ(u) over κ(x). Surjectivity of the
   field-point map and lem-weil-pbc-surjective-base-change prove coverage.
3. By thm-nagata-global-blowup-complement, the complement is unchanged. The
   generic fibre is contained in that complement, so its induced map is an
   isomorphism, and local rings away from x are unchanged.
4. Use lem-sfb-dvr-nodal-chart-blowup-calculus over R'. Its charts have equations
   at=π, rs=π^(n-2), bh=π. The outer charts are regular. The middle is smooth
   for n=2, regular for n=3, and has exactly one nonregular point for n≥4.
   Its residue field is κ(o). The binomial geometric-fibre and monomial
   local-completion lemmas give reduced pure curves with the stated nodes.
5. The scheme case of lem-sfb-space-nodal-chart-locality transports the model
   from Spec R' to S. Apply lem-trf-nodal-family-etale-source-locality to the
   model, the common neighbourhood, and the unchanged complement, obtaining
   flatness, local finite presentation, purity and nodality on the blowup.
6. Over an algebraically closed field the étale base has point components.
   The binomial fibres are reduced; etale-proposition-etale-reduced gives
   reducedness on the cover. Faithfully flat local injections descend it.
7. By lem-sfb-etale-stalk-invariants regularity agrees across both étale legs.
   For n≥4 the inverse image of the residual model origin is Spec κ(u), since
   its residue field is κ(o). Coverage then gives exactly one nonregular point
   above x. For n=2 and n=3 there is none.
8. Restrict the common neighbourhood to the middle chart to get exponent n-2.
   The closed-point field criterion (lem-kun-closed-point-field) makes κ(x)
   finite over k; κ(u) is finite over κ(x), and κ(x⁺) embeds in κ(u).
   The finite-residue-point theorem (lem-trf-finite-residue-point-closed-in-fibre)
   makes x⁺ closed in the special fibre and hence in the total space.
-/
theorem nodal_point_blowup_local_descent
    (R R' : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    [IsDomain R'] [IsDiscreteValuationRing R']
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (φ : R →+* R') (hφ : Function.Injective φ) [IsLocalHom φ]
    [Etale (Spec.map (CommRingCat.ofHom φ))]
    (hπ' : IsLocalRing.maximalIdeal R' = Ideal.span {φ π})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X U : Scheme.{u}} (f : X ⟶ Spec R)
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hgeneric : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec R),
      IsReduced (pullback (C := Scheme.{u}) f g) ∧
      (pullback (C := Scheme.{u}) f g).IsPureDimension 1 ∧
      ∀ z : ↥(pullback (C := Scheme.{u}) f g),
        IsClosed ({z} : Set (pullback (C := Scheme.{u}) f g)) →
        (¬ ∃ W : (pullback (C := Scheme.{u}) f g).Opens, z ∈ W ∧ Smooth (W.ι ≫ pullback.snd f g)) →
          IsGeometricOrdinaryDoublePoint Ω (pullback (C := Scheme.{u}) f g) z)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hspecial : f x = IsLocalRing.closedPoint R)
    (hnotregular : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (n : ℕ) (hn : 2 ≤ n) (o : model R' (φ π) n) (ho : IsOrigin R' (φ π) n o)
    (p : U ⟶ X) (q : U ⟶ model R' (φ π) n) [Etale p] [Etale q]
    (hover : p ≫ f = q ≫ projection R' (φ π) n ≫ Spec.map (CommRingCat.ofHom φ))
    (u : U) (hux : p u = x) (huo : q u = o) :
    (∃ (V : U.Opens) (v : V.toScheme), V.ι v = u ∧
      ∃ hv : IsClosed ({v} : Set V.toScheme),
        (pointIdeal x hx).comap (V.ι ≫ p) = pointIdeal v hv ∧
        (centre R' (φ π) n).comap (V.ι ≫ q) = pointIdeal v hv ∧
        ∃ (pPlus : (pointIdeal v hv).blowup ⟶ (pointIdeal x hx).blowup)
          (qPlus : (pointIdeal v hv).blowup ⟶ (centre R' (φ π) n).blowup),
          IsPullback pPlus (pointIdeal v hv).blowupMap (pointIdeal x hx).blowupMap (V.ι ≫ p) ∧
          IsPullback qPlus (pointIdeal v hv).blowupMap (centre R' (φ π) n).blowupMap (V.ι ≫ q) ∧
          Etale pPlus ∧ Etale qPlus ∧
          ∀ y : (pointIdeal x hx).blowup,
            (pointIdeal x hx).blowupMap y = x → ∃ w, pPlus w = y) ∧
    Flat ((pointIdeal x hx).blowupMap ≫ f) ∧
    LocallyOfFinitePresentation ((pointIdeal x hx).blowupMap ≫ f) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec R),
      IsReduced (pullback (C := Scheme.{u}) ((pointIdeal x hx).blowupMap ≫ f) g) ∧
      (pullback (C := Scheme.{u}) ((pointIdeal x hx).blowupMap ≫ f) g).IsPureDimension 1 ∧
      ∀ z : ↥(pullback (C := Scheme.{u}) ((pointIdeal x hx).blowupMap ≫ f) g),
        IsClosed ({z} : Set (pullback (C := Scheme.{u}) ((pointIdeal x hx).blowupMap ≫ f) g)) →
        (¬ ∃ W : (pullback (C := Scheme.{u}) ((pointIdeal x hx).blowupMap ≫ f) g).Opens,
          z ∈ W ∧ Smooth (W.ι ≫ pullback.snd ((pointIdeal x hx).blowupMap ≫ f) g)) →
          IsGeometricOrdinaryDoublePoint Ω
            (pullback (C := Scheme.{u}) ((pointIdeal x hx).blowupMap ≫ f) g) z) ∧
    IsIso (pullback.map ((pointIdeal x hx).blowupMap ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) f
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (pointIdeal x hx).blowupMap (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
    IsIso ((pointIdeal x hx).blowupMap ∣_ (pointIdeal x hx).support.compl) ∧
    ((n = 2 ∨ n = 3) → ∀ y : (pointIdeal x hx).blowup,
      (pointIdeal x hx).blowupMap y = x →
        IsRegularLocalRing ((pointIdeal x hx).blowup.presheaf.stalk y)) ∧
    (4 ≤ n → ∃ xPlus : (pointIdeal x hx).blowup,
      (pointIdeal x hx).blowupMap xPlus = x ∧
      ¬ IsRegularLocalRing ((pointIdeal x hx).blowup.presheaf.stalk xPlus) ∧
      IsClosed ({xPlus} : Set (pointIdeal x hx).blowup) ∧
      (∀ y : (pointIdeal x hx).blowup, (pointIdeal x hx).blowupMap y = x →
        ¬ IsRegularLocalRing ((pointIdeal x hx).blowup.presheaf.stalk y) → y = xPlus) ∧
      ∃ (W : Scheme.{u}) (w : W) (a : W ⟶ (pointIdeal x hx).blowup)
        (c : W ⟶ model R' (φ π) (n - 2)),
        Etale a ∧ Etale c ∧ a w = xPlus ∧ IsOrigin R' (φ π) (n - 2) (c w) ∧
        a ≫ (pointIdeal x hx).blowupMap ≫ f =
          c ≫ projection R' (φ π) (n - 2) ≫ Spec.map (CommRingCat.ofHom φ)) ∧
    (∀ y : (pointIdeal x hx).blowup, (pointIdeal x hx).blowupMap y ≠ x →
      (IsRegularLocalRing ((pointIdeal x hx).blowup.presheaf.stalk y) ↔
        IsRegularLocalRing (X.presheaf.stalk ((pointIdeal x hx).blowupMap y)))) := by
  sorry

end AlgebraicGeometry.DvrNodal
