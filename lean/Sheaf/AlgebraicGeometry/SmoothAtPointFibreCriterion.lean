/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.FormallySmooth

/-!
# Pointwise smoothness from a smooth fibre

Source: Stacks Project, Morphisms, Tag 01V9, `lemma-smooth-at-point`, equivalence (1) and (2)
(blueprint: lem-trf-smooth-at-point-fibre-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a locally finitely presented morphism flat at `x`, smoothness on a neighbourhood
of `x` is equivalent to smoothness of the scheme-theoretic fibre near its canonical point
`f.asFiber x`. Flatness is imposed only on the stalk map at this point.
Source: Stacks Project, Morphisms, Tag 01V9, `lemma-smooth-at-point`, (1) iff (2)
(blueprint: lem-trf-smooth-at-point-fibre-criterion).

Proof:
1. Given a smooth open neighbourhood `U` of `x`, apply `sbc-lem-smooth-criterion` to
   `U.ι ≫ f`. Its fibre is smooth. The open-fibre-product identification
   (`lem-weil-pbc-open-fibre-product`, `def-pc-scheme-fibre`) identifies this fibre with
   the open above `U` in `f.fiber (f x)`, containing `f.asFiber x`.
2. Conversely choose affine neighbourhoods `W = Spec A` of `x` and `V = Spec R` of `f x`
   with `f(W) ⊆ V` and `A` finitely presented over `R`
   (`def-sbc-locally-finite-presentation`). Write `q` for `x` and `p` for its contraction.
   The affine Spec square and stalk-localization identifications
   (`lem-weil-pbc-affine-opens-induced-ring-map-spec-square`,
   `lem-weil-pbc-affine-open-stalk-localization`, `lem-weil-pbc-spec-map-stalk-localization`)
   identify the given flat stalk map with `R_p → A_q`.
3. Put `k = κ(p)` and `F = A ⊗[R] k`. The residue-field identification and affine and open
   fibre-product lemmas (`lem-weil-pbc-spec-residue-field-identification`,
   `lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-open-fibre-product`) identify
   `Spec F` with the open fibre above `W`. The point over `x` is the kernel `Q` of the
   canonical map `F → κ(q)`, since it contracts to `q` (`def-pc-scheme-fibre`). Inside the
   assumed smooth fibre neighbourhood choose a basic open `D(h)` containing `Q`.
   Principal localization identifies it with `Spec F_h`
   (`lem-weil-pbc-principal-localization-open-immersion`). Open immersion followed by
   a smooth map is smooth (`lem-pc-open-immersion-smooth-composition`), so `k → F_h`
   is smooth (`lem-weil-pbc-smooth-ring-map-iff-smooth-affine`). Thus `k → F` is smooth
   at `Q` (`def-weil-pbc-singular-ideal`).
4. Apply `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime` to `R → A`, with finite
   presentation witnessed by localization at `1`, the flat local map of step 2 and the
   smooth fibre of step 3. Unpack `def-weil-pbc-singular-ideal` to obtain `g ∉ q` with
   `R → A_g` smooth.
5. Principal localization and the smooth affine comparison identify `Spec A_g` with
   an open neighbourhood `W_g` of `x`, smooth over `V`. Its composite to `S` is locally
   finitely presented (`def-sbc-locally-finite-presentation`). For formal smoothness,
   any first order thickening of affine `S`-schemes has the same underlying points
   (`def-sbc-first-order-thickening`), so a lifting problem whose closed restriction
   maps into `W_g` factors through `V` (`def-weil-open-immersion`). Formal smoothness
   over `V` supplies the lift over `S` (`def-sbc-formally-smooth`). Hence `W_g → S` is
   smooth (`def-sbc-smooth-morphisms`), giving the required neighbourhood. -/
theorem smooth_at_point_iff_smooth_fibre_at_point
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X)
    (hflat : (f.stalkMap x).hom.Flat) :
    (∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) ↔
      ∃ V : (f.fiber (f x)).Opens,
        f.asFiber x ∈ V ∧ Smooth (V.ι ≫ f.fiberToSpecResidueField (f x)) := by
  sorry

end AlgebraicGeometry
