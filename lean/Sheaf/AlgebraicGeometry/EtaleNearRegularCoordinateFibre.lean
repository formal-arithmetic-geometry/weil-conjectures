/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.Etale.LocalDimension
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.RingTheory.MiracleFlatness
import WeilConjectures.RingTheory.FlatOfFlatClosedFiber
import Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion
import Sheaf.RingTheory.RelativeRegularEquationsBaseChange

/-!
# Étaleness near a regular coordinate fibre

Source: Stacks Project, More on Morphisms, Tag 0FUE, local flatness argument
(blueprint: lem-pur-etale-near-regular-coordinate-fibre).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A specified map from a smooth scheme to affine space is étale near an étale
regular coordinate fibre. This is a criterion for a given map, without constructing
coordinates or choosing equations.

Source: Stacks Project, More on Morphisms, Tag 0FUE, last two proof paragraphs,
using Tags 039C, 00R4 and 02GU
(blueprint: lem-pur-etale-near-regular-coordinate-fibre).

Proof. Work on affine neighbourhoods in the base and source. The map is finitely
presented by finite-presentation permanence, since its composite with affine-space
projection is smooth. On the fibre through `y`, the ambient local ring is regular,
as is the local ring of affine space. The last `b` equations remain regular after
base change because both the ambient scheme and its closed coordinate fibre are
flat over the base; the latter follows from its étale map to affine space. Taking
the quotient by this regular sequence drops the local dimension by `b` on both
sides. Étaleness of `v` equates the remaining dimensions and identifies the local
fibre as a finite separable field extension, of dimension zero. Miracle flatness
therefore makes the map on the fibre flat at `y`. The fibre criterion of flatness,
applied to the two local rings over the local base, makes the original map flat
at `y`. The map's fibre is the fibre of `v`, so is étale over the residue field.
Base change for differentials and Nakayama make the localized relative differential
module zero. The finite-presentation flat-unramified criterion gives an open
neighbourhood of `i(y)` where the specified map is étale. -/
theorem Scheme.Hom.exists_etale_open_of_regular_coordinate_fibre
    {S X Y : Scheme.{u}} (p : X ⟶ S) [Smooth p] (i : Y ⟶ X)
    [IsClosedImmersion i] (a b : ℕ)
    (h : X ⟶ AffineSpace (ULift.{u} (Fin (a + b))) S)
    (v : Y ⟶ AffineSpace (ULift.{u} (Fin a)) S) [Etale v]
    (hh : h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) = p)
    (H : IsPullback v i
      (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
        (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
          (fun _ ↦ 0) j.down)) h)
    (hreg : ∀ W : X.affineOpens,
      RingTheory.Sequence.IsWeaklyRegular Γ(X, W)
        (List.ofFn (fun j : Fin b ↦
          X.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
            (h.appTop (AffineSpace.coord S (ULift.up (Fin.natAdd a j)))))))
    (y : Y) :
    ∃ T : X.Opens, i y ∈ T ∧ Etale (T.ι ≫ h) := by
  sorry

end AlgebraicGeometry
