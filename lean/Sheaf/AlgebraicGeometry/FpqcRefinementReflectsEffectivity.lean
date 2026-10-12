/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.FpqcRefinementFullyFaithful

/-! Auxiliary step of effective fpqc descent, following the Stacks Project. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Effectivity descends through a refinement of singleton fpqc coverings.
Source: Stacks Project, Descent, Tag 02W3, affine-base proof, using Tag 02W0.
(blueprint: lem-galois-fpqc-refinement-reflects-effectivity)

Choose an effective object W over S for E. The canonical datum on W ×_S X has
pullback to X' canonically identified with E through the effective pullback square.
Full faithfulness of refinement descends this identification and its inverse to
maps between the canonical datum and D. Faithfulness makes their composites the
identities. The resulting isomorphism identifies V with W ×_S X and preserves
transport; hence its projection to W witnesses effectivity of D. No assumption
that h itself is fpqc is needed: both composite covers f and g are fpqc. The
identity refinement and empty base cases are included. -/
theorem fpqc_refinement_reflects_effectivity {S X X' : Scheme.{u}}
    (f : X ⟶ S) (g : X' ⟶ S) (h : X' ⟶ X)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    (hg : Presieve.singleton g ∈ Scheme.fpqcPrecoverage S) (hc : h ≫ f = g)
    {V : Over X} {V' : Over X'} (q : V'.left ⟶ V.left)
    (hq : q ≫ V.hom = V'.hom ≫ h)
    (D : Over.DescentDatum f V) (E : Over.DescentDatum g V')
    (hp : IsPullback q V'.hom V.hom h)
    (hD : Over.DescentDatum.IsBaseChange hc hq D E) (hE : E.IsEffective) :
    D.IsEffective := by
  sorry

end AlgebraicGeometry
