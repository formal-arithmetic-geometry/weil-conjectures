/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Fpqc descent of local quasi-finiteness

Source: Stacks Project, Descent, Tag 02VI, `lemma-descending-property-quasi-finite`,
the descending direction of the locally quasi-finite assertion
(blueprint: lem-sfb-scheme-lqf-fpqc-descent).

The predicate `Scheme.Hom.IsLocallyQuasiFinite` includes local finite type as in Tag 01TD.
The fpqc hypothesis is on the family and does not require its individual maps to be
quasi-compact.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- Local quasi-finiteness in the Stacks sense descends along any fpqc covering family.
Source: Stacks Project, Descent, Tag 02VI, `lemma-descending-property-quasi-finite`
(blueprint: lem-sfb-scheme-lqf-fpqc-descent).

Proof:
1. Apply `locallyOfFiniteType_of_isLocallyQuasiFinite`
   (lem-weil-pbc-lqf-locally-finite-type) to every second projection. Then apply
   `AlgebraicGeometry.locallyOfFiniteType_of_fpqcCover`
   (lem-weil-pbc-fpqc-descend-locally-finite-type, Tag 02KX) to obtain local finite type of `f`.
2. Base change the fpqc family along `f` by `Precoverage.mem_coverings_of_isPullback`
   (lem-galois-fpqc-covering-base-change, Tag 022D(3)). The first projections form an fpqc
   cover of `X`; their joint surjectivity (def-weil-pbc-fpqc-covering, Tag 022B) lifts each
   point `x` to a point `x'` of some `pullback f (g i)`.
3. The hypothesis at `i` gives quasi-finiteness of the second projection at `x'`
   (pqf-def-quasifinite, Tag 01TD). Apply the reverse implication of
   lem-sfb-scheme-quasifinite-at-base-change (Tag 01TM(1)), using local finite type from
   step 1, to obtain quasi-finiteness of `f` at `x`. This holds for every point, which is
   `f.IsLocallyQuasiFinite` by pqf-def-quasifinite. For empty `X` there is no point to check. -/
theorem isLocallyQuasiFinite_of_fpqcCover
    {X T : Scheme.{u}} (f : X ⟶ T) {I : Type v} (T' : I → Scheme.{u})
    (g : ∀ i : I, T' i ⟶ T)
    (hcover : Presieve.ofArrows T' g ∈ Scheme.fpqcPrecoverage T)
    (h : ∀ i : I, (pullback.snd f (g i)).IsLocallyQuasiFinite) :
    f.IsLocallyQuasiFinite := by
  sorry

end AlgebraicGeometry.Scheme.Hom
