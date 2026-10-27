/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Formal étaleness on compatible étale scheme charts

Source: Stacks Project, More on Morphisms of Spaces, Tag 04GD, equivalence (1) and (2),
with formal étaleness as in definition-formally-smooth-etale-unramified
(blueprint: lem-sfb-formally-etale-space-chart-locality).

The affine first order unique lifting properties are expanded on both sides.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Formal étaleness is equivalent to the unique affine first order lifting property
on every compatible pair of representable étale scheme charts.
Source: Stacks Project, More on Morphisms of Spaces, Tag 04GD, (1) iff (2)
(blueprint: lem-sfb-formally-etale-space-chart-locality).

Proof:
1. A representable étale map has unique lifts across first order scheme thickenings:
base change a lifting square to obtain an étale scheme over the target test scheme.
The initial lift is a section on the thickening. The equivalence of étale scheme
categories across thickenings [lem-sfb-space-thickening-etale-scheme-equivalence]
is fully faithful, so that section extends uniquely. First order thickenings are
thickenings [def-sbc-first-order-thickening].
2. If `f` has the lifting property, fix a compatible diagram `u ≫ f = h ≫ v`.
Lift first along `f` and then along `u` using step 1. Uniqueness for `v` forces the
resulting map to lie over the prescribed map to `V`. Uniqueness for `f` and `u`
proves uniqueness for `h`. The diagram need not be cartesian.
3. Conversely choose a surjective étale atlas `V → Y`. Compatible charts with
surjective `U → X` exist by [lem-sfb-unramified-etale-compatible-charts]. The
hypothesis gives unique lifts for `h`. Step 1 for `v` and then lifting for `h`
give unique lifts for the composite `U → Y`.
4. For a square for `f`, pull `U → X` back to the initial affine test scheme `T₀`.
Lift this étale scheme across `T₀ → T` using the equivalence in step 1. Its lift
`W → T` is surjective since its reduction is surjective and a thickening is
surjective. Cover `W` by affine opens. Their reductions are affine square-zero
thickenings: locally the defining ideal is `IC`, with `(IC)^2 = 0`. These opens
form a jointly surjective étale, hence fppf, covering of `T`, using étale
composition [lem-weil-pbc-etale-composition-cancellation] and [def-pc-fppf-site].
5. Two lifts for `f` pull back on this affine covering to lifts along `U → X`
by step 1. They agree by uniqueness for `U → Y` from step 3. Sheaf separatedness
[def-weil-pbc-sites-and-cohomology] gives equality on `T`. This uniqueness extends
to nonaffine tests by affine open restriction and the same separatedness.
6. Step 3 gives lifts on the affine covering of step 4. On possibly nonaffine
overlaps they agree by step 5. The fppf sheaf equalizer glues them to `T → X`.
Separatedness for `Y` verifies its composite with `f`, and separatedness for `X`
on the base-changed covering verifies its reduction. Step 5 gives uniqueness.
This proves the converse without separation or finiteness assumptions on `f`. -/
theorem unique_affine_thickening_lifts_iff_on_etale_charts
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (∀ (T₀ T : Over S) [IsAffine T₀.left] [IsAffine T.left]
      (j : T₀ ⟶ T), IsFirstOrderThickening j.left →
      ∀ (a₀ : yoneda.obj T₀ ⟶ X.obj.obj) (b : yoneda.obj T ⟶ Y.obj.obj),
        a₀ ≫ f.hom.hom = yoneda.map j ≫ b →
        ∃! a : yoneda.obj T ⟶ X.obj.obj,
          yoneda.map j ≫ a = a₀ ∧ a ≫ f.hom.hom = b) ↔
    (∀ (U V : Over S) (u : yoneda.obj U ⟶ X.obj.obj)
      (v : yoneda.obj V ⟶ Y.obj.obj) (h : U ⟶ V),
      IsEtale u → IsEtale v → u ≫ f.hom.hom = yoneda.map h ≫ v →
      ∀ (T₀ T : Over S) [IsAffine T₀.left] [IsAffine T.left]
        (j : T₀ ⟶ T), IsFirstOrderThickening j.left →
        ∀ (a₀ : T₀ ⟶ U) (b : T ⟶ V), a₀ ≫ h = j ≫ b →
          ∃! a : T ⟶ U, j ≫ a = a₀ ∧ a ≫ h = b) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
