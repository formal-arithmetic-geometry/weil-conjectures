/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Base-open factorization detected by a surjective scheme chart

Source: Stacks Project, Properties of Spaces, Tag 03FY, final proof sentence;
Spaces, Tag 025V; Schemes, Tags 01HI and 01IK
(blueprint: lem-a1-surjective-chart-base-open-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a representable surjective scheme chart maps into a base open, the algebraic
space factors uniquely through that open. The scheme-test lifts are the underlying
scheme maps of `yoneda.preimage (a ≫ b)`; their uniqueness and compatibility are explicit.
The structural map to `h_S` is the unique map to the represented terminal object of
`Over S`. Neither the chart nor the open is required to be affine, and the chart need
not be étale.

Source: Stacks Project, Properties of Spaces, Tag 03FY, final proof sentence, expanded
using Spaces, Tag 025V, and Schemes, Tags 01HI and 01IK
(blueprint: lem-a1-surjective-chart-base-open-factorization).

Proof:
1. For a scheme test `a : h_T → Y`, apply the scheme-test definition `IsSurjective q`
   of `def-trf-algebraic-space` to represent `h_T ×_Y h_U` by a scheme `P` over `S`.
   Its projection `p : P → T` is surjective; the other projection gives `v : P → U`
   by Yoneda, and the structural maps satisfy `p ≫ T.hom = v ≫ U.hom`.
2. Write `U.hom = c ≫ j`. Every point `t` of `T` lifts along `p` to a point `z` of
   `P`, so its image in `S` is `j (c (v z))`. Thus `T.hom` has image in `j`.
3. Apply `lem-weil-pbc-morphism-factors-through-open-subscheme`, namely
   `IsOpenImmersion.lift`, `lift_fac`, and `lift_uniq`, to obtain the unique lift
   `b_a : T.left → W`.
4. For `r : T' → T`, both `b_(h_r ≫ a)` and `r.left ≫ b_a` compose with `j` to
   `T'.hom`; uniqueness of open factorization identifies them.
5. For a section `y` of `Y(T)`, use its Yoneda map `a_y : h_T → Y` and set
   `b_T(y) = b_(a_y)`. Step 4 gives naturality. Step 3 gives the structural
   factorization and its uniqueness on every section. Yoneda identifies the
   resulting test lift with `yoneda.preimage (a ≫ b)`, giving all displayed clauses. -/
theorem surjective_chart_base_open_factorization {S : Scheme.{u}}
    (Y : AlgebraicSpace S) (U : Over S) (q : yoneda.obj U ⟶ Y.obj.obj)
    (hq : IsSurjective q) (W : Scheme.{u}) (j : W ⟶ S) [IsOpenImmersion j]
    (hU : ∃ c : U.left ⟶ W, c ≫ j = U.hom) :
    ∃ b : Y.obj.obj ⟶ yoneda.obj (Over.mk j),
      b ≫ yoneda.map (Over.mkIdTerminal.from (Over.mk j)) =
        ((Over.mkIdTerminal (X := S)).isTerminalObj yoneda _).from Y.obj.obj ∧
      (∀ b' : Y.obj.obj ⟶ yoneda.obj (Over.mk j),
        b' ≫ yoneda.map (Over.mkIdTerminal.from (Over.mk j)) =
          ((Over.mkIdTerminal (X := S)).isTerminalObj yoneda _).from Y.obj.obj → b' = b) ∧
      (∀ (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj),
        (yoneda.preimage (a ≫ b)).left ≫ j = T.hom ∧
        ∀ c : T.left ⟶ W, c ≫ j = T.hom → c = (yoneda.preimage (a ≫ b)).left) ∧
      (∀ (T T' : Over S) (r : T' ⟶ T) (a : yoneda.obj T ⟶ Y.obj.obj),
        (yoneda.preimage ((yoneda.map r ≫ a) ≫ b)).left =
          r.left ≫ (yoneda.preimage (a ≫ b)).left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
