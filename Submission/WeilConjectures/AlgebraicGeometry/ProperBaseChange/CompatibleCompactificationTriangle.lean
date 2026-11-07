/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
import Submission.WeilConjectures.Compactification.NagataCompactification
import Submission.WeilConjectures.Compactification.BaseChange

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Compatible geometric compactifications of a composable pair

Source: Stacks Project, More Étale Cohomology, Tag 0F7J, proof of
`lemma-shriek-composition`, first paragraph and displayed diagram
(blueprint: lem-weil-pbc-compatible-compactification-triangle).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Compatible compactifications over a prescribed compactification of the second morphism.
Source: Stacks Project, Tag 0F7J, proof of `lemma-shriek-composition`, first paragraph
(blueprint: lem-weil-pbc-compatible-compactification-triangle).

Proof: First, properness of `d.g` and its diagonal, together with qcqs permanence, makes
`d.Z` quasi-compact and quasi-separated. Second, `f ≫ d.i` is of finite type: `d.i` is a
quasi-compact open immersion, locally finite type is preserved by composition, and a map
from a quasi-compact scheme to a quasi-separated scheme is quasi-compact. Monicity of
`d.i` identifies the relative self-products for `f` and `f ≫ d.i`, so the latter is separated.
Third, apply Nagata compactification to obtain `e`. Fourth, base change `e` along `d.i`;
monicity identifies `X ×_{d.Z} Y` with `X`, with inverse maps `(id, f)` and the first
projection. The resulting source map is `c`, its projections are `e.i` and `f`, and its
proper map is the second projection. Finally, the first projection is the base change of
the quasi-compact open immersion `d.i`; composing the proper maps `e.g` and `d.g` gives
the total compactification. The pullback universal property gives the Cartesian square.

Here `e.Z`, `e.i`, `e.g` are respectively the node's `X̄`, `a`, `p`, and the two pullback
projections are `b`, `p_Y`. The conditions on `c` and the second projection state that
they compactify `f`; the final properness and factorization conditions state that
`e.i` and `e.g ≫ d.g` compactify `f ≫ g`. Quasi-compactness of `d.i` follows from
`QuasiCompact g` by `Compactification.quasiCompact_openImmersion`. -/
theorem exists_compatible_compactification_triangle
    {X Y Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (d : Compactification g) :
    ∃ e : Compactification (f ≫ d.i), QuasiCompact e.i ∧
      ∃ c : X ⟶ pullback e.g d.i,
        IsOpenImmersion c ∧ QuasiCompact c ∧
        c ≫ pullback.fst e.g d.i = e.i ∧ c ≫ pullback.snd e.g d.i = f ∧
        IsOpenImmersion (pullback.fst e.g d.i) ∧ QuasiCompact (pullback.fst e.g d.i) ∧
        IsProper (pullback.snd e.g d.i) ∧
        IsPullback (pullback.fst e.g d.i) (pullback.snd e.g d.i) e.g d.i ∧
        IsProper (e.g ≫ d.g) ∧ e.i ≫ (e.g ≫ d.g) = f ≫ g := by
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : QuasiSeparatedSpace d.Z := quasiSeparatedSpace_of_quasiSeparated d.g
  have : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let e := NagataCompactification (f ≫ d.i)
  have : QuasiCompact e.i := e.quasiCompact_openImmersion inferInstance
  have hsq : IsPullback (𝟙 X) f (f ≫ d.i) d.i :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  let c := (e.ofIsPullback hsq).i
  have : QuasiCompact c := (e.ofIsPullback hsq).quasiCompact_openImmersion inferInstance
  refine ⟨e, inferInstance, c, inferInstance, inferInstance, ?_, ?_,
    inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
    inferInstance, ?_⟩
  · exact (e.ofIsPullback_i_fst hsq).trans (Category.id_comp e.i)
  · exact e.ofIsPullback_i_snd hsq
  · rw [← Category.assoc, ← e.comm, Category.assoc, ← d.comm]

end AlgebraicGeometry
