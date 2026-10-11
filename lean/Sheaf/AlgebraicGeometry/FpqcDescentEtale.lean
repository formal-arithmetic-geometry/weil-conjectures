/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Etale descent along fpqc coverings

Source: Stacks Project, Descent, Lemma Tag 02VN
(blueprint: lem-galois-fpqc-descend-etale).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-galois-fpqc-descend-etale) Stacks Project, Descent, Lemma 02VN,
descent direction: if every base change of `f` along an fpqc covering is etale, then
`f` is etale. Each base change is etale, i.e. locally of finite presentation, flat and
unramified (Morphisms 02GV). Flatness descends along the covering (Descent 02L2), local
finite presentation descends (Descent 02KY), and being unramified descends (Descent
02VM). Hence `f` is flat, locally of finite presentation and unramified, i.e. etale. -/
theorem etale_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, Etale (pullback.snd f (g i))) : Etale f := by
  sorry

end AlgebraicGeometry
