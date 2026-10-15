/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.Variety
public import Sheaf.AlgebraicGeometry.Morphisms.Projective

/-!
# Smooth projective curves over a field

Source: the blueprint of the Weil conjectures, chapter `sec-abelian-varieties`, unit
`sk-def-av-jacobian` (blueprint: def-pc-smooth-projective-curve); Stacks Project,
Chapter 44 (Picard Schemes of Curves), `pic.tex`, `lemma-check-conditions` (Tag 0B9U);
Varieties, Tags 020D and 0A23.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsSmoothProjectiveCurve`: a curve over a field whose
  structure morphism is smooth and projective.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- (blueprint: def-pc-smooth-projective-curve) A smooth projective curve over a field `k`
consists of a curve over `k` and a smooth, projective structure morphism to `Spec k`.
Source: Stacks Project, `pic.tex`, `lemma-check-conditions` (Tag 0B9U), with the
curve convention of Varieties, Tags 020D and 0A23.
The curve, smoothness, and projectivity are those of `Scheme.Hom.IsCurveOverField`,
`AlgebraicGeometry.Smooth`, and `AlgebraicGeometry.IsProjective`, respectively. -/
class Scheme.Hom.IsSmoothProjectiveCurve (f : X ⟶ Spec (.of k)) : Prop
    extends f.IsCurveOverField, Smooth f, IsProjective f

end AlgebraicGeometry
