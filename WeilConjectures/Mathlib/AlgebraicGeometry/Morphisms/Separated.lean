/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# The diagonal of a separated morphism locally of finite presentation

For a separated morphism the diagonal is a closed immersion. Combined with
`AlgebraicGeometry.locallyOfFinitePresentation_diagonal` this shows that the diagonal of a
separated morphism locally of finite presentation is a closed immersion of finite presentation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The diagonal of a separated morphism of finite presentation is a closed immersion of
finite presentation.**

Mathlib has no bundled class for "of finite presentation"; a morphism is of finite presentation
if it is locally of finite presentation, quasi-compact and quasi-separated. -/
theorem Scheme.Hom.diagonal_isClosedImmersion_finitePresentation [IsSeparated f]
    [LocallyOfFinitePresentation f] :
    IsClosedImmersion (pullback.diagonal f) ∧
      LocallyOfFinitePresentation (pullback.diagonal f) ∧
      QuasiCompact (pullback.diagonal f) ∧ QuasiSeparated (pullback.diagonal f) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
