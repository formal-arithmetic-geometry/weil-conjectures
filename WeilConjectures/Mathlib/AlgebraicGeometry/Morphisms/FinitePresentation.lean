/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# The diagonal of a morphism locally of finite presentation

We prove the cancellation property of morphisms locally of finite presentation: if `f ≫ g` is
locally of finite presentation and `g` is locally of finite type, then so is `f`
(`AlgebraicGeometry.locallyOfFinitePresentation_of_comp`, Stacks Tag 02FV).

Applying this to `Δ ≫ pullback.fst f f = 𝟙 X` shows that the diagonal of a morphism locally of
finite presentation is again locally of finite presentation
(`AlgebraicGeometry.locallyOfFinitePresentation_diagonal`). Since a diagonal is a monomorphism,
it is automatically quasi-separated, so it is of finite presentation as soon as it is
quasi-compact, that is, as soon as `f` is quasi-separated.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Cancellation for morphisms locally of finite presentation**: if `f ≫ g` is locally of
finite presentation and `g` is locally of finite type, then `f` is locally of finite
presentation. -/
@[stacks 02FV]
theorem locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f :=
  HasRingHomProperty.of_comp' (P' := @LocallyOfFiniteType)
    (fun _ _ hf hfg ↦ hfg.of_comp_finiteType _ hf) ‹_› ‹_›

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The diagonal of a morphism locally of finite presentation is locally of finite
presentation. -/
instance locallyOfFinitePresentation_diagonal [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := by
  have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)

end Diagonal

end AlgebraicGeometry
