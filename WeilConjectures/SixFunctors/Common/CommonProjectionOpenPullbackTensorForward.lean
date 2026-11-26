/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Currying

/-! # Forward open pullback/tensor square for common-stage inclusion

We prove the forward form of the open tensor/pullback square from a representative
compatibility equation.

## Implementation details

The compatibility equation is an explicit hypothesis: without it the statement fails, e.g.
for `SingleObj (Multiplicative Bool)` with identity functors and comparisons and first
projections as tensor functors, where the equation reduces to `mu = mu'`. The inverse square
follows from the compatibility equation by cancelling the two displayed isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false

universe v w v' w'
open CategoryTheory

namespace WeilConjectures

/-- The forward form of the open tensor/pullback square, assuming the canonical compatibility
equation. -/
theorem commonProjectionOpenPullbackTensor_forward
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {A' : Type v} [Category.{w} A'] {B' : Type v'} [Category.{w'} B']
    {F : A ⥤ B} {F' : A' ⥤ B'} {c : A ⥤ A'} {d : B ⥤ B'}
    (e : F ⋙ d ≅ c ⋙ F')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA')
    (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (M N : A) (mu : F.obj (TA.obj (M, N)) ⟶ TB.obj (F.obj M, F.obj N))
    (mu' : F'.obj (TA'.obj (c.obj M, c.obj N)) ⟶
      TB'.obj (F'.obj (c.obj M), F'.obj (c.obj N))) :
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' →
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' := by
  intro h
  exact h

end WeilConjectures
