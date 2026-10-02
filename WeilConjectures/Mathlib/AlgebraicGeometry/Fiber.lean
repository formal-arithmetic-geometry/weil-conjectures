/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Fiber maps of a morphism over a base

A morphism `φ : A ⟶ B` of schemes over `Y` induces, for every morphism `p : P ⟶ Y`, a morphism
`A ×_Y P ⟶ B ×_Y P` between the base changes along `p`. For `p = Y.fromSpecResidueField y` this
is a morphism `a.fiber y ⟶ b.fiber y` between the scheme-theoretic fibers over `y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {A B Y P : Scheme.{u}} {a : A ⟶ Y} {b : B ⟶ Y}

/-- The base change `A ×_Y P ⟶ B ×_Y P` along `p : P ⟶ Y` of a morphism `φ : A ⟶ B` over `Y`,
that is, the unique morphism making the diagram

```
  A ×_Y P ── fiberMap φ h p ──▶ B ×_Y P
     │    ╲                  ╱    │
     │     ╲ pullback.snd   ╱     │
     │      ▼              ▼      │
     │             P              │
     │             │ p            │
     ▼             ▼              ▼
     A ───── a ──▶ Y ◀──── b ──── B
      ╲                          ╱
       ╲───────── φ ───────────▶
```

commute. For `p = Y.fromSpecResidueField y` it is a morphism `a.fiber y ⟶ b.fiber y`. -/
noncomputable def fiberMap (φ : A ⟶ B) (h : φ ≫ b = a) (p : P ⟶ Y) :
    pullback a p ⟶ pullback b p :=
  pullback.map a p b p φ (𝟙 P) (𝟙 Y) (by simp [h]) (by simp)

end AlgebraicGeometry.Scheme.Hom
