module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Length

/-!
# Evaluated differentials and their torsion length

Source: BLR, Neron Models, 3.3, printed p.65, and 3.6, printed p.79.
(blueprint: def-sfb-valued-point-differential-defect)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- The evaluated differential module `A ⊗[B, φ] Ω[B/R]` at an algebra-valued point.
Source: BLR 3.3, printed p.65; 3.6, printed p.79.
(blueprint: def-sfb-valued-point-differential-defect) -/
noncomputable def evaluatedDifferentials {R : Type u} {B : Type v} {A : Type w}
    [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
    (φ : B →ₐ[R] A) : ModuleCat A :=
  (ModuleCat.extendScalars φ.toRingHom).obj (ModuleCat.of B (KaehlerDifferential R B))

/-- The torsion submodule of the evaluated differentials. Over a domain, its elements
are exactly those annihilated by some nonzero scalar.
Source: BLR 3.3, printed p.65; 3.6, printed p.79.
(blueprint: def-sfb-valued-point-differential-defect) -/
noncomputable def evaluatedDifferentialTorsion {R : Type u} {B : Type v} {A : Type w}
    [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
    (φ : B →ₐ[R] A) : Submodule A (evaluatedDifferentials φ) :=
  Submodule.torsion A (evaluatedDifferentials φ)

/-- The (possibly infinite) length of the torsion part of the evaluated differentials.
Source: BLR 3.3, printed p.65; 3.6, printed p.79.
(blueprint: def-sfb-valued-point-differential-defect) -/
noncomputable def valuedPointDifferentialDefect {R : Type u} {B : Type v} {A : Type w}
    [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
    (φ : B →ₐ[R] A) : ℕ∞ :=
  Module.length A (evaluatedDifferentialTorsion φ)

end Algebra
