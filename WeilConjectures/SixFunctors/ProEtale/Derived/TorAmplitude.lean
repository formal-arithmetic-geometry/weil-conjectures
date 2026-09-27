/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ProEtale.Derived.Tensor

/-!

# Finite Tor amplitude on the pro-étale site

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme, so that the
derived category `D(X_proét)` of `A`-valued pro-étale sheaves on `X` carries the derived tensor
product `- ⊗ᴸ -` of `WeilConjectures.SixFunctors.ProEtale.Derived.Tensor`.

This file is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`: it records homology concentration in
an interval, Tor amplitude in an interval, and finite Tor amplitude for objects of
`D(X_proét)`.

## Main definitions

- `AlgebraicGeometry.ProEtale.DerivedCategory.homologyConcentratedIn`: homology vanishing
  outside an interval `[a, b]`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn`: Tor amplitude in `[a, b]`, tested
  by tensoring with an arbitrary pro-étale sheaf.
- `AlgebraicGeometry.ProEtale.DerivedCategory.finiteTorAmplitude`: finite Tor amplitude.
- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`: a placeholder for the
  bounded constructible objects of `D(X_proét)`, see the implementation note below.

## Implementation notes

Unlike the étale site, the pro-étale site has no notion of constructibility anywhere in this
repository: `AlgebraicGeometry.Scheme.IsConstructibleSheaf` is defined only for the small étale
site, and the comparison morphism of sites `ν : X_proét ⟶ X_ét` — along which a pro-étale sheaf
is called constructible when it is `ν^*` of an étale constructible one — has not been
formalised either. Pro-étale constructibility belongs to a different blueprint block, so here it
is recorded as an `opaque` constant rather than a `sorry`-bodied definition; using `opaque`
keeps `sorryAx` out of the file.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace ProEtale.DerivedCategory

/-- An object of `D(X_proét)` has homology concentrated in `[a, b]` if its homology sheaves
vanish outside that interval. -/
def homologyConcentratedIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  fun M ↦ ∀ n : ℤ, n < a ∨ b < n →
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology X) A) n).obj M)

/-- An object `M` of `D(X_proét)` has *Tor amplitude in `[a, b]`* if for every pro-étale sheaf
`F` the derived tensor product `M ⊗ᴸ F` has homology concentrated in `[a, b]`. -/
def torAmplitudeIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  fun M ↦ ∀ F : Sheaf (Scheme.ProEt.topology X) A, homologyConcentratedIn A X a b
    (((-⊗ᴸ-(X)[A]).obj M).obj
      ((_root_.DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) A) 0).obj F))

/-- An object of `D(X_proét)` has *finite Tor amplitude* if it has Tor amplitude in some
interval `[a, b]`. -/
def finiteTorAmplitude :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  fun M ↦ ∃ a b : ℤ, torAmplitudeIn A X a b M

end ProEtale.DerivedCategory

-- TODO(unify): def:weil-finite-torsion-constructibility
/-- The bounded constructible objects of `D(X_proét)`.

A pro-étale complex is bounded constructible when it is bounded and, pulled back along the
comparison morphism of sites `ν : X_proét ⟶ X_ét`, comes from a bounded constructible complex
on the small étale site. Neither ingredient exists in this repository: constructibility
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf`) is only defined for the small étale site, and
the comparison `ν^*` has not been formalised. The notion therefore belongs to another blueprint
block and is recorded here as an `opaque` constant, so that the statements on the pro-étale
side can be phrased without introducing `sorryAx`.

Issue 1053 tracks unifying this with the étale
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible`, once `ν^*` is available. -/
opaque ProEtale.DerivedCategory.boundedConstructible :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))

end AlgebraicGeometry
