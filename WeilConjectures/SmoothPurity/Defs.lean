/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.TateTwist.ProEtale

/-!

# Smooth purity for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime, `k` a field of characteristic `p ≠ ℓ` and `f : X ⟶ Y` a smooth morphism of
pure relative dimension `d` of separated `k`-schemes of finite type. *Smooth purity* (SGA 4,
Exposé XVIII, Théorème 3.2.5, and Bhatt–Scholze, *The pro-étale topology for schemes*,
Section 6.8, for `ℚ̄_ℓ`-coefficients) identifies the exceptional inverse image of the constant
coefficient object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the bounded constructible derived category `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of module objects over `ℚ̄_ℓ,X`.
Here `Rf^!` is `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek` (the
right adjoint of `Rf_!`, built from the compactification chosen by Nagata's theorem), `ℚ̄_ℓ,Y`
is the tensor unit of `Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` and `ℚ̄_ℓ,X(d)` is the Tate twist of
`WeilConjectures.TateTwist.ProEtale`. Since `ℓ` is invertible in `k`, no further invertibility
hypothesis is needed.

## Sorried input

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived`: the shifted
  Tate twists `ℚ̄_ℓ,X(d)[n]` are bounded constructible.

## Sorried data

`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is the purity isomorphism, stated as
a `@[no_expose]` definition with value `sorry`: it is a *chosen* isomorphism, which downstream
constructions (the trace map and Poincaré duality, see
`WeilConjectures/PoincareDuality/Instruction.tex`) use as data, and whose normalization they
inherit.

The isomorphism is not a canonical map whose invertibility could be stated as a proposition
with the tools currently available: classically it is the adjoint of the trace map
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of SGA 4, Exposé XVIII, whose construction (by reduction to
relative curves and the cycle class of the diagonal) is not formalized. Its intended
normalization and compatibilities — with composition of smooth morphisms, with base change,
with étale maps (where `d = 0` and `pur` is the identification `Rf^! = Lf^*`), and the
identification of the induced trace with the classical trace on `H^{2d}_c` of a smooth curve —
are therefore not stated here either.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]` is bounded constructible. -/
lemma boundedConstructible_tateTwistDerived (X : Scheme.{u}) (d n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((shiftFunctor _ n).obj (tateTwistDerived X ℓ d)) :=
  sorry

/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]`, as a bounded constructible complex. -/
noncomputable def boundedConstructibleTateTwist (X : Scheme.{u}) (d n : ℤ) :
    Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  ⟨(shiftFunctor _ n).obj (tateTwistDerived X ℓ d),
    boundedConstructible_tateTwistDerived ℓ X d n⟩

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
  [(boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)).IsMonoidal]

/-- **Smooth purity**: for a smooth morphism `f : X ⟶ Y` of pure relative dimension `d` of
separated `k`-schemes of finite type, the exceptional inverse image of the constant coefficient
object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. This is a chosen isomorphism:
see the module docstring. -/
@[no_expose]
noncomputable def smoothPurityIso :
    (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ k f).obj (𝟙_ _) ≅
      boundedConstructibleTateTwist ℓ X d (2 * d) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
