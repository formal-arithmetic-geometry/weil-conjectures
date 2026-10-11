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

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
separated and of finite type over `Spec k`, and all morphisms are morphisms over `Spec k`; in
particular `ℓ` is invertible on every scheme considered.

Let `f : X ⟶ Y` be a smooth morphism of pure relative dimension `d`. *Smooth purity* (SGA 4,
Exposé XVIII, Théorème 3.2.5, and Bhatt–Scholze, *The pro-étale topology for schemes*,
Section 6.8, for `ℚ̄_ℓ`-coefficients) identifies the exceptional inverse image of the constant
coefficient object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the derived category `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, the
pullback of the condensed ring `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`). Here `Rf^!` is
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek` on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (the right adjoint of `Rf_!`, built from the
compactification of `f` chosen by Nagata's theorem), `ℚ̄_ℓ,Y` is the tensor unit of
`D(Mod_{ℚ̄_ℓ,Y})`, regarded as a bounded constructible complex
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUnit`), and `ℚ̄_ℓ,X(d)` is the
Tate twist of `WeilConjectures.TateTwist.ProEtale`. The isomorphism is stated after the
inclusion `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`, which is fully faithful, so that the constructibility
of the Tate twists need not be recorded.

## Sorried input

* `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensorUnit`: the tensor unit
  `Λ_X` of `D(Mod_{Λ_X})` is bounded constructible: it is the module `Λ_X` placed in degree `0`,
  which is free of rank one.

## Sorried data

`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is the purity isomorphism, stated as a
`@[no_expose]` definition with value `sorry`: it is a *chosen* isomorphism, which downstream
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

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The constant coefficient object -/

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (X : Scheme.{u})

/-- The tensor unit `Λ_X` of `D(Mod_{Λ_X})` is bounded constructible. See the module
docstring. -/
lemma boundedConstructible_tensorUnit :
    boundedConstructible (condensedRingObj Λ X)
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)))) :=
  sorry

/-- The constant coefficient object `Λ_X`, the tensor unit of `D(Mod_{Λ_X})`, as a bounded
constructible complex. -/
noncomputable def boundedConstructibleUnit : Dᵇc(X)⟦Λ⟧ :=
  ⟨𝟙_ _, boundedConstructible_tensorUnit Λ X⟩

end Unit

/-! ### Smooth purity -/

section Purity

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]

/-- **Smooth purity**: for a smooth morphism `f : X ⟶ Y` of pure relative dimension `d` between
separated `k`-schemes of finite type, the exceptional inverse image of the constant coefficient
object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. This is a chosen isomorphism:
see the module docstring. -/
@[no_expose]
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ k f).obj
      (boundedConstructibleUnit _ Y)).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X ℓ d) :=
  sorry

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing
