/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# Exceptional-adjoint admissibility on bounded constructible module objects

Let `Λ` be a commutative condensed ring, with coefficient ring objects `Λ_X = p_X^* Λ`. This
file states the conditions on the module-object exceptional adjunction
`Rf_! ⊣ Rf^!` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`) under which it is
*admissible*, and the separate uniform bound on proper direct images. They are hypotheses,
not theorems: supplying them is an additional input.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleInterval`: the full subcategory
  `D_c^{[a,b]}(X, Λ) ⊆ Dᵇc(X)⟦Λ⟧` of objects with cohomology concentrated in `[a, b]`.
- `ProEtale.CondensedRing.boundedConstructibleFiniteTor`: the full subcategory
  `D^b_ctf(X, Λ) ⊆ Dᵇc(X)⟦Λ⟧` of objects of finite Tor amplitude
  (`DerivedCategory.finiteTorAmplitude`).
- `ProEtale.CondensedRing.HasUniformAmplitude`: `Rf^!` has uniform constructible cohomological
  amplitude with bounds `c⁻ ≤ c⁺`.
- `ProEtale.CondensedRing.PreservesFiniteTor`: `Rf_!` and `Rf^!` preserve `D^b_ctf`.
- `ProEtale.CondensedRing.ExceptionalAdmissibility`: an admissibility datum, the bounds together
  with the amplitude and preservation properties.
- `ProEtale.CondensedRing.HasUniformProperCohomologicalDimensionLE`: the condition
  `FullCD(p, Λ; N)` for a proper `p`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Constructible cohomology intervals and finite Tor amplitude -/

section Intervals

variable (X : Scheme.{u})

/-- Blueprint `pur456-def-intervals-module`: Constructible cohomology intervals, module
objects.

For integers `a ≤ b`, the full subcategory `D_c^{[a,b]}(X, Λ)` of the bounded constructible
derived category `Dᵇc(X)⟦Λ⟧` of module objects over `Λ_X` whose cohomology module objects
vanish outside `[a, b]`. -/
def boundedConstructibleInterval (a b : ℤ) : ObjectProperty (Dᵇc(X)⟦Λ⟧) :=
  fun K ↦ DerivedCategory.homologyConcentratedIn a b K.obj

lemma boundedConstructibleInterval_iff (a b : ℤ) (K : Dᵇc(X)⟦Λ⟧) :
    boundedConstructibleInterval Λ X a b K ↔
      ∀ i : ℤ, (i < a ∨ b < i) → IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj) := by
  refine ⟨fun ⟨ha, hb⟩ i hi ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K.obj a).1 ha i hi
    · exact (DerivedCategory.isLE_iff K.obj b).1 hb i hi
  · exact (DerivedCategory.isGE_iff K.obj a).2 fun i hi ↦ h i (Or.inl hi)
  · exact (DerivedCategory.isLE_iff K.obj b).2 fun i hi ↦ h i (Or.inr hi)

/-- The full subcategory `D^b_ctf(X, Λ)` of the bounded constructible derived category
`Dᵇc(X)⟦Λ⟧` of module objects over `Λ_X` consisting of the objects of finite Tor amplitude:
for some `[p, q]`, `H^r(K ⊗ᴸ_{Λ_X} M) = 0` for `r ∉ [p, q]` and every module object `M` placed in
degree zero (`DerivedCategory.finiteTorAmplitude`). -/
def boundedConstructibleFiniteTor : ObjectProperty (Dᵇc(X)⟦Λ⟧) :=
  fun K ↦ DerivedCategory.finiteTorAmplitude _ K.obj

end Intervals

/-! ### Admissibility of the exceptional adjunction -/

section Admissibility

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]

/-- Blueprint `pur456-def-amplitude-module`: Uniform constructible cohomological amplitude,
module objects.

The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` of the module-object exceptional
adjunction (`ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`) has uniform
constructible cohomological amplitude with bounds `c⁻`, `c⁺` if for all integers `a ≤ b` it
sends `D_c^{[a,b]}(Y, Λ)` into `D_c^{[a + c⁻, b + c⁺]}(X, Λ)`. -/
def HasUniformAmplitude (cMinus cPlus : ℤ) : Prop :=
  ∀ (a b : ℤ), a ≤ b → ∀ K : Dᵇc(Y.left)⟦Λ⟧, boundedConstructibleInterval Λ Y.left a b K →
    boundedConstructibleInterval Λ X.left (a + cMinus) (b + cPlus)
      ((boundedConstructibleUpperShriek Λ ℓ f).obj K)

/-- Blueprint `pur456-def-preservation-module`: Preservation of the finite-Tor constructible
categories, module objects.

The module-object exceptional adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`) preserves the finite-Tor
constructible categories: `Rf_!` sends `D^b_ctf(X, Λ)` into `D^b_ctf(Y, Λ)` and `Rf^!` sends
`D^b_ctf(Y, Λ)` into `D^b_ctf(X, Λ)`. Preservation of the bounded constructible categories
themselves is part of the construction of the functors; only finite Tor amplitude is a
condition. -/
def PreservesFiniteTor : Prop :=
  (∀ K : Dᵇc(X.left)⟦Λ⟧, boundedConstructibleFiniteTor Λ X.left K →
    boundedConstructibleFiniteTor Λ Y.left ((boundedConstructibleLowerShriek Λ ℓ f).obj K)) ∧
  ∀ L : Dᵇc(Y.left)⟦Λ⟧, boundedConstructibleFiniteTor Λ Y.left L →
    boundedConstructibleFiniteTor Λ X.left ((boundedConstructibleUpperShriek Λ ℓ f).obj L)

/-- Blueprint `pur456-def-admissibility-module`: Exceptional-adjoint admissibility, module
objects.

A module-object admissibility datum for `f`: the module-object exceptional adjunction
`Rf_! ⊣ Rf^!` (`ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`, built from the
proper-adjoint instance argument), bounds `c⁻ ≤ c⁺` for which `Rf^!` has uniform constructible
cohomological amplitude, and the preservation of the finite-Tor constructible categories.
Supplying it is an additional hypothesis. -/
structure ExceptionalAdmissibility where
  /-- The lower amplitude bound `c⁻`. -/
  cMinus : ℤ
  /-- The upper amplitude bound `c⁺`. -/
  cPlus : ℤ
  cMinus_le_cPlus : cMinus ≤ cPlus
  hasUniformAmplitude : HasUniformAmplitude Λ ℓ f cMinus cPlus
  preservesFiniteTor : PreservesFiniteTor Λ ℓ f

end Admissibility

/-! ### The uniform proper-direct-image bound -/

section FullCD

variable {k : Type u} [Field k] {Z Y : Over (Spec (.of k))}

/-- Blueprint `pur456-def-fullcd-module`: A separate uniform proper-direct-image bound, module
objects.

For a proper morphism `p : Z ⟶ Y` of `k`-schemes of finite type and an integer `N ≥ 0`, the
condition `FullCD(p, Λ; N)`: for every morphism `v : Y' ⟶ Y` of `k`-schemes of finite type, with
base change `p' : Z' ⟶ Y'` of `p` (any cartesian square), and every module object `M` over
`Λ_{Z'}` placed in degree zero, `H^r(Rp'_* M) = 0` for `r > N`, with `Rp'_*` the module-object
derived direct image `ProEtale.CondensedRing.rightDerivedLowerStar`. The bound is uniform in `v`
and `M`. -/
def HasUniformProperCohomologicalDimensionLE (p : Z ⟶ Y) (N : ℕ) : Prop :=
  ∀ (Y' Z' : Over (Spec (.of k))) [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (v : Y' ⟶ Y) (v' : Z' ⟶ Z) (p' : Z' ⟶ Y'), IsPullback v'.left p'.left p.left v.left →
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z'.left) Ab.{u + 1}) (condensedRingObj Λ Z'.left))
      (r : ℤ), (N : ℤ) < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((rightDerivedLowerStar Λ p'.left).obj ((DerivedCategory.singleFunctor _ 0).obj M)))

end FullCD

end AlgebraicGeometry.ProEtale.CondensedRing
