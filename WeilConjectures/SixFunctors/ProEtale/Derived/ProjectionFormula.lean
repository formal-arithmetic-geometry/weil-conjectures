/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!

# The projection formula on the pro-étale site

Let `A` be a monoidal Grothendieck abelian coefficient category and `f : X ⟶ Y` a morphism of
schemes. This file states two pro-étale facts of the six-functor formalism:

* the direct image `Rf_*` of a separated finite-type morphism with `dim X ≤ d` preserves
  `Dctf`, shifting the Tor amplitude bound `[a, b]` to `[a, b + 2d]`;
* the *projection formula* `Rf_!(K ⊗ᴸ Lf^* L) ≅ (Rf_! K) ⊗ᴸ L` in `D(Y_proét)`.

## Implementation notes

The blueprint obtains both statements by transporting their étale counterparts along the
comparison morphism of sites `ν : X_proét ⟶ X_ét`, using that every bounded constructible
pro-étale complex is of étale origin, i.e. of the form `ν^* K'`. Neither the comparison `ν^*`
nor the étale-origin witness exists in this repository (see the implementation note of
`WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude`), so both statements are made
directly on the pro-étale site, with pro-étale bounded constructibility supplied by the
`opaque` placeholder `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`.

Following the convention of this branch, membership in `Dctf(X_proét, A)` is spelled out as the
conjunction `boundedConstructible … K ∧ torAmplitudeIn … a b K` rather than as an object of the
full subcategory, and the isomorphisms are asserted in the form `Nonempty (_ ≅ _)`, canonical
comparison maps being out of scope.

## Main definitions

- `AlgebraicGeometry.ProEtale.ProjectionFormulaStatement`: the assertion that the projection
  formula holds for a given `f`, `K` and `L`.

## Main statements

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStar_mem_dctf`: `Rf_*` carries
  `Dctf(X_proét, A)` into `Dctf(Y_proét, A)`, with Tor amplitude `[a, b] ↦ [a, b + 2d]`.
- `AlgebraicGeometry.ProEtale.projectionFormulaStatement_of_boundedConstructible`: the
  projection formula for bounded constructible complexes of finite Tor amplitude.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

open ProEtale.DerivedCategory

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-cor-sf-direct-image-ctf`: The direct image cell on the pro-étale site.

For `f : X ⟶ Y` separated of finite type with `dim X ≤ d`, the direct image `Rf_*` carries
`Dctf(X_proét, A)` into `Dctf(Y_proét, A)`: if `K` is bounded constructible with Tor amplitude
in `[a, b]`, then `Rf_* K` is bounded constructible with Tor amplitude in `[a, b + 2d]`.

Unlike on the étale side there is no restriction to complexes of étale origin: every bounded
constructible pro-étale complex is of étale origin. -/
theorem rightDerivedLowerStar_mem_dctf (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : ℕ∞)) (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (hK : boundedConstructible A X K ∧ torAmplitudeIn A X a b K) :
    boundedConstructible A Y ((R((f)_*[A])).obj K) ∧
      torAmplitudeIn A Y a (b + 2 * d) ((R((f)_*[A])).obj K) :=
  sorry

variable (f : X ⟶ Y) [HasCompactification f]

/-- The projection formula for `f : X ⟶ Y` at the pro-étale complexes `K` on `X` and `L` on `Y`:
the assertion that the canonical comparison

`Rf_!(K ⊗ᴸ Lf^* L) ⟶ (Rf_! K) ⊗ᴸ L`

is an isomorphism in `D(Y_proét)`. Since the comparison map itself is not available in this
repository, the assertion is phrased as the existence of an isomorphism between the two
objects. -/
noncomputable def ProjectionFormulaStatement
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) : Prop :=
  Nonempty ((R(f)_![A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj ((L((f)^*[A])).obj L)) ≅
    ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj K)).obj L)

/-- Blueprint `sk-thm-sf-pf-proetale`: Projection formula: the pro-étale realization.

Let `f : X ⟶ Y` be a morphism admitting a compactification, let `K` on `X` and `L` on `Y` be
bounded constructible of finite Tor amplitude. Then the projection formula holds:

`Rf_!(K ⊗ᴸ Lf^* L) ≅ (Rf_! K) ⊗ᴸ L` in `D(Y_proét)`.

In the blueprint this is obtained by transporting the étale projection formula along the site
comparison `ν^*`, which is exact and monoidal and commutes with `Lf^*` and with the
compactly-supported direct image; as `ν^*` is not formalised here, the statement is made
directly on the pro-étale site. -/
theorem projectionFormulaStatement_of_boundedConstructible
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (hK : boundedConstructible A X K ∧ finiteTorAmplitude A X K)
    (hL : boundedConstructible A Y L ∧ finiteTorAmplitude A Y L) :
    ProjectionFormulaStatement A f K L :=
  sorry

end ProEtale

end AlgebraicGeometry
