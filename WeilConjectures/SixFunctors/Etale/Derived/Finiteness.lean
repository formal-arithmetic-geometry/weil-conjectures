/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Finiteness, perfectness, flat models and Künneth

The four finiteness inputs the purity chapter takes from the six-functor formalism:

* `Rf_*` and `Rf_!` preserve bounded constructibility, with a cohomological-dimension bound
  in terms of the fibre dimension (`sk-prop-sf-finiteness`);
* compactly supported cohomology and geometric stalks are perfect complexes of `Λ`-modules
  (`sk-prop-sf-trace-perfectness`);
* finite Tor amplitude in `[a, b]` is the same as admitting a bounded flat model concentrated
  in `[a, b]` (`sk-lem-sf-flat-model`);
* the Künneth formula and the projection formula in ordinary étale cohomology
  (`sk-prop-sf-kunneth-ordinary`).

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.finite_homology_compactlySupportedGlobalSections`
- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`
- `AlgebraicGeometry.Etale.nonempty_iso_kunneth`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of direct images.** Let `Λ` be a finite ring annihilated by an integer invertible
on the schemes in question and let `f : X ⟶ Y` be a morphism of finite-type `k`-schemes. Then
`Rf_*` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)` — separatedness of `f` is not needed — and, if
`f` is moreover separated, so does `Rf_!`, with `R^q f_! F = 0` for `q > 2e` when `e` bounds
the dimensions of the geometric fibres.

The underlying numerical input is that the torsion cohomological dimension of a finite-type
`k`-scheme of dimension `d` over a field of torsion cohomological dimension at most `c` is
bounded by `2d + c`; in particular it is `0` for the spectrum of a separably closed field. -/
theorem boundedConstructible_rightDerivedLowerStar [Finite Λ] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness and the fibre-dimension bound for `Rf_!`.** For `f : X ⟶ Y` separated of finite
type between finite-type `k`-schemes, `Rf_!` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`, and if
`e` bounds the dimensions of the geometric fibres of `f` then `R^q f_! F = 0` for `q > 2e`. -/
theorem boundedConstructible_rightDerivedLowerShriek [Finite Λ] (f : X ⟶ Y)
    [HasCompactification f] (e : ℕ)
    (_he : ∀ (Ω : Type u) (_ : Field Ω) (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ∧
      ∀ q : ℤ, (2 * e : ℤ) < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) :=
  sorry

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Perfectness of compactly supported cohomology.** Let `Λ` be a finite coefficient ring, `X`
separated of finite type over `k` with structure morphism `a_X`, and `K ∈ D^b_{ctf}(X, Λ)`.
Then `RΓ_c(X, K) = Ra_{X!} K` is a perfect complex of `Λ`-modules: it is bounded, each
cohomology module is finite, and it has finite Tor amplitude — over the Artinian local ring
`A_{E,n}` these three conditions are exactly perfectness. The derived geometric stalk
`K_{x̄} = Lx̄^* K` at any geometric point is perfect for the same reason. -/
theorem finite_homology_compactlySupportedGlobalSections [Finite Λ] (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    ∀ q : ℤ, Module.Finite Λ
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((Etale.compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) f).obj K)) :=
  sorry

/-- Blueprint `sk-lem-sf-flat-model`: Bounded flat model of finite Tor amplitude

**Finite Tor amplitude means a bounded flat model.** For `K ∈ D^b_c(X, Λ)` and integers
`a ≤ b` the following are equivalent: `K` has Tor amplitude in `[a, b]`; and `K` is isomorphic
to a bounded complex `P` of *flat* sheaves of `Λ`-modules with `P^q = 0` for `q ∉ [a, b]`.

One direction is that a bounded-above complex of flat sheaves is K-flat; the other truncates a
bounded-above free resolution and checks that the truncation is flat by the Tor criterion. -/
theorem hasTorAmplitudeIn_iff_exists_flatModel (X : Scheme.{u}) (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
        (∀ q : ℤ, ObjectProperty.flat (P.X q)) ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) :=
  sorry

/-- Blueprint `sk-prop-sf-kunneth-ordinary`: Künneth and the projection formula in ordinary
étale cohomology

**Künneth.** Let `k` be separably closed, let `n` be invertible in `k` and let `X`, `Y` be
finite-type `k`-schemes with product `X ×_k Y` and projections `p₁`, `p₂`. Then the
exterior-product map

`RΓ(X, E) ⊗^L RΓ(Y, K) ≅ RΓ(X ×_k Y, Lp₁^* E ⊗^L Lp₂^* K)`

is an isomorphism for all `E ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)` — unbounded, and with no
properness hypothesis — together with its one-proper-factor and compact-support forms; and for
`f` proper the projection formula `Rf_* E ⊗^L L ≅ Rf_*(E ⊗^L Lf^* L)` is an isomorphism. -/
theorem nonempty_iso_kunneth {W : Scheme.{u}} (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ≅
      (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) W).obj
            ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) :=
  sorry

end Etale

end AlgebraicGeometry
