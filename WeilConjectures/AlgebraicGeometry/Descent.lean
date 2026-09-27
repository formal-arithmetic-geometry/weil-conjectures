/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Fpqc descent for quasi-coherent modules and for finite locally free closed subschemes

Let `{T i ⟶ T}` be an fpqc covering, i.e. a family of arrows generating a covering sieve
for `AlgebraicGeometry.Scheme.fpqcTopology`. This file states the two descent theorems
needed for the construction of the Picard scheme.

**(D1) Descending modules.** Descent data for quasi-coherent modules relative to the
covering are effectively represented by quasi-coherent modules on `T`: the comparison
functor from `T.Modules` to descent data is fully faithful on quasi-coherent objects, and
every descent datum with quasi-coherent components comes from a quasi-coherent module.
The equivalence preserves finite presentability and local freeness, and in particular
invertible modules glue to an invertible module.

**(D2) Effective closed immersions.** Given `X ⟶ T` and closed subschemes of the base
changes `X ×_T T i` which are finite locally free of degree `d` over `T i` and agree after
further base change, there is a unique closed subscheme of `X` restricting to them, and it
is finite locally free of degree `d` over `T`.

## Implementation notes

Closed subschemes are spelled as ideal sheaves (`AlgebraicGeometry.Scheme.IdealSheafData`),
which is what makes the cocycle condition of the blueprint degenerate to a plain equality:
`IdealSheafData` is a *set*, so descent data for it carry no extra structure and (D2) is a
genuine sheaf condition. Degrees are measured by `AlgebraicGeometry.Scheme.Hom.finrank`.

(D1) is stated as five separate assertions rather than through
`CategoryTheory.Functor.IsStack`: `Mathlib.CategoryTheory.Sites.Descent.IsStack` asks for
effectivity of *all* descent data, whereas what holds here is effectivity of the
quasi-coherent ones, which is not an instance of that class.

Flatness of a sheaf of modules has no name in Mathlib yet, so its preservation under the
equivalence of (D1) is not part of the statements below.

## Main statements

- `AlgebraicGeometry.bijective_toDescentData_map`,
  `AlgebraicGeometry.exists_isQuasicoherent_toDescentData_iso`,
  `AlgebraicGeometry.isFinitePresentation_of_toDescentData_iso`,
  `AlgebraicGeometry.isLocallyFree_of_toDescentData_iso` and
  `AlgebraicGeometry.isInvertible_of_toDescentData_iso`: (D1), fpqc descent for
  quasi-coherent modules.
- `AlgebraicGeometry.isSheaf_fpqc_finiteLocallyFreeSubscheme`: (D2), the sheaf condition
  for closed subschemes which are finite locally free of a fixed degree.
-/

@[expose] public section

universe w u

open CategoryTheory Opposite CategoryTheory.Bicategory

namespace AlgebraicGeometry

/-- The pseudofunctor sending a scheme `X` to its category `X.Modules` of sheaves of
modules and a morphism to the pullback functor. This is the pseudofunctor underlying
`AlgebraicGeometry.Scheme.Modules.pseudofunctor`, which also records the pushforward
functors and the adjunctions; here we only keep the contravariant part, which is the
shape required by `CategoryTheory.Pseudofunctor.DescentData`. -/
noncomputable abbrev modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Adj.forget₁

variable {T : Scheme.{u}} {ι : Type w} {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T)

/-- **Fpqc descent for modules: full faithfulness.** For an fpqc covering `{g i : T i ⟶ T}`,
the comparison functor from sheaves of modules on `T` to descent data relative to the covering
is fully faithful on quasi-coherent objects.

(blueprint: `sk-thm-picard-descent`, part (D1)) -/
theorem bijective_toDescentData_map (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (M N : modulesPseudofunctor.obj (.mk (op T)))
    (hM : (M : T.Modules).IsQuasicoherent) (hN : (N : T.Modules).IsQuasicoherent) :
    Function.Bijective ((modulesPseudofunctor.toDescentData g).map : (M ⟶ N) → _) :=
  sorry

/-- **Fpqc descent for modules: effectivity.** For an fpqc covering `{g i : T i ⟶ T}`, every
descent datum whose components are quasi-coherent comes from a quasi-coherent module on `T`.

(blueprint: `sk-thm-picard-descent`, part (D1)) -/
theorem exists_isQuasicoherent_toDescentData_iso
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsQuasicoherent) :
    ∃ M : modulesPseudofunctor.obj (.mk (op T)), (M : T.Modules).IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D) :=
  sorry

/-- **Finite presentation descends along an fpqc covering.**

(blueprint: `sk-thm-picard-descent`, part (D1)) -/
theorem isFinitePresentation_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFinitePresentation) :
    (M : T.Modules).IsFinitePresentation :=
  sorry

/-- **Local freeness descends along an fpqc covering.**

(blueprint: `sk-thm-picard-descent`, part (D1)) -/
theorem isLocallyFree_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsLocallyFree) :
    (M : T.Modules).IsLocallyFree :=
  sorry

/-- **Invertibility descends along an fpqc covering**: a compatible family of invertible
modules `ℒ i` on the `T i` glues to an invertible module `ℒ` on `T` with `ℒ|_{T i} ≅ ℒ i`.

(blueprint: `sk-thm-picard-descent`, part (D1)) -/
theorem isInvertible_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsInvertible) :
    (M : T.Modules).IsInvertible :=
  sorry

/-- **Fpqc descent for finite locally free closed subschemes.** Let `f : X ⟶ T` be a morphism
of schemes, let `{g i : T i ⟶ T}` be an fpqc covering and let `p i : X i ⟶ X`,
`q i : X i ⟶ T i` exhibit `X i` as the base change `X ×_T T i`:

```
   X' i ──── p i ────▶ X
     │                 │
   q i                 f
     │                 │
     ▼                 ▼
   T' i ──── g i ────▶ T
```

Given closed subschemes `Z i ⊆ X i`, described by ideal sheaves `I i`, which are finite
locally free of degree `d` over `T i` and whose pullbacks agree over `X i ×_X X j`, there
is a unique closed subscheme `Z ⊆ X` with `Z ×_T T i = Z i`, and `Z` is finite locally
free of degree `d` over `T`.

(blueprint: `sk-thm-picard-descent`, part (D2)) -/
theorem isSheaf_fpqc_finiteLocallyFreeSubscheme (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    {X : Scheme.{u}} (f : X ⟶ T) (d : ℕ)
    {X' : ι → Scheme.{u}} (p : ∀ i, X' i ⟶ X) (q : ∀ i, X' i ⟶ T' i)
    (hp : ∀ i, IsPullback (p i) (q i) f (g i)) (I : ∀ i, (X' i).IdealSheafData)
    (hfin : ∀ i, IsFinite ((I i).subschemeι ≫ q i))
    (hflat : ∀ i, Flat ((I i).subschemeι ≫ q i))
    (hfp : ∀ i, LocallyOfFinitePresentation ((I i).subschemeι ≫ q i))
    (hdeg : ∀ i (t : T' i), ((I i).subschemeι ≫ q i).finrank t = d)
    (hcompat : ∀ ⦃Y : Scheme.{u}⦄ ⦃i j : ι⦄ (a : Y ⟶ X' i) (b : Y ⟶ X' j),
      a ≫ p i = b ≫ p j → (I i).comap a = (I j).comap b) :
    ∃ J : X.IdealSheafData, (∀ i, J.comap (p i) = I i) ∧
      IsFinite (J.subschemeι ≫ f) ∧ Flat (J.subschemeι ≫ f) ∧
      LocallyOfFinitePresentation (J.subschemeι ≫ f) ∧
      (∀ t : T, (J.subschemeι ≫ f).finrank t = d) ∧
      ∀ J' : X.IdealSheafData, (∀ i, J'.comap (p i) = I i) → J' = J :=
  sorry

end AlgebraicGeometry
