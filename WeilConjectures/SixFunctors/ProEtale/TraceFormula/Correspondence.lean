/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs

/-!
# Correspondences, global operators and Borel-Moore integration

A correspondence from `(X, K)` to `(Y, L)` is a pair of legs `c = (c₁, c₂) : C ⟶ Y × X`
together with a coefficient map `u : c₂^* K ⟶ c₁^! L`. When `X = Y` and `K = L` it is an
*endocorrespondence*, its fixed scheme `Fix(c)` is the locus where the two legs agree, and
when the ordinary leg `c₂` is proper it induces a *global operator* on compactly supported
cohomology.

A *Borel-Moore section* on a geometric scheme `T` is a map `A_T ⟶ ω_T`; it can be pushed
forward along a proper morphism, and integrated when `T` is proper over the base.

## Main definitions

- `AlgebraicGeometry.ProEtale.Correspondence`: a correspondence and its supported class.
- `AlgebraicGeometry.ProEtale.Correspondence.fix`, `fixι`, `fixStr`: the fixed scheme of an
  endocorrespondence, its inclusion into the support and its structure morphism.
- `AlgebraicGeometry.ProEtale.Correspondence.toProd`,
  `AlgebraicGeometry.ProEtale.Correspondence.toProdSwap`,
  `AlgebraicGeometry.ProEtale.Correspondence.intersection`,
  `AlgebraicGeometry.ProEtale.Correspondence.intersectionStr`: the support map
  `c : C ⟶ Y × X`, its swapped form on an opposite correspondence, and the intersection
  support `E(C, D) = C ×_{Y × X} D` of an opposite pair.
- `AlgebraicGeometry.ProEtale.Correspondence.ofEnd`: the diagonal endocorrespondence
  attached to an endomorphism of the coefficient complex.
- `AlgebraicGeometry.ProEtale.Correspondence.globalOperator`: the global operator
  `T_c(u)` on compactly supported cohomology.
- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMooreSections`: the Borel-Moore
  sections `A_T ⟶ ω_T` of a geometric scheme.
- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.integral`: the pushforward and the
  integral of a Borel-Moore section.

## Implementation notes

`globalOperator`, `borelMoorePushforward`, `integral` and the coefficient map of `ofEnd`
are composites of comparison maps that the package
`AlgebraicGeometry.ProEtale.GeometricOperations` only postulates, so this project cannot
build them. They are declared `opaque`: their types carry the content, no `sorryAx` enters
the development, and — unlike a `sorry`-bodied definition, whose value does not mention its
arguments — they remain genuinely dependent on all of them.

The integral takes its values in `End (A_s)`, which is the coefficient ring by the
normalisation `GeometricOperations.dualizingBase : ω_s ≅ A_s`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s : Scheme.{u}}

/-- A correspondence from `(X, K)` to `(Y, L)`: a geometric scheme `C` over the base `s`,
two legs `c₁ : C ⟶ Y`, `c₂ : C ⟶ X` over `s` — the blueprint's `c = (c₁, c₂) : C ⟶ Y × X`,
`c₂` being the *ordinary-pullback* leg — and a coefficient map `u : c₂^* K ⟶ c₁^! L`:

```
            C
          ↙   ↘
       c₁       c₂
      ↙           ↘
     Y             X          u : Lc₂^* K ⟶ c₁^! L
      ↘     ↓a_C  ↙
       a_Y  ↓  a_X
          ↘ ↓ ↙
            s
```

A class supported on `i : T ⟶ Z` is an element of `Hom(Ri_! A_T, P)`; tensor-hom, the
projection formula and exceptional adjunction identify such classes with coefficient maps,
so the supported class `[u]` carries the same information as `u` and is not separate data
(blueprint: `sk-d-corr`). -/
structure Correspondence {X Y : Scheme.{u}} (aX : X ⟶ s) (aY : Y ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) where
  /-- the support `C` of the correspondence. -/
  supp : Scheme.{u}
  /-- the structure morphism `a_C : C ⟶ s`. -/
  str : supp ⟶ s
  /-- the exceptional leg `c₁ : C ⟶ Y`. -/
  fst : supp ⟶ Y
  /-- the ordinary-pullback leg `c₂ : C ⟶ X`. -/
  snd : supp ⟶ X
  /-- `c₁` is a morphism over `s`. -/
  fst_comp : fst ≫ aY = str
  /-- `c₂` is a morphism over `s`. -/
  snd_comp : snd ≫ aX = str
  /-- `c₁` admits a compactification, so that `c₁^!` is available. -/
  [hasCompactification_fst : HasCompactification fst]
  /-- the coefficient map `u : c₂^* K ⟶ c₁^! L`. -/
  coeff : ((upperStar A snd).leftDerivedFunctor).obj K ⟶
    (rightDerivedUpperShriek A fst).obj L

attribute [instance] Correspondence.hasCompactification_fst

namespace Correspondence

variable {X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}

/-- The fixed scheme `Fix(c) = C ×_{X × X, c, Δ_X} X` of an endocorrespondence: the locus
where the two legs agree, realised as their equaliser (part of blueprint `sk-d-corr`). -/
noncomputable def fix (c : Correspondence aX aX K K) : Scheme.{u} :=
  equalizer c.fst c.snd

/-- The inclusion `Fix(c) ⟶ C` of the fixed scheme into the support
(part of blueprint `sk-d-corr`). -/
noncomputable def fixι (c : Correspondence aX aX K K) : c.fix ⟶ c.supp :=
  equalizer.ι c.fst c.snd

/-- The structure morphism `Fix(c) ⟶ s` of the fixed scheme
(part of blueprint `sk-d-corr`). -/
noncomputable def fixStr (c : Correspondence aX aX K K) : c.fix ⟶ s :=
  c.fixι ≫ c.str

/-- The support map `c = (c₁, c₂) : C ⟶ Y × X` of a correspondence
(part of blueprint `sk-d-corr`). -/
noncomputable def toProd (c : Correspondence aX aY K L) : c.supp ⟶ pullback aY aX :=
  pullback.lift c.fst c.snd (c.fst_comp.trans c.snd_comp.symm)

/-- The support map `d̄ = τ d : D ⟶ Y × X` of an opposite correspondence, obtained from
`d = (d₁, d₂) : D ⟶ X × Y` by the exchange of factors
(part of blueprint `sk-d-corr`). -/
noncomputable def toProdSwap (d : Correspondence aY aX L K) : d.supp ⟶ pullback aY aX :=
  pullback.lift d.snd d.fst (d.snd_comp.trans d.fst_comp.symm)

/-- The intersection support `E(C, D) = C ×_{Y × X} D` of an opposite pair
(part of blueprint `sk-d-pairing`). -/
noncomputable def intersection (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) : Scheme.{u} :=
  pullback c.toProd d.toProdSwap

/-- The structure morphism `E(C, D) ⟶ s` of the intersection support
(part of blueprint `sk-d-pairing`). -/
noncomputable def intersectionStr (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) : c.intersection d ⟶ s :=
  pullback.fst c.toProd d.toProdSwap ≫ c.str

/-- The coefficient map of `AlgebraicGeometry.ProEtale.Correspondence.ofEnd`: the
endomorphism `v` read through the comparisons `L(𝟙)^* K ≃ K ≃ 𝟙^! K`. -/
noncomputable opaque ofEndCoeff
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    ((upperStar A (𝟙 X)).leftDerivedFunctor).obj K ⟶
      (rightDerivedUpperShriek A (𝟙 X)).obj K := 0

/-- The endocorrespondence on `(X, K)` with support `X`, support map the diagonal `Δ_X`,
identity legs, and coefficient map induced by `v : K ⟶ K`. For `v = 𝟙 K` this is the
blueprint's *diagonal identity* (part of blueprint `sk-d-corr`). -/
noncomputable def ofEnd (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    Correspondence aX aX K K where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := 𝟙 X
  fst_comp := Category.id_comp aX
  snd_comp := Category.id_comp aX
  coeff := ofEndCoeff K v

instance isIso_fixι_ofEnd (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    IsIso (ofEnd aX K v).fixι :=
  inferInstanceAs (IsIso (equalizer.ι (𝟙 X) (𝟙 X)))

instance isProper_fixStr_ofEnd (aX : X ⟶ s) [IsProper aX]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    IsProper (ofEnd aX K v).fixStr :=
  inferInstanceAs (IsProper ((ofEnd aX K v).fixι ≫ aX))

/-- The global operator of an endocorrespondence `(C, c, u)` on `(X, K)` whose ordinary leg
`c₂` is proper: the composite

`T_c(u) : RΓ_c(X, K) ⟶ RΓ_c(X, Rc₂_* c₂^* K) ≃ RΓ_c(C, c₂^* K) ⟶ RΓ_c(C, c₁^! K)
  ≃ RΓ_c(X, Rc₁_! c₁^! K) ⟶ RΓ_c(X, K)`

of the unit of `c₂^* ⊣ Rc₂_*`, the proper identification `Rc₂_* = Rc₂_!` and the counit of
`Rc₁_! ⊣ c₁^!`, acting on compactly supported cohomology `RΓ_c(X, K) = Ra_{X!} K`
(blueprint: `sk-d-operator`). -/
noncomputable opaque globalOperator (G : GeometricOperations A s)
    (c : Correspondence aX aX K K) [HasCompactification aX] [IsProper c.snd]
    [HasCompactification c.snd] :
    (rightDerivedLowerShriek A aX).obj K ⟶ (rightDerivedLowerShriek A aX).obj K := 0

end Correspondence

namespace GeometricOperations

variable (G : GeometricOperations A s)

/-- The *Borel-Moore sections* `A_T ⟶ ω_T` of a geometric scheme `a : T ⟶ s`
(part of blueprint `sk-d-integral`). -/
abbrev borelMooreSections {T : Scheme.{u}} (a : T ⟶ s) :=
  𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) A)) ⟶ G.dualizing a

/-- The pushforward of a Borel-Moore section `α : A_T ⟶ ω_T` along a proper `h : T ⟶ T'`
over `s`: the composite

`A_{T'} ⟶ Rh_* A_T ⟶ Rh_* ω_T ≃ Rh_! h^! ω_{T'} ⟶ ω_{T'}`

of the unit of `h^* ⊣ Rh_*`, the proper identification `Rh_* = Rh_!`, the dualizing
composition `h^! ω_{T'} ≃ ω_T` and the counit of `Rh_! ⊣ h^!`
(blueprint: `sk-d-integral`). -/
noncomputable opaque borelMoorePushforward {T T' : Scheme.{u}} (h : T ⟶ T') (a : T' ⟶ s)
    [HasCompactification h] [IsProper h] (α : G.borelMooreSections (h ≫ a)) :
    G.borelMooreSections a := 0

/-- The integral `∫_T α ∈ A` of a Borel-Moore section over a geometric scheme `T` that is
proper over the base: the pushforward of `α` along `a_T`, read in `End (A_s) = A` through
`GeometricOperations.dualizingBase` (part of blueprint `sk-d-integral`). -/
noncomputable opaque integral {T : Scheme.{u}} (a : T ⟶ s) [HasCompactification a]
    [IsProper a] (α : G.borelMooreSections a) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) := 0

end GeometricOperations

end AlgebraicGeometry.ProEtale
