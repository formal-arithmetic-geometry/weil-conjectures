/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

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

- `AlgebraicGeometry.ProEtale.Correspondence` (blueprint `sk-d-corr`)
- `AlgebraicGeometry.ProEtale.Correspondence.globalOperator` (blueprint `sk-d-operator`)
- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward`
  (blueprint `sk-d-integral`)
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s : Scheme.{u}}

/-- Blueprint `sk-d-corr`: Correspondences and supported classes.

A correspondence from `(X, K)` to `(Y, L)` consists of a geometric scheme `C` over the base
`s`, two legs `c₁ : C ⟶ Y` and `c₂ : C ⟶ X` over `s` — the blueprint's
`c = (c₁, c₂) : C ⟶ Y × X` — and a coefficient map `u : c₂^* K ⟶ c₁^! L`. The leg `c₂` is
the *ordinary-pullback* leg.

The blueprint also records that a class supported on `i : T ⟶ Z` is an element of
`Hom(Ri_! A_T, P)`, and that tensor-hom, the projection formula and exceptional adjunction
identify such classes with coefficient maps, so that the supported class `[u]` carries the
same information as `u`; the correspondence itself is the data above. All supports and
structure maps remain part of the data. -/
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

variable {X : Scheme.{u}} {aX : X ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}

/-- The fixed scheme `Fix(c) = C ×_{X × X, c, Δ_X} X` of an endocorrespondence: the locus
where the two legs agree, realised as their equaliser. -/
noncomputable def fix (c : Correspondence aX aX K K) : Scheme.{u} :=
  equalizer c.fst c.snd

/-- The inclusion `Fix(c) ⟶ C` of the fixed scheme into the support. -/
noncomputable def fixι (c : Correspondence aX aX K K) : c.fix ⟶ c.supp :=
  equalizer.ι c.fst c.snd

/-- The structure morphism `Fix(c) ⟶ s` of the fixed scheme. -/
noncomputable def fixStr (c : Correspondence aX aX K K) : c.fix ⟶ s :=
  c.fixι ≫ c.str

/-- Blueprint `sk-d-operator`: Global operators.

For an endocorrespondence `(C, c, u)` on `(X, K)` whose ordinary leg `c₂` is proper, the
unit of `c₂^* ⊣ Rc₂_*`, the proper identification `Rc₂_* = Rc₂_!` and the counit of
`Rc₁_! ⊣ c₁^!` compose to a global operator

`T_c(u) : RΓ_c(X, K) ⟶ RΓ_c(X, Rc₂_* c₂^* K) ≃ RΓ_c(C, c₂^* K) ⟶ RΓ_c(C, c₁^! K)
  ≃ RΓ_c(X, Rc₁_! c₁^! K) ⟶ RΓ_c(X, K)`

on compactly supported cohomology. The composite is not constructed here: several of its
steps are comparison maps that the package
`AlgebraicGeometry.ProEtale.GeometricOperations` only postulates, so the definition is
stated and left with a `sorry` body. -/
noncomputable def globalOperator (G : GeometricOperations A s)
    (c : Correspondence aX aX K K) [HasCompactification aX] [IsProper c.snd]
    [HasCompactification c.snd] :
    (compactlySupportedGlobalSections A aX).obj K ⟶
      (compactlySupportedGlobalSections A aX).obj K :=
  sorry

end Correspondence

namespace GeometricOperations

variable (G : GeometricOperations A s)

/-- Blueprint `sk-d-integral`: Borel-Moore sections and integration.

A *Borel-Moore section* on a geometric scheme `a : T ⟶ s` is a morphism `α : A_T ⟶ ω_T` in
the derived category, that is, an element of
`𝟙_ (D(T, A)) ⟶ G.dualizing a`. For a proper `h : T ⟶ T'` over `s` its pushforward
`h_* α` is the composite

`A_{T'} ⟶ Rh_* A_T ⟶ Rh_* ω_T ≃ Rh_! h^! ω_{T'} ⟶ ω_{T'}`

built from the unit of `h^* ⊣ Rh_*`, the proper identification `Rh_* = Rh_!`, the
dualizing composition `h^! ω_{T'} ≃ ω_T` and the counit of `Rh_! ⊣ h^!`. The composite
uses comparison maps that the package only postulates, so it is stated here and left with
a `sorry` body. -/
noncomputable def borelMoorePushforward {T T' : Scheme.{u}} (h : T ⟶ T') (a : T' ⟶ s)
    [HasCompactification h] [IsProper h]
    (α : 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) A)) ⟶ G.dualizing (h ≫ a)) :
    𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T') A)) ⟶ G.dualizing a :=
  sorry

/-- The integral `∫_T α ∈ A` of a Borel-Moore section over a geometric scheme `T` that is
proper over the base: the pushforward of `α` along `a_T`, read in
`End (A_s) = A` through `ω_s = A_s` and `RΓ(s, -)` (part of blueprint `sk-d-integral`). -/
noncomputable def integral {T : Scheme.{u}} (a : T ⟶ s) [HasCompactification a] [IsProper a]
    (α : 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) A)) ⟶ G.dualizing a) :
    End (𝟙_ (DerivedCategory A)) :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
