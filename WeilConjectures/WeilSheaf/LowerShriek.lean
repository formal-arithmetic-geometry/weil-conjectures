/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.WeilSheaf.Defs

/-!

# Transport of a Weil structure through `Rf_!`

Let `X₀` and `Y₀` be schemes over a finite field `k` with structure morphisms
`a_{X₀} : X₀ ⟶ Spec k` and `a_{Y₀} : Y₀ ⟶ Spec k`, and let `f₀ : X₀ ⟶ Y₀` be a morphism
over `k`. Passing to geometric fibers gives `f : X ⟶ Y`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberMap`) between the geometric fibers of
`WeilConjectures.WeilSheaf.GeometricFrobenius`, and `f` commutes with the geometric
Frobenius on both sides,

```
X  -- g_X -->  X
|              |
f              f
v              v
Y  -- g_Y -->  Y
```

This *Frobenius square of `f`* is Cartesian
(`Scheme.Hom.isPullback_geometricFrobenius_geometricFiberMap`): it is obtained by
cancelling the Cartesian Frobenius square of `Y` from that of `X` in the vertical
pasting over `σ : Spec k̄ ≅ Spec k̄`.

Following the reference (`reference.tex` in this directory), a *Frobenius compatibility*
for a functor `F : Dᵇ(X) ⥤ Dᵇ(Y)` is a natural isomorphism `β_F : G_Y F ≅ F G_X`, and it
transports a Weil complex `(K, Φ_K)` to the Weil complex

`G_Y F(K) --β_F(K)--> F(G_X K) --F(Φ_K)--> F(K)`.

This is the general construction `CategoryTheory.WeilObject.map` of
`WeilConjectures.WeilSheaf.Defs`, so the content of this file is the Frobenius
compatibility of `Rf_!`, which is the compact-support base-change isomorphism `Ex_!` of
the Frobenius square.

## Frobenius-equivariant compactifications

The derived lower shriek of this project is attached to a *chosen compactification*
`c = (X ⟶[i] Z ⟶[p] Y)` of `f`, and its independence of that choice is not available;
correspondingly, the base-change morphism
`AlgebraicGeometry.Etale.lowerShriekBaseChangeOfSquares` relates `Rf_!^c` and `Rf_!^{c'}`
for compactifications related by a morphism over the Cartesian square. A Frobenius
compatibility is therefore an exchange isomorphism between the *same* functor `Rf_!^c` on
both sides, which needs a compactification `c` carrying a geometric Frobenius of its own,
compatible with those of `X` and `Y`.

Such a compactification is exactly what a compactification of `f₀` over the finite field
provides: if `c₀ = (X₀ ⟶[i₀] Z₀ ⟶[p₀] Y₀)` is a compactification of `f₀`, then its
geometric fiber `Compactification.geometricFiber` — the compactification
`X ⟶[i] Z ⟶[p] Y` of `f` obtained by base change to `k̄`, where `Z` is the geometric fiber
of `Z₀` for the structure morphism `p₀ ≫ a_{Y₀}` — is a compactification of `f` whose
geometric Frobenius `g_Z` makes both

```
X  -- g_X -->  X            Z  -- g_Z -->  Z
|              |            |              |
i              i            p              p
v              v            v              v
Z  -- g_Z -->  Z            Y  -- g_Y -->  Y
```

Cartesian. This is the geometric input of the Frobenius compatibility
`AlgebraicGeometry.Etale.frobeniusLowerShriekCompatibility`.

## Bounded below Weil complexes

The compact-support base change of this project lives on the *bounded below* derived
categories, so the Weil complexes transported here are those of
`AlgebraicGeometry.WeilComplexPlus`, the Weil objects for the Frobenius pullback
`(AlgebraicGeometry.Etale.frobeniusPullback A a).mapDerivedCategoryPlus` on
`D⁺(X_ét, A)`. A bounded below Weil complex is a Weil complex through
`AlgebraicGeometry.WeilComplexPlus.toWeilComplex`, the transport along the inclusion
`DerivedCategory.Plus.ι`, which commutes with the two Frobenius pullbacks by
`CategoryTheory.Functor.mapDerivedCategoryPlusCompatibility`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.geometricFiberMap`: the morphism `f : X ⟶ Y` of
  geometric fibers induced by a morphism `f₀ : X₀ ⟶ Y₀` over the finite base field.
- `AlgebraicGeometry.Scheme.Hom.isPullback_geometricFrobenius_geometricFiberMap`: the
  Frobenius square of `f` is Cartesian.
- `AlgebraicGeometry.Compactification.geometricFiber`: the geometric fiber of a
  compactification of `f₀`, a compactification of `f`, with the two Cartesian Frobenius
  squares `isPullback_geometricFrobenius_geometricFiber_i` and
  `isPullback_geometricFrobenius_geometricFiber_g`.
- `AlgebraicGeometry.WeilComplexPlus`: the category of bounded below Weil complexes, the
  Weil objects for the Frobenius pullback on the bounded below derived category of étale
  sheaves on the geometric fiber, with its forgetful functor `forget` and its comparison
  `toWeilComplex` with `AlgebraicGeometry.WeilComplex`.
- `AlgebraicGeometry.Etale.frobeniusLowerShriekCompatibility`: the Frobenius
  compatibility `β_{Rf_!} : G_Y Rf_! ≅ Rf_! G_X` of the derived lower shriek, the
  compact-support base-change isomorphism of the Frobenius square.
- `AlgebraicGeometry.WeilComplexPlus.lowerShriek`: the transport of bounded below Weil
  complexes through `Rf_!`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Abelian

noncomputable section

namespace AlgebraicGeometry

open Scheme

/-! ### Morphisms of geometric fibers -/

namespace Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ Z₀ : Scheme.{u}}
  {aX : X₀ ⟶ Spec (.of k)} {aY : Y₀ ⟶ Spec (.of k)} {aZ : Z₀ ⟶ Spec (.of k)}

/-- The morphism `f : X ⟶ Y` of geometric fibers induced by a morphism `u : X₀ ⟶ Y₀` over
the finite base field `k`, namely `u ×_{Spec k} Spec k̄`. -/
def geometricFiberMap {u : X₀ ⟶ Y₀} (h : u ≫ aY = aX) :
    aX.geometricFiber ⟶ aY.geometricFiber :=
  pullback.map aX (specAlgebraicClosure k) aY (specAlgebraicClosure k) u (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← h]) (by simp)

omit [Finite k] in
/-- The geometric fiber is a pullback along `Spec k̄ ⟶ Spec k`, stated for the named
projections `p_X` and `a_X` rather than for the anonymous `pullback.fst`/`pullback.snd`. -/
theorem isPullback_geometricFiber (a : X₀ ⟶ Spec (.of k)) :
    IsPullback a.geometricFiberProj a.geometricFiberStruct a (specAlgebraicClosure k) :=
  IsPullback.of_hasPullback a (specAlgebraicClosure k)

omit [Finite k] in
/-- The morphism of geometric fibers commutes with the projections to the models:
`p_Y ∘ f = u ∘ p_X`. -/
@[reassoc (attr := simp)]
theorem geometricFiberMap_proj {u : X₀ ⟶ Y₀} (h : u ≫ aY = aX) :
    geometricFiberMap h ≫ aY.geometricFiberProj = aX.geometricFiberProj ≫ u := by
  simp [geometricFiberMap, geometricFiberProj]

omit [Finite k] in
/-- The morphism of geometric fibers is a morphism over `Spec k̄`: `a_Y ∘ f = a_X`. -/
@[reassoc (attr := simp)]
theorem geometricFiberMap_struct {u : X₀ ⟶ Y₀} (h : u ≫ aY = aX) :
    geometricFiberMap h ≫ aY.geometricFiberStruct = aX.geometricFiberStruct := by
  simp [geometricFiberMap, geometricFiberStruct]

omit [Finite k] in
/-- The morphism of geometric fibers only depends on the underlying morphism of models,
not on the proof that it lies over `Spec k`. -/
theorem geometricFiberMap_congr {u u' : X₀ ⟶ Y₀} (h : u ≫ aY = aX) (h' : u' ≫ aY = aX)
    (e : u = u') : geometricFiberMap h = geometricFiberMap h' := by
  subst e; rfl

omit [Finite k] in
/-- Taking geometric fibers is functorial. -/
@[reassoc]
theorem geometricFiberMap_comp {u : X₀ ⟶ Y₀} {v : Y₀ ⟶ Z₀} (hu : u ≫ aY = aX)
    (hv : v ≫ aZ = aY) :
    geometricFiberMap hu ≫ geometricFiberMap hv =
      geometricFiberMap (show (u ≫ v) ≫ aZ = aX by rw [Category.assoc, hv, hu]) := by
  simp [geometricFiberMap, pullback.map_comp]

omit [Finite k] in
/-- The geometric fiber of `u : X₀ ⟶ Y₀` is the base change of `u` along the projection
`p_Y : Y ⟶ Y₀`: the square

```
X  -- p_X -->  X₀
|              |
f              u
v              v
Y  -- p_Y -->  Y₀
```

is Cartesian, by cancelling the Cartesian square defining `Y` from the one defining
`X`. -/
theorem isPullback_geometricFiberProj {u : X₀ ⟶ Y₀} (h : u ≫ aY = aX) :
    IsPullback aX.geometricFiberProj (geometricFiberMap h) u aY.geometricFiberProj := by
  refine IsPullback.of_bot ?_ (geometricFiberMap_proj h).symm (isPullback_geometricFiber aY)
  rw [geometricFiberMap_struct, h]
  exact isPullback_geometricFiber aX

/-- The morphism of geometric fibers commutes with the geometric Frobenius:
`f ∘ g_X = g_Y ∘ f`, both sides acting through the geometric Frobenius on the
coefficients only. -/
@[reassoc (attr := simp)]
theorem geometricFrobenius_hom_geometricFiberMap {u : X₀ ⟶ Y₀} (h : u ≫ aY = aX) :
    aX.geometricFrobenius.hom ≫ geometricFiberMap h =
      geometricFiberMap h ≫ aY.geometricFrobenius.hom := by
  simp [geometricFiberMap, geometricFrobenius, pullback.map_comp]

/-- **The Frobenius square of a morphism of geometric fibers is Cartesian**:

```
X  -- g_X -->  X
|              |
f              f
v              v
Y  -- g_Y -->  Y
```

Indeed, pasting this square below the Cartesian Frobenius square of `Y` over `σ` gives
the Cartesian Frobenius square of `X` over `σ`, since `a_Y ∘ f = a_X`. This is the square
whose compact-support base-change isomorphism is the Frobenius compatibility of
`Rf_!`. -/
theorem isPullback_geometricFrobenius_geometricFiberMap {u : X₀ ⟶ Y₀} (h : u ≫ aY = aX) :
    IsPullback aX.geometricFrobenius.hom (geometricFiberMap h) (geometricFiberMap h)
      aY.geometricFrobenius.hom := by
  refine IsPullback.of_bot ?_ (geometricFrobenius_hom_geometricFiberMap h)
    aY.isPullback_geometricFrobenius
  rw [geometricFiberMap_struct]
  exact aX.isPullback_geometricFrobenius

end Scheme.Hom

/-! ### The geometric fiber of a compactification -/

namespace Compactification

open Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}}
  {aX : X₀ ⟶ Spec (.of k)} {aY : Y₀ ⟶ Spec (.of k)} {u : X₀ ⟶ Y₀}

/-- The geometric fiber of a compactification `c₀ = (X₀ ⟶[i₀] Z₀ ⟶[p₀] Y₀)` of a morphism
`u : X₀ ⟶ Y₀` over the finite base field: the compactification `X ⟶[i] Z ⟶[p] Y` of the
geometric fiber of `u`, where `Z` is the geometric fiber of `Z₀` for the structure
morphism `p₀ ≫ a_{Y₀}`. Properness of `p` and the open-immersion property of `i` hold
since both are stable under base change, the geometric fibers being base changes along
the projections to the models. -/
def geometricFiber (c₀ : Compactification u) (h : u ≫ aY = aX) :
    Compactification (geometricFiberMap h) where
  Z := (c₀.g ≫ aY).geometricFiber
  g := geometricFiberMap (aX := c₀.g ≫ aY) rfl
  i := geometricFiberMap (show c₀.i ≫ c₀.g ≫ aY = aX by rw [← Category.assoc, ← c₀.comm, h])
  comm := by
    rw [geometricFiberMap_comp]
    exact geometricFiberMap_congr _ _ c₀.comm
  isProper :=
    MorphismProperty.of_isPullback (isPullback_geometricFiberProj (aX := c₀.g ≫ aY) rfl)
      c₀.isProper
  isOpenImmersion :=
    MorphismProperty.of_isPullback (isPullback_geometricFiberProj
      (show c₀.i ≫ c₀.g ≫ aY = aX by rw [← Category.assoc, ← c₀.comm, h])) c₀.isOpenImmersion

omit [Finite k] in
@[simp]
lemma geometricFiber_Z (c₀ : Compactification u) (h : u ≫ aY = aX) :
    (c₀.geometricFiber h).Z = (c₀.g ≫ aY).geometricFiber :=
  rfl

omit [Finite k] in
@[simp]
lemma geometricFiber_g (c₀ : Compactification u) (h : u ≫ aY = aX) :
    (c₀.geometricFiber h).g = geometricFiberMap (aX := c₀.g ≫ aY) rfl :=
  rfl

omit [Finite k] in
@[simp]
lemma geometricFiber_i (c₀ : Compactification u) (h : u ≫ aY = aX) :
    (c₀.geometricFiber h).i =
      geometricFiberMap (show c₀.i ≫ c₀.g ≫ aY = aX by rw [← Category.assoc, ← c₀.comm, h]) :=
  rfl

/-- The open-immersion square of the geometric fiber of a compactification is Frobenius
equivariant, with Cartesian square

```
X  -- g_X -->  X
|              |
i              i
v              v
Z  -- g_Z -->  Z
```
-/
theorem isPullback_geometricFrobenius_geometricFiber_i (c₀ : Compactification u)
    (h : u ≫ aY = aX) :
    IsPullback aX.geometricFrobenius.hom (c₀.geometricFiber h).i (c₀.geometricFiber h).i
      (c₀.g ≫ aY).geometricFrobenius.hom :=
  isPullback_geometricFrobenius_geometricFiberMap
    (show c₀.i ≫ c₀.g ≫ aY = aX by rw [← Category.assoc, ← c₀.comm, h])

/-- The proper square of the geometric fiber of a compactification is Frobenius
equivariant, with Cartesian square

```
Z  -- g_Z -->  Z
|              |
p              p
v              v
Y  -- g_Y -->  Y
```
-/
theorem isPullback_geometricFrobenius_geometricFiber_g (c₀ : Compactification u)
    (h : u ≫ aY = aX) :
    IsPullback (c₀.g ≫ aY).geometricFrobenius.hom (c₀.geometricFiber h).g
      (c₀.geometricFiber h).g aY.geometricFrobenius.hom :=
  isPullback_geometricFrobenius_geometricFiberMap (aX := c₀.g ≫ aY) rfl

end Compactification

/-! ### Bounded below Weil complexes -/

section WeilComplexPlus

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k))

/-- A *bounded below Weil complex* on the geometric fiber `X` of a scheme over a finite
field is an object `K` of `D⁺(X_ét, A)` together with an isomorphism `Φ : G_X K ≅ K`
along the Frobenius pullback `G_X = g_X^*`, which on `D⁺(X_ét, A)` is
`(Etale.frobeniusPullback A a).mapDerivedCategoryPlus`, the restriction of
`Etale.derivedFrobeniusPullback` along the inclusion `DerivedCategory.Plus.ι`. The
isomorphism `Φ` is structure data. This is the level at which the compact-support base
change of this project, hence the transport of Weil structures through `Rf_!`, is
available. -/
def WeilComplexPlus : Type _ :=
  WeilObject (Etale.frobeniusPullback A a).mapDerivedCategoryPlus

instance : Category (WeilComplexPlus A a) :=
  inferInstanceAs (Category (WeilObject (Etale.frobeniusPullback A a).mapDerivedCategoryPlus))

/-- The forgetful functor from bounded below Weil complexes to `D⁺(X_ét, A)`, discarding
the Frobenius structure isomorphisms. -/
def WeilComplexPlus.forget :
    WeilComplexPlus A a ⥤
      DerivedCategory.Plus (Sheaf (a.geometricFiber).smallEtaleTopology A) :=
  WeilObject.forget (Etale.frobeniusPullback A a).mapDerivedCategoryPlus

/-- A bounded below Weil complex is in particular a Weil complex: the inclusion
`DerivedCategory.Plus.ι` commutes with the two Frobenius pullbacks by
`Functor.mapDerivedCategoryPlusCompatibility` and transports the Weil structure. -/
def WeilComplexPlus.toWeilComplex : WeilComplexPlus A a ⥤ WeilComplex A a :=
  WeilObject.map (F := DerivedCategory.Plus.ι)
    (Etale.frobeniusPullback A a).mapDerivedCategoryPlusCompatibility.symm

end WeilComplexPlus

/-! ### The Frobenius compatibility of `Rf_!` -/

section LowerShriek

open Scheme.Hom Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}}
  {aX : X₀ ⟶ Spec (.of k)} {aY : Y₀ ⟶ Spec (.of k)} {u : X₀ ⟶ Y₀}

/-- **The Frobenius compatibility of the derived lower shriek**: for a morphism
`u : X₀ ⟶ Y₀` over the finite base field with a compactification `c₀`, the compact-support
base-change morphism of the Cartesian Frobenius square of `f = u ×_k k̄`, taken for the
Frobenius-equivariant compactification `c = c₀.geometricFiber h` of `f`, is a natural
isomorphism

`β_{Rf_!} : Rf_!^c ⋙ G_Y ≅ G_X ⋙ Rf_!^c`

(in diagrammatic order; that is, `G_Y ∘ Rf_!^c ≅ Rf_!^c ∘ G_X`). It is an isomorphism by
the base change theorem for the lower shriek, the coefficient ring being torsion.

Both squares of `Compactification.geometricFiber` being Cartesian is what makes the
source and the target of this base-change morphism involve the *same* derived lower
shriek `Rf_!^c`, so that it is a Frobenius compatibility in the sense of
`CategoryTheory.WeilObject.map` and not merely a comparison of the lower shrieks of two
different compactifications. -/
def Etale.frobeniusLowerShriekCompatibility (hΛ : IsAddTorsion Λ) (h : u ≫ aY = aX)
    (c₀ : Compactification u) :
    Rf_!(c₀.geometricFiber h)[ModuleCat.{u + 1} Λ]+ ⋙
        (Etale.frobeniusPullback (ModuleCat.{u + 1} Λ) aY).mapDerivedCategoryPlus ≅
      (Etale.frobeniusPullback (ModuleCat.{u + 1} Λ) aX).mapDerivedCategoryPlus ⋙
        Rf_!(c₀.geometricFiber h)[ModuleCat.{u + 1} Λ]+ :=
  have := Etale.isIso_lowerShriekBaseChangeOfSquares Λ hΛ (c₀.geometricFiber h)
    (c₀.geometricFiber h) (c₀.isPullback_geometricFrobenius_geometricFiber_i h)
    (c₀.isPullback_geometricFrobenius_geometricFiber_g h)
  asIso (Etale.lowerShriekBaseChangeOfSquares (ModuleCat.{u + 1} Λ) (c₀.geometricFiber h)
    (c₀.geometricFiber h) (c₀.isPullback_geometricFrobenius_geometricFiber_i h)
    (c₀.isPullback_geometricFrobenius_geometricFiber_g h))

/-- **The Weil structure on `Rf_! K`**: the transport of bounded below Weil complexes
through the derived lower shriek of the geometric fiber of a compactification `c₀` of
`u : X₀ ⟶ Y₀`. A Weil complex `(K, Φ_K)` on `X` is sent to `Rf_!^c K` equipped with

`G_Y Rf_!^c K --Ex_!--> Rf_!^c G_X K --Rf_!^c(Φ_K)--> Rf_!^c K`,

the transport of `CategoryTheory.WeilObject.map` along the Frobenius compatibility
`Etale.frobeniusLowerShriekCompatibility`. -/
def WeilComplexPlus.lowerShriek (hΛ : IsAddTorsion Λ) (h : u ≫ aY = aX)
    (c₀ : Compactification u) :
    WeilComplexPlus (ModuleCat.{u + 1} Λ) aX ⥤ WeilComplexPlus (ModuleCat.{u + 1} Λ) aY :=
  WeilObject.map (Etale.frobeniusLowerShriekCompatibility Λ hΛ h c₀)

end LowerShriek

end AlgebraicGeometry

end

end
