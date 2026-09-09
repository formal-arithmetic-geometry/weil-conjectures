/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.WeilSheaf.Defs

/-!

# The Weil structure on a stalk

This file carries out Section 3 of the reference (`reference.tex` in this directory),
*Weil structure and Frobenius on a stalk*: it equips the stalk of a Weil sheaf or Weil
complex at a Frobenius-invariant geometric point with a Weil structure of its own, and it
produces the local Frobenius operator at a genuinely fixed point.

The layer this file works in is the bounded below derived category `D⁺(X_ét, A)`, that is
`AlgebraicGeometry.WeilComplexPlus`. This is the layer at which the compact-support base
change of this project, hence the transport of Weil structures through `Rf_!`, is
available, so it is the layer in which the two sides of the trace formula must be
compared: `R Γ_c(X, K)` on one side and the stalks `K_x̄` on the other. The Weil sheaf and
`D(X_ét, A)` layers are constructed along the way, `D⁺` being cut out of `D` by
restriction.

## Equivariant pullback

Everything comes from one observation. Let `e : X ≅ X` and `ε : S ≅ S` be schemes with
automorphisms and let `x : S ⟶ X` be *equivariant*, that is

```
      x
  S ------> X
  |         |
  ε         e
  v         v
  S ------> X
      x
```

commutes, `x ≫ e = ε ≫ x`. Then the pullback `x^*` intertwines the two pullback
endofunctors, `x^* ∘ ε^* ≅ e^* ∘ x^*` (`AlgebraicGeometry.Etale.upperStarSquare`), and
this is exactly the commutation datum that
`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` transports algebras along. So `x^*`
carries Weil structures for `(X, e)` to Weil structures for `(S, ε)`. No base change
theorem is involved: the commutation isomorphism is the composition isomorphism
`AlgebraicGeometry.Etale.upperStarComp` of pullbacks, so `x` is an arbitrary morphism of
schemes; this is what makes the construction available for a geometric point, which is
very far from being étale or of finite type.

## Stalks at geometric points

The intended instance is the following, and it is the reason the transport is stated for
a *pair* of automorphisms rather than for a fixed point. Let `X₀` be a scheme over a
finite field `k` with structure morphism `f : X₀ ⟶ Spec k`, let `X = X₀ ×_{Spec k} Spec k̄`
be its geometric fiber, `e = g_X` its geometric Galois Frobenius and `σ` the geometric
Frobenius of `Spec k̄`. A geometric point `x̄ : Spec k̄ ⟶ X` of `X` over `k̄` is *not* fixed
by `g_X`, since `g_X` is semilinear over `k̄`; what does hold, exactly when the underlying
`k̄`-point `x₀ = p_X ∘ x̄` of the model `X₀` is `σ`-invariant, is the equivariance
`x̄ ≫ g_X = σ ≫ x̄`
(`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius_comp_geometricPoint`). The stalk
`K_x̄` is therefore a bounded below Weil complex for `(Spec k̄, σ)`: a Frobenius module,
which is the classical statement that the stalk of a Weil sheaf at a geometric point is a
representation of the Weil group.

Turning that Weil structure into an honest endomorphism of `K_x̄`, the local Frobenius
`F_x` of the reference, needs the étale topos of `Spec k̄` to be the point, i.e. the
identification `σ^* ≅ 𝟭` on `Sheaf (Spec k̄)_ét`. That identification is not yet available
here and is the one input still owed at this step; the reference obtains the same operator
along a different route, replacing `g_γ` by the `q`-power scheme Frobenius `Φ`, which does
fix `x̄` on the nose, at the cost of the comparison `κ_m : LΦ^{m*} ≅ Lg_γ^{m*}` coming from
the invariance of the étale topos under a universal homeomorphism. Both routes need one
input beyond the six operations, and neither is formalized here.

What *is* available unconditionally is the case of a genuinely fixed point, `x ≫ e = x`,
which is the case `ε = 𝟙`: there the composite

```
             x^*(Φ)
K_x = (x ≫ e)^* K ≅ x^*(e^* K) -------> x^* K = K_x
```

is a well-defined automorphism of the stalk,
`AlgebraicGeometry.WeilComplexPlus.stalkFrobenius`. Its `m`-th power is the operator
`F_{x,m}` of the reference; no separate iterate is needed, because a point fixed by `e` is
fixed by `eᵐ`.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarSquare`: the commutation isomorphism
  `u^* ⋙ x^* ≅ y^* ⋙ w^*` of pullbacks attached to a commuting square of schemes, with
  its derived variants `Etale.upperStarSquareMapDerivedCategory` and
  `Etale.upperStarSquareMapDerivedCategoryPlus`.
- `AlgebraicGeometry.WeilComplexPlus.upperStar`: the transport of bounded below Weil
  complexes along an equivariant morphism `x : S ⟶ X`, with the Weil sheaf and
  `D(X_ét, A)` versions `AlgebraicGeometry.WeilSheaf.upperStar` and
  `AlgebraicGeometry.WeilComplex.upperStar`.
- `AlgebraicGeometry.WeilComplexPlus.stalkFrobenius`: the local Frobenius automorphism of
  the stalk at a fixed point of `e`, with the Weil sheaf and `D(X_ét, A)` versions
  `AlgebraicGeometry.WeilSheaf.stalkFrobenius` and
  `AlgebraicGeometry.WeilComplex.stalkFrobenius`.
- `AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius_comp_geometricPoint`: a geometric
  point of the geometric fiber whose underlying point of the model is `σ`-invariant is
  equivariant for the geometric Galois Frobenius and `σ`.
- `AlgebraicGeometry.WeilComplexPlus.stalk`: the resulting Weil structure on the stalk of
  a bounded below Weil complex at such a geometric point.

-/

@[expose] public section

universe u u'

open CategoryTheory Endofunctor Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry

open Scheme

noncomputable section

/-! ### The commutation isomorphism of a square of pullbacks -/

section Square

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {S T X Y : Scheme.{u}} {w : S ⟶ T} {y : T ⟶ Y} {x : S ⟶ X} {u : X ⟶ Y}

open Etale in
/-- The commutation isomorphism `u^* ⋙ x^* ≅ y^* ⋙ w^*` of pullbacks on étale sheaves
attached to a commuting square

```
      x
  S ------> X
  |         |
  w         u
  v         v
  T ------> Y
      y
```

that is, to an identity `x ≫ u = w ≫ y`. Both sides are the pullback along the diagonal
of the square, through the composition isomorphism `Etale.upperStarComp`; this is plain
functoriality of the pullback and not a base change theorem, so no hypothesis on the
square is needed and it need not be Cartesian. -/
def Etale.upperStarSquare (h : x ≫ u = w ≫ y) :
    (u)^*[A] ⋙ (x)^*[A] ≅ (y)^*[A] ⋙ (w)^*[A] :=
  (Etale.upperStarComp A x u).symm ≪≫ eqToIso (congrArg (Etale.upperStar A) h) ≪≫
    Etale.upperStarComp A w y

open Etale in
/-- The commutation isomorphism `Etale.upperStarSquare` of a commuting square of schemes,
on the derived categories of étale sheaves: the pullbacks being exact, transport
`Etale.upperStarSquare` through `CategoryTheory.Functor.mapDerivedCategoryNatIso` and
undo the two composites with `CategoryTheory.Functor.mapDerivedCategoryCompIso`. -/
def Etale.upperStarSquareMapDerivedCategory (h : x ≫ u = w ≫ y) :
    (u)^*[A].mapDerivedCategory ⋙ (x)^*[A].mapDerivedCategory ≅
      (y)^*[A].mapDerivedCategory ⋙ (w)^*[A].mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.upperStarSquare A h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

open Etale in
/-- The commutation isomorphism `Etale.upperStarSquare` of a commuting square of schemes,
on the bounded below derived categories of étale sheaves. This is the form used for the
stalk: `D⁺` is the layer carrying the compact-support base change, hence the transport of
Weil structures through `Rf_!`. -/
def Etale.upperStarSquareMapDerivedCategoryPlus (h : x ≫ u = w ≫ y) :
    (u)^*[A].mapDerivedCategoryPlus ⋙ (x)^*[A].mapDerivedCategoryPlus ≅
      (y)^*[A].mapDerivedCategoryPlus ⋙ (w)^*[A].mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarSquare A h) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

end Square

/-! ### Transport of Weil structures along an equivariant morphism -/

section Equivariant

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X S : Scheme.{u}} {e : X ≅ X} {ε : S ≅ S} {x : S ⟶ X}

/-- **The Weil sheaf structure on a pullback**. If `x : S ⟶ X` is equivariant for the
automorphisms `e : X ≅ X` and `ε : S ≅ S`, that is `x ≫ e = ε ≫ x`, then `x^*` sends a
Weil sheaf `(F, Φ)` for `(X, e)` to the Weil sheaf `x^* F` for `(S, ε)` with structure
isomorphism

```
                          x^*(Φ)
ε^*(x^* F) ≅ x^*(e^* F) ----------> x^* F,
```

the transport `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` of algebras along the
commutation isomorphism `Etale.upperStarSquare` of the equivariance square. -/
def WeilSheaf.upperStar (h : x ≫ e.hom = ε.hom ≫ x) : WeilSheaf A e ⥤ WeilSheaf A ε :=
  IsoAlgebra.mapOfNatIso (Etale.upperStarSquare A h).symm

/-- **The Weil structure on the pullback of a Weil complex** along a morphism `x : S ⟶ X`
equivariant for `e : X ≅ X` and `ε : S ≅ S`. -/
def WeilComplex.upperStar (h : x ≫ e.hom = ε.hom ≫ x) : WeilComplex A e ⥤ WeilComplex A ε :=
  IsoAlgebra.mapOfNatIso (Etale.upperStarSquareMapDerivedCategory A h).symm

/-- **The Weil structure on the pullback of a bounded below Weil complex** along a
morphism `x : S ⟶ X` equivariant for `e : X ≅ X` and `ε : S ≅ S`. For `x` a geometric
point this is the Weil structure on the stalk, in the layer `D⁺(X_ét, A)` in which the
compact-support Frobenius of the trace formula lives. -/
def WeilComplexPlus.upperStar (h : x ≫ e.hom = ε.hom ≫ x) :
    WeilComplexPlus A e ⥤ WeilComplexPlus A ε :=
  IsoAlgebra.mapOfNatIso (Etale.upperStarSquareMapDerivedCategoryPlus A h).symm

end Equivariant

/-! ### The local Frobenius at a fixed point -/

section FixedPoint

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X S : Scheme.{u}} {e : X ≅ X} {x : S ⟶ X}

open Etale in
/-- **The local Frobenius on a stalk**. If `x : S ⟶ X` is fixed by the automorphism
`e : X ≅ X`, that is `x ≫ e = x`, then the stalk `F_x = x^* F` of a Weil sheaf `(F, Φ)`
carries the automorphism

```
                               x^*(Φ)
F_x = (x ≫ e)^* F ≅ x^*(e^* F) -------> x^* F = F_x,
```

the first isomorphism being the equality `x ≫ e = x` followed by the composition
isomorphism `Etale.upperStarComp`. Changing `x` within its `e`-orbit conjugates this
automorphism, so its trace does not depend on that choice. -/
def WeilSheaf.stalkFrobenius (K : WeilSheaf A e) (h : x ≫ e.hom = x) :
    ((x)^*[A]).obj K.carrier ≅ ((x)^*[A]).obj K.carrier :=
  eqToIso (congrArg (fun g ↦ ((g)^*[A]).obj K.carrier) h.symm) ≪≫
    (Etale.upperStarComp A x e.hom).app K.carrier ≪≫ ((x)^*[A]).mapIso K.str

open Etale in
/-- **The local Frobenius on the stalk of a Weil complex** at a point `x : S ⟶ X` fixed by
the automorphism `e : X ≅ X`, the derived-category form of
`AlgebraicGeometry.WeilSheaf.stalkFrobenius`. -/
def WeilComplex.stalkFrobenius (K : WeilComplex A e) (h : x ≫ e.hom = x) :
    ((x)^*[A]).mapDerivedCategory.obj K.carrier ≅
      ((x)^*[A]).mapDerivedCategory.obj K.carrier :=
  eqToIso (congrArg (fun g ↦ ((g)^*[A]).mapDerivedCategory.obj K.carrier) h.symm) ≪≫
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A x e.hom)).app K.carrier ≪≫
    (Functor.mapDerivedCategoryCompIso ((e.hom)^*[A]) ((x)^*[A])).app K.carrier ≪≫
    ((x)^*[A]).mapDerivedCategory.mapIso K.str

open Etale in
/-- **The local Frobenius on the stalk of a bounded below Weil complex** at a point
`x : S ⟶ X` fixed by the automorphism `e : X ≅ X`. This is the operator `F_{x,1}` of the
reference, in the layer `D⁺(X_ét, A)` in which the compact-support Frobenius `F_{c,K}`
lives, so that the two sides of the trace formula are operators on objects of the same
category. The operator `F_{x,m}` is its `m`-th power, a point fixed by `e` being fixed by
`eᵐ`. -/
def WeilComplexPlus.stalkFrobenius (K : WeilComplexPlus A e) (h : x ≫ e.hom = x) :
    ((x)^*[A]).mapDerivedCategoryPlus.obj K.carrier ≅
      ((x)^*[A]).mapDerivedCategoryPlus.obj K.carrier :=
  eqToIso (congrArg (fun g ↦ ((g)^*[A]).mapDerivedCategoryPlus.obj K.carrier) h.symm) ≪≫
    (Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarComp A x e.hom)).app K.carrier ≪≫
    (Functor.mapDerivedCategoryPlusCompIso ((e.hom)^*[A]) ((x)^*[A])).app K.carrier ≪≫
    ((x)^*[A]).mapDerivedCategoryPlus.mapIso K.str

end FixedPoint

/-! ### Geometric points of a geometric fiber -/

namespace Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- **A `σ`-invariant geometric point is equivariant for the geometric Galois Frobenius**.
Let `x̄ : Spec k̄ ⟶ X` be a geometric point of the geometric fiber `X = X₀ ×_{Spec k} Spec k̄`
lying over `Spec k̄`, and assume that the underlying `k̄`-point `x₀ = p_X ∘ x̄` of the model
`X₀` is invariant under the geometric Frobenius `σ` of `Spec k̄`. Then the square

```
          x̄
Spec k̄ ------> X
  |            |
  σ           g_X
  v            v
Spec k̄ ------> X
          x̄
```

commutes. Note that `x̄` itself is *not* fixed by `g_X`: the geometric Galois Frobenius is
semilinear over `k̄`, so it moves a geometric point by `σ` on the coefficients, and `σ` is
what the equivariance keeps track of. Both sides are compared componentwise in the
pullback defining `X`: on the model they agree by the `σ`-invariance of `x₀`, and on the
coefficients both are `σ`. -/
@[reassoc]
theorem geometricGaloisFrobenius_comp_geometricPoint
    (x : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber)
    (hx : x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _)
    (hx₀ : (specGeometricFrobenius k).hom ≫ x ≫ f.geometricFiberProj =
      x ≫ f.geometricFiberProj) :
    x ≫ f.geometricGaloisFrobenius.hom = (specGeometricFrobenius k).hom ≫ x := by
  have h₁ : (x ≫ f.geometricGaloisFrobenius.hom) ≫ f.geometricFiberProj =
      ((specGeometricFrobenius k).hom ≫ x) ≫ f.geometricFiberProj := by
    simp only [Category.assoc, geometricGaloisFrobenius_hom_comp_geometricFiberProj]
    exact hx₀.symm
  have h₂ : (x ≫ f.geometricGaloisFrobenius.hom) ≫ f.geometricFiberToAlgebraicClosure =
      ((specGeometricFrobenius k).hom ≫ x) ≫ f.geometricFiberToAlgebraicClosure := by
    simp only [Category.assoc,
      geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure, reassoc_of% hx,
      hx, Category.comp_id]
  exact pullback.hom_ext h₁ h₂

end Scheme.Hom

/-! ### The Weil structure on the stalk at a geometric point -/

section Stalk

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}

/-- **The Weil structure on the stalk of a bounded below Weil complex at a geometric
point**. For a `σ`-invariant geometric point `x̄` of the geometric fiber `X` of
`f : X₀ ⟶ Spec k`, the stalk `K_x̄` of a bounded below Weil complex `K` for `(X, g_X)` is a
bounded below Weil complex for `(Spec k̄, σ)`: a Frobenius module. This is the
specialization of `AlgebraicGeometry.WeilComplexPlus.upperStar` to the equivariance
square `Scheme.Hom.geometricGaloisFrobenius_comp_geometricPoint`.

Both this and the compact-support Frobenius of `R Γ_c(X, K)` are constructions in
`D⁺`, which is what lets the two sides of the trace formula be compared. -/
def WeilComplexPlus.stalk
    (x : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber)
    (hx : x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _)
    (hx₀ : (specGeometricFrobenius k).hom ≫ x ≫ f.geometricFiberProj =
      x ≫ f.geometricFiberProj) :
    WeilComplexPlus A f.geometricGaloisFrobenius ⥤
      WeilComplexPlus A (specGeometricFrobenius k) :=
  WeilComplexPlus.upperStar A (f.geometricGaloisFrobenius_comp_geometricPoint x hx hx₀)

end Stalk

end

end AlgebraicGeometry

end
