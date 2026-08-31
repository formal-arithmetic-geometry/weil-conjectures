/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek

/-!

# The Weil structure on compactly supported cohomology

Let `X₀` be a scheme over a finite field `k` with structure morphism
`a_{X₀} : X₀ ⟶ Spec k`, let `s = Spec k̄` be the geometric point, and let `X` be the
geometric fiber with structure morphism `a_X : X ⟶ s`. Following the reference
(`reference.tex` in this directory) the compactly supported derived global sections of a
complex `K` on `X` are

`RΓc(X, K) := RΓ(s, Ra_{X!} K)`,

and `H_c^i(X, K) := Hⁱ(RΓc(X, K))`. This file equips them with the geometric Frobenius,
i.e. transports a Weil structure on `K` to an *automorphism* of `RΓc(X, K)` and of each
`H_c^i(X, K)`.

## The Frobenius on `RΓc`

Both halves of `RΓc` move under Frobenius, in opposite ways, and the two motions cancel:

- the Cartesian Frobenius square of `a_X` (`Scheme.Hom.isPullback_geometricFrobenius`)

  ```
  X  -- g_X -->  X
  |              |
  a_X            a_X
  v              v
  s  --  σ  -->  s
  ```

  gives, through the compact-support base change of a Frobenius-equivariant
  compactification, the exchange isomorphism
  `Ex_! : Ra_{X!} ⋙ Lσ^* ≅ G_X ⋙ Ra_{X!}`
  (`Etale.frobeniusLowerShriekStructCompatibility`);
- derived global sections on the geometric point do not see `σ` at all:
  `Lσ^* ⋙ RΓ(s, -) ≅ RΓ(s, -)` (`Etale.upperStarCompRightDerivedGlobalSectionsPlusIso`),
  the `c_σ` of the reference.

Composing them gives a Frobenius compatibility for `RΓc(X, -)` whose *target*
endofunctor is the identity (`Etale.frobeniusCompactlySupportedCompatibility`):

`RΓc(X, -) ≅ G_X ⋙ RΓc(X, -)`.

Transporting a Weil complex along it with `CategoryTheory.WeilObject.map` therefore lands
in `WeilObject (𝟭 _)`, the category of objects equipped with an automorphism: the
structure isomorphism `CategoryTheory.WeilObject.str` of such an object is an
automorphism of the underlying object, namely the geometric Frobenius `F_{K,1}` of the
reference, and `F_{K,n}` is its `n`-th power.

## `c_σ`: derived global sections on the geometric point are Frobenius invariant

`σ` is an *isomorphism* of schemes, hence in particular étale, so `Lσ^*` is computed by
restriction along the localization functor of the small étale site
(`Etale.upperStarIsoOpenImmersionRestriction`). Global sections are sections over the
terminal object `𝟙 s`, and restriction sends the terminal object to the object `σ` of the
small étale site of `s`, which is terminal again because `σ` is an isomorphism
(`AlgebraicGeometry.Scheme.isTerminalEtaleMkIso`). So already on sheaves
`Γ(s, σ^* -) ≅ Γ(s, -)` (`Etale.upperStarCompGlobalSectionsIso`), for an arbitrary
isomorphism of schemes in place of `σ`.

Passing to the bounded below derived categories uses that `σ^*` is exact, so that it is
its own right derived functor
(`Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`), and preserves injectives,
being right adjoint to the exact extension by zero `σ_!`; the composition theorem
`Functor.rightDerivedFunctorPlusCompIso'` then derives the underived isomorphism. The
cocycle law in `n` demanded by the reference is not a separate datum here: the iterates
`F_{K,n}` are powers of the single automorphism `F_{K,1}`.

## Main definitions

- `AlgebraicGeometry.Compactification.geometricFiberStruct`: the geometric fiber of a
  compactification of `a_{X₀}`, a Frobenius-equivariant compactification of `a_X`, with
  its two Cartesian Frobenius squares.
- `AlgebraicGeometry.Etale.upperStarCompGlobalSectionsIso` and
  `AlgebraicGeometry.Etale.upperStarCompRightDerivedGlobalSectionsPlusIso`: global
  sections, resp. bounded below derived global sections, are invariant under pullback
  along an isomorphism of schemes; for `σ` this is the `c_σ` of the reference.
- `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsPlus`: `RΓ(X, -)` on the bounded
  below derived categories.
- `AlgebraicGeometry.Etale.frobeniusLowerShriekStructCompatibility`: the Frobenius
  compatibility `Ex_!` of `Ra_{X!}`.
- `AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsPlus`: `RΓc(X, -)`.
- `AlgebraicGeometry.Etale.frobeniusCompactlySupportedCompatibility`: the Frobenius
  compatibility of `RΓc(X, -)`, with the identity as target endofunctor.
- `AlgebraicGeometry.WeilComplexPlus.compactlySupportedGlobalSections` and
  `AlgebraicGeometry.WeilComplexPlus.compactlySupportedCohomology`: the geometric
  Frobenius on `RΓc(X, K)` and on `H_c^i(X, K)`, as objects with an automorphism.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Abelian

noncomputable section

namespace AlgebraicGeometry

open Scheme

/-! ### The geometric fiber of a compactification of the structure morphism -/

namespace Compactification

open Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} {aX : X₀ ⟶ Spec (.of k)}

/-- The geometric fiber of a compactification `c₀ = (X₀ ⟶[i₀] Z₀ ⟶[p₀] Spec k)` of the
structure morphism of a scheme over the finite field `k`: the base change
`Compactification.baseChange` of `c₀` along the Cartesian square
`Scheme.Hom.isPullback_geometricFiber` exhibiting the geometric fiber as the base change
along `Spec k̄ ⟶ Spec k`. It is the compactification `X ⟶[i] Z ⟶[a_Z] Spec k̄` of the
structure morphism `a_X : X ⟶ Spec k̄` of the geometric fiber, in which the compactifying
scheme `Z` is the geometric fiber of `Z₀` and `a_Z` is its structure morphism, both on the
nose. -/
def geometricFiberStruct (c₀ : Compactification aX) :
    Compactification aX.geometricFiberStruct :=
  c₀.baseChange (isPullback_geometricFiber aX)

omit [Finite k] in
@[simp]
lemma geometricFiberStruct_Z (c₀ : Compactification aX) :
    (c₀.geometricFiberStruct).Z = c₀.g.geometricFiber :=
  rfl

omit [Finite k] in
@[simp]
lemma geometricFiberStruct_g (c₀ : Compactification aX) :
    (c₀.geometricFiberStruct).g = c₀.g.geometricFiberStruct :=
  rfl

omit [Finite k] in
/-- The open immersion of the geometric fiber of a compactification of the structure
morphism is the geometric fiber of the open immersion of the compactification. -/
@[simp]
lemma geometricFiberStruct_i (c₀ : Compactification aX) :
    (c₀.geometricFiberStruct).i = geometricFiberMap c₀.comm.symm := by
  apply pullback.hom_ext <;>
    simp [geometricFiberStruct, Compactification.baseChange,
      Compactification.baseChangeOpenImmersion, geometricFiberMap, geometricFiberProj,
      Scheme.Hom.geometricFiberStruct]

/-- The open-immersion square of the geometric fiber of a compactification of the
structure morphism is Frobenius equivariant, with Cartesian square

```
X  -- g_X -->  X
|              |
i              i
v              v
Z  -- g_Z -->  Z
```
-/
theorem isPullback_geometricFrobenius_geometricFiberStruct_i (c₀ : Compactification aX) :
    IsPullback aX.geometricFrobenius.hom (c₀.geometricFiberStruct).i
      (c₀.geometricFiberStruct).i c₀.g.geometricFrobenius.hom := by
  rw [geometricFiberStruct_i]
  exact isPullback_geometricFrobenius_geometricFiberMap c₀.comm.symm

/-- The proper square of the geometric fiber of a compactification of the structure
morphism is Frobenius equivariant, with Cartesian square

```
Z  -- g_Z -->  Z
|              |
a_Z            a_Z
v              v
s  --  σ  -->  s
```

This is the Cartesian Frobenius square of `Z`, `Scheme.Hom.isPullback_geometricFrobenius`:
the bottom of the square is the geometric Frobenius `σ` of the base point itself. -/
theorem isPullback_geometricFrobenius_geometricFiberStruct_g (c₀ : Compactification aX) :
    IsPullback c₀.g.geometricFrobenius.hom (c₀.geometricFiberStruct).g
      (c₀.geometricFiberStruct).g (specGeometricFrobenius k).hom :=
  c₀.g.isPullback_geometricFrobenius

end Compactification

/-! ### Frobenius invariance of derived global sections on the geometric point -/

section GlobalSections

open Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Global sections are invariant under pullback along an isomorphism of schemes**:
`Γ(W, e^* -) ≅ Γ(X, -)` for `e : W ≅ X`. Global sections are the sections over the
terminal object `𝟙 W` of the small étale site; since `e` is in particular étale, `e^*` is
restriction along the localization functor, which sends `𝟙 W` to the object `e` of the
small étale site of `X`, and that object is terminal again because `e` is an isomorphism
(`Scheme.isTerminalEtaleMkIso`). -/
def Etale.upperStarCompGlobalSectionsIso {W X : Scheme.{u}} (e : W ≅ X) :
    (e.hom)^*[A] ⋙ Sheaf.Γ W.smallEtaleTopology A ≅ Sheaf.Γ X.smallEtaleTopology A :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections W.smallEtaleTopology A
      (Scheme.isTerminalEtaleMkIso (Iso.refl W))) ≪≫
    Functor.isoWhiskerRight (Etale.upperStarIsoOpenImmersionRestriction A e.hom) _ ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
    (sheafSections X.smallEtaleTopology A).mapIso
      ((Scheme.isTerminalEtaleMkIso (Iso.refl X)).uniqueUpToIso
        (Scheme.isTerminalEtaleMkIso (Iso.refl W ≪≫ e))).op ≪≫
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
      (Scheme.isTerminalEtaleMkIso (Iso.refl X))).symm

/-- The derived global sections `RΓ(X, -) : D⁺(X_ét) ⥤ D⁺(A)` on the *bounded below*
derived categories: the bounded below right derived functor of the global sections
functor on étale sheaves, which exists since the small étale site has a terminal object.
This is the `RΓ(s, -)` of the reference, on the level at which the compact-support base
change of this project is available. -/
def Etale.rightDerivedGlobalSectionsPlus (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory.Plus A :=
  (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlus

/-- **Derived global sections are invariant under pullback along an isomorphism of
schemes**: `RΓ(W, Le^* -) ≅ RΓ(X, -)` for `e : W ≅ X`. This is the `c_σ` of the reference,
for `e = σ` the geometric Frobenius of the geometric point.

The pullback `e^*` is exact, so it is its own bounded below right derived functor, and it
preserves injectives, being right adjoint to the exact extension by zero `e_!`; the
composition theorem for bounded below right derived functors therefore derives the
underived isomorphism `Etale.upperStarCompGlobalSectionsIso`. -/
def Etale.upperStarCompRightDerivedGlobalSectionsPlusIso {W X : Scheme.{u}} (e : W ≅ X) :
    (e.hom)^*[A].mapDerivedCategoryPlus ⋙ Etale.rightDerivedGlobalSectionsPlus A W ≅
      Etale.rightDerivedGlobalSectionsPlus A X :=
  have : ((e.hom)^*[A]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.openImmersionLowerShriekUpperStarAdjunction A e.hom)
  Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus ((e.hom)^*[A])).symm
      (Etale.rightDerivedGlobalSectionsPlus A W) ≪≫
    Functor.rightDerivedFunctorPlusCompIso' _ _ (Etale.upperStarCompGlobalSectionsIso A e)

end GlobalSections

/-! ### The Weil structure on `RΓc` and on `H_c^i` -/

section CompactlySupported

open Scheme.Hom Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} {aX : X₀ ⟶ Spec (.of k)}

/-- **The Frobenius compatibility of `Ra_{X!}`**: for a compactification `c₀` of the
structure morphism `a_{X₀} : X₀ ⟶ Spec k`, the compact-support base-change morphism of the
Cartesian Frobenius square

```
X  -- g_X -->  X
|              |
a_X            a_X
v              v
s  --  σ  -->  s
```

of the structure morphism of the geometric fiber, taken for the Frobenius-equivariant
compactification `c = c₀.geometricFiberStruct` of `a_X`, is a natural isomorphism

`Ex_! : Ra_{X!}^c ⋙ Lσ^* ≅ G_X ⋙ Ra_{X!}^c`

(in diagrammatic order). Unlike the situation of
`Etale.frobeniusLowerShriekCompatibility`, the Frobenius on the target of `a_X` is the
geometric Frobenius `σ` of `Spec k̄` itself, not that of a geometric fiber. -/
def Etale.frobeniusLowerShriekStructCompatibility (hΛ : IsAddTorsion Λ)
    (c₀ : Compactification aX) :
    Rf_!(c₀.geometricFiberStruct)[ModuleCat.{u + 1} Λ]+ ⋙
        ((specGeometricFrobenius k).hom)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlus ≅
      (Etale.frobeniusPullback (ModuleCat.{u + 1} Λ) aX).mapDerivedCategoryPlus ⋙
        Rf_!(c₀.geometricFiberStruct)[ModuleCat.{u + 1} Λ]+ :=
  have := Etale.isIso_lowerShriekBaseChangeOfSquares Λ hΛ c₀.geometricFiberStruct
    c₀.geometricFiberStruct c₀.isPullback_geometricFrobenius_geometricFiberStruct_i
    c₀.isPullback_geometricFrobenius_geometricFiberStruct_g
  asIso (Etale.lowerShriekBaseChangeOfSquares (ModuleCat.{u + 1} Λ) c₀.geometricFiberStruct
    c₀.geometricFiberStruct c₀.isPullback_geometricFrobenius_geometricFiberStruct_i
    c₀.isPullback_geometricFrobenius_geometricFiberStruct_g)

/-- The **compactly supported derived global sections** of the geometric fiber `X` of a
scheme over a finite field, *defined* as the composite

`RΓc(X, -) := RΓ(s, Ra_{X!} -) : D⁺(X_ét) ⥤ D⁺(A)`

for a compactification `c` of the structure morphism `a_X : X ⟶ Spec k̄`. The intermediate
object `Ra_{X!} K ∈ D⁺(s_ét)` and the coefficient complex `RΓc(X, K) ∈ D⁺(A)` are not
definitionally the same. -/
def Etale.compactlySupportedGlobalSectionsPlus
    (c : Compactification aX.geometricFiberStruct) :
    DerivedCategory.Plus (Sheaf (aX.geometricFiber).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Λ) :=
  Rf_!(c)[ModuleCat.{u + 1} Λ]+ ⋙
    Etale.rightDerivedGlobalSectionsPlus (ModuleCat.{u + 1} Λ)
      (Spec (.of (AlgebraicClosure k)))

/-- **The Frobenius compatibility of `RΓc`**: the natural isomorphism

`RΓc(X, -) ≅ G_X ⋙ RΓc(X, -)`,

a Frobenius compatibility in the sense of `CategoryTheory.WeilObject.map` whose *target*
endofunctor is the identity. It is the composite of the compact-support exchange
isomorphism `Ex_!` of the Frobenius square of `a_X`
(`Etale.frobeniusLowerShriekStructCompatibility`) with the Frobenius invariance `c_σ` of
derived global sections on the geometric point
(`Etale.upperStarCompRightDerivedGlobalSectionsPlusIso`): the `σ` produced by the first
is absorbed by the second. -/
def Etale.frobeniusCompactlySupportedCompatibility (hΛ : IsAddTorsion Λ)
    (c₀ : Compactification aX) :
    Etale.compactlySupportedGlobalSectionsPlus Λ c₀.geometricFiberStruct ⋙
        𝟭 (DerivedCategory.Plus (ModuleCat.{u + 1} Λ)) ≅
      (Etale.frobeniusPullback (ModuleCat.{u + 1} Λ) aX).mapDerivedCategoryPlus ⋙
        Etale.compactlySupportedGlobalSectionsPlus Λ c₀.geometricFiberStruct :=
  Functor.rightUnitor _ ≪≫
    Functor.isoWhiskerLeft Rf_!(c₀.geometricFiberStruct)[ModuleCat.{u + 1} Λ]+
      (Etale.upperStarCompRightDerivedGlobalSectionsPlusIso (ModuleCat.{u + 1} Λ)
        (specGeometricFrobenius k)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Etale.frobeniusLowerShriekStructCompatibility Λ hΛ c₀) _ ≪≫
    Functor.associator _ _ _

/-- **The geometric Frobenius on `RΓc(X, K)`**: a bounded below Weil complex `(K, Φ_K)`
on the geometric fiber is sent to `RΓc(X, K)` equipped with the automorphism

`RΓc(X, K) --c_σ⁻¹--> RΓ(s, Lσ^* Ra_{X!} K) --Ex_!--> RΓ(s, Ra_{X!} G_X K)
  --RΓ(s, Ra_{X!} Φ_K)--> RΓc(X, K)`,

the transport of `CategoryTheory.WeilObject.map` along
`Etale.frobeniusCompactlySupportedCompatibility`. Since the target endofunctor is the
identity, the transported Weil structure *is* an automorphism, the `F_{K,1}` of the
reference; the `F_{K,n}` of the trace formula are its powers. -/
def WeilComplexPlus.compactlySupportedGlobalSections (hΛ : IsAddTorsion Λ)
    (c₀ : Compactification aX) :
    WeilComplexPlus (ModuleCat.{u + 1} Λ) aX ⥤
      WeilObject (𝟭 (DerivedCategory.Plus (ModuleCat.{u + 1} Λ))) :=
  WeilObject.map (Etale.frobeniusCompactlySupportedCompatibility Λ hΛ c₀)

/-- **The geometric Frobenius on `H_c^i(X, K)`**: the `i`-th homology object of
`RΓc(X, K)` together with the automorphism `F^i_{K,1} := Hⁱ(F_{K,1})` induced by the
Frobenius of `Etale.WeilComplexPlus.compactlySupportedGlobalSections`. Finiteness of
`H_c^i(X, K)` is a theorem, not part of the definition. -/
def WeilComplexPlus.compactlySupportedCohomology (i : ℤ) (hΛ : IsAddTorsion Λ)
    (c₀ : Compactification aX) :
    WeilComplexPlus (ModuleCat.{u + 1} Λ) aX ⥤ WeilObject (𝟭 (ModuleCat.{u + 1} Λ)) :=
  WeilComplexPlus.compactlySupportedGlobalSections Λ hΛ c₀ ⋙
    WeilObject.map (F := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)
      (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

end CompactlySupported

end AlgebraicGeometry

end

end
