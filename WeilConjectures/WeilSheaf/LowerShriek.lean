/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Derived
public import WeilConjectures.WeilSheaf.Defs

/-!

# Weil structures through `Rf_!` and the Frobenius on compactly supported cohomology

Let `X₀` be a scheme over a finite field `k` and `X` its geometric fiber with geometric
Frobenius `g_X` and structure morphism `a_X : X ⟶ Spec k̄`. This file transports Weil
structures through the derived lower shriek and produces the geometric Frobenius
operators on compactly supported cohomology. Two ingredients are assumed with `sorry`,
following the trace-formula interface:

- `AlgebraicGeometry.Etale.derivedLowerShriekExchange`: the compact-support base change
  isomorphism `Ex_! : Lg^* ∘ Rq_! ≅ Rp_! ∘ L(g')^*` attached to a Cartesian square;
- `AlgebraicGeometry.Etale.baseFrobeniusRightDerivedGlobalSectionsIso`: the canonical
  isomorphism `c_σ : RΓ(s, Lσ^* M) ≅ RΓ(s, M)` on the separably closed point
  `s = Spec k̄`, where evaluation at the canonical geometric point is exact and
  identifies with global sections.

From these, everything is a transport of Weil objects along a functor equipped with a
commutation isomorphism (`CategoryTheory.WeilObject.map`):

- For a morphism `h : X₀ ⟶ Y₀` over `k`, the Frobenius square of the geometric base
  change `h̄ : X ⟶ Y` is Cartesian
  (`Scheme.Hom.isPullback_geometricFrobenius_geometricFiberMap`), and its `Ex_!` is a
  Frobenius compatibility `G_Y ∘ Rh̄_! ≅ Rh̄_! ∘ G_X`; transporting along it sends a Weil
  complex `(K, Φ)` on `X` to `Rh̄_! K` with the structure isomorphism
  `G_Y Rh̄_! K ≅ Rh̄_! G_X K ≅ Rh̄_! K` (`AlgebraicGeometry.WeilComplex.lowerShriek`).
- For the structure morphism `a_X` the same transport along the Cartesian Frobenius
  square `a_X ∘ g_X = σ ∘ a_X` lands in Weil objects on `s` for the endofunctor
  `Lσ^*` (`AlgebraicGeometry.WeilComplex.lowerShriekToBase`).
- Composing with `RΓ(s, -)` along `c_σ` lands in Weil objects for the *identity*
  endofunctor of `D(A)`: an object together with an automorphism. The underlying object
  is `RΓc(X, K) = RΓ(s, Ra_{X!} K)` and the structure isomorphism *is* the global
  geometric Frobenius
  `F_K : RΓc(X, K) ≅ RΓc(X, K)`
  (`AlgebraicGeometry.WeilComplex.frobeniusCompactlySupportedGlobalSections`); its
  homology gives the Frobenius on compactly supported cohomology
  `F_K^i : H_c^i(X, K) ≅ H_c^i(X, K)`
  (`AlgebraicGeometry.WeilComplex.frobeniusCompactlySupportedCohomology`).

Every operator here is a functorial image of the single structure isomorphism `Φ`; no
Frobenius on cohomology is chosen independently.

-/

@[expose] public section

universe w w' u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

section Exchange

variable {W X Y Z : Scheme.{u}} {g' : W ⟶ X} {p : W ⟶ Y} {q : X ⟶ Z} {g : Y ⟶ Z}
variable [HasCompactification p] [HasCompactification q]
variable [∀ F : Z.Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F]
variable [∀ F : X.Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ g').op.HasLeftKanExtension F]
variable [HasDerivedCategory.{w} (Sheaf W.smallEtaleTopology A)]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w} (Sheaf Y.smallEtaleTopology A)]
variable [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]

/-- The compact-support base change isomorphism `Ex_!` attached to a Cartesian square

```
W  -- g' -->  X
|             |
p             q
v             v
Y  --  g -->  Z
```

of schemes: the exchange isomorphism `Lg^* ∘ Rq_! ≅ Rp_! ∘ L(g')^*` between the derived
pullbacks and the derived lower shrieks. This is part of the six-functor formalism and
is assumed here (stated with `sorry`); applied to Frobenius squares it transports Weil
structures through `Rf_!`. -/
noncomputable def Etale.derivedLowerShriekExchange (sq : IsPullback g' p q g) :
    Etale.rightDerivedLowerShriek A q ⋙ (Etale.upperStar A g).mapDerivedCategory ≅
      (Etale.upperStar A g').mapDerivedCategory ⋙ Etale.rightDerivedLowerShriek A p :=
  sorry

end Exchange

section LowerShriek

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}}
  (fY : Y₀ ⟶ Spec (.of k)) (h : X₀ ⟶ Y₀)
variable [HasCompactification (fY.geometricFiberMap h)]
variable [∀ F : (fY.geometricFiber).Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ fY.geometricFrobenius.hom).op.HasLeftKanExtension F]
variable [∀ F : ((h ≫ fY).geometricFiber).Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤
    (h ≫ fY).geometricFrobenius.hom).op.HasLeftKanExtension F]
variable [HasDerivedCategory.{w} (Sheaf ((h ≫ fY).geometricFiber).smallEtaleTopology A)]
variable [HasDerivedCategory.{w} (Sheaf (fY.geometricFiber).smallEtaleTopology A)]

/-- The Weil structure on the derived lower shriek: for a morphism `h : X₀ ⟶ Y₀` over
the finite base field with geometric base change `h̄ : X ⟶ Y`, the compact-support base
change isomorphism of the Cartesian Frobenius square `h̄ ∘ g_X = g_Y ∘ h̄` is a Frobenius
compatibility `G_Y ∘ Rh̄_! ≅ Rh̄_! ∘ G_X`, and a Weil complex `(K, Φ)` on `X` transports
to `Rh̄_! K` with the structure isomorphism `G_Y Rh̄_! K ≅ Rh̄_! G_X K ≅ Rh̄_! K`. -/
noncomputable def WeilComplex.lowerShriek :
    WeilComplex A (h ≫ fY) ⥤ WeilComplex A fY :=
  WeilObject.map
    (Etale.derivedLowerShriekExchange A (fY.isPullback_geometricFrobenius_geometricFiberMap h))

end LowerShriek

section BaseFrobenius

variable (k : Type u) [Field k] [Finite k]
variable [∀ F : (Spec (.of (AlgebraicClosure k))).Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤
    (specGeometricFrobenius k).hom).op.HasLeftKanExtension F]
variable [HasDerivedCategory.{w}
  (Sheaf (Spec (.of (AlgebraicClosure k))).smallEtaleTopology A)]

/-- The derived Frobenius pullback `Lσ^*` on the derived category of étale sheaves on
the base point `s = Spec k̄`, the derived pullback along the geometric Frobenius `σ` of
the algebraic closure. Weil complexes on `X` transport through `Ra_{X!}` to Weil
objects on `s` for this endofunctor. -/
noncomputable abbrev Etale.derivedBaseFrobeniusPullback :
    DerivedCategory (Sheaf (Spec (.of (AlgebraicClosure k))).smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf (Spec (.of (AlgebraicClosure k))).smallEtaleTopology A) :=
  (Etale.upperStar A (specGeometricFrobenius k).hom).mapDerivedCategory

variable [HasDerivedCategory.{w'} A]

/-- The canonical isomorphism `c_σ : RΓ(s, Lσ^* M) ≅ RΓ(s, M)` on the separably closed
point `s = Spec k̄`: evaluation at the canonical geometric point is exact and
canonically identifies with global sections, which are invariant under pullback along
the automorphism `σ`. This is part of the trace-formula interface and is assumed here
(stated with `sorry`). -/
noncomputable def Etale.baseFrobeniusRightDerivedGlobalSectionsIso :
    Etale.derivedBaseFrobeniusPullback A k ⋙
      Etale.rightDerivedGlobalSections A (Spec (.of (AlgebraicClosure k))) ≅
        Etale.rightDerivedGlobalSections A (Spec (.of (AlgebraicClosure k))) :=
  sorry

end BaseFrobenius

section CompactlySupportedFrobenius

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
variable [HasCompactification f.geometricFiberStruct]
variable [∀ F : (f.geometricFiber).Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ f.geometricFrobenius.hom).op.HasLeftKanExtension F]
variable [∀ F : (Spec (.of (AlgebraicClosure k))).Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤
    (specGeometricFrobenius k).hom).op.HasLeftKanExtension F]
variable [HasDerivedCategory.{w} (Sheaf (f.geometricFiber).smallEtaleTopology A)]
variable [HasDerivedCategory.{w}
  (Sheaf (Spec (.of (AlgebraicClosure k))).smallEtaleTopology A)]

/-- Transport of the Weil structure through `Ra_{X!}` along the structure morphism
`a_X : X ⟶ Spec k̄` of the geometric fiber: the compact-support base change isomorphism
of the Cartesian Frobenius square `a_X ∘ g_X = σ ∘ a_X` sends a Weil complex `(K, Φ)`
on `X` to `Ra_{X!} K` with the structure isomorphism
`Lσ^* Ra_{X!} K ≅ Ra_{X!} G_X K ≅ Ra_{X!} K`, a Weil object on `s` for `Lσ^*`. -/
noncomputable def WeilComplex.lowerShriekToBase :
    WeilComplex A f ⥤ WeilObject (Etale.derivedBaseFrobeniusPullback A k) :=
  WeilObject.map (Etale.derivedLowerShriekExchange A f.isPullback_geometricFrobenius)

variable [HasDerivedCategory.{w'} A]

/-- The compactly supported global sections of a Weil complex, as a Weil object for the
*identity* endofunctor of `D(A)`: the transport of the Weil structure through
`Ra_{X!}` and then through `RΓ(s, -)` along `c_σ`. The underlying object is
`RΓc(X, K) = RΓ(s, Ra_{X!} K)` and the structure isomorphism is the global geometric
Frobenius `F_K`. -/
noncomputable def WeilComplex.compactlySupportedGlobalSections :
    WeilComplex A f ⥤ WeilObject (𝟭 (DerivedCategory A)) :=
  WeilComplex.lowerShriekToBase A f ⋙
    WeilObject.map
      ((Etale.rightDerivedGlobalSections A (Spec (.of (AlgebraicClosure k)))).rightUnitor ≪≫
        (Etale.baseFrobeniusRightDerivedGlobalSectionsIso A k).symm)

/-- The global geometric Frobenius `F_K : RΓc(X, K) ≅ RΓc(X, K)` on the compactly
supported derived global sections of a Weil complex `(K, Φ)`:

`RΓc(X, K) ≅ RΓ(s, Lσ^* Ra_{X!} K) ≅ RΓ(s, Ra_{X!} G_X K) ≅ RΓc(X, K)`

via `c_σ`, the exchange isomorphism `Ex_!`, and `Φ`. It is the structure isomorphism of
`WeilComplex.compactlySupportedGlobalSections`, not a separately chosen operator. -/
noncomputable def WeilComplex.frobeniusCompactlySupportedGlobalSections
    (K : WeilComplex A f) :
    (Etale.compactlySupportedGlobalSections A f.geometricFiberStruct).obj K.obj ≅
      (Etale.compactlySupportedGlobalSections A f.geometricFiberStruct).obj K.obj :=
  ((WeilComplex.compactlySupportedGlobalSections A f).obj K).str

/-- The geometric Frobenius `F_K^i : H_c^i(X, K) ≅ H_c^i(X, K)` on the compactly
supported cohomology of a Weil complex `(K, Φ)`, the homology of the global geometric
Frobenius on `RΓc(X, K)`. -/
noncomputable def WeilComplex.frobeniusCompactlySupportedCohomology
    (i : ℤ) (K : WeilComplex A f) :
    (Etale.compactlySupportedCohomology A f.geometricFiberStruct i).obj K.obj ≅
      (Etale.compactlySupportedCohomology A f.geometricFiberStruct i).obj K.obj :=
  (DerivedCategory.homologyFunctor A i).mapIso
    (WeilComplex.frobeniusCompactlySupportedGlobalSections A f K)

end CompactlySupportedFrobenius

end AlgebraicGeometry

end
