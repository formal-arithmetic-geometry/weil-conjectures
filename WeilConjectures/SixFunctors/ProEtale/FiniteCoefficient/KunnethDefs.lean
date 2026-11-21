/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Finite-coefficient pro-étale definitions for the ordinary Künneth formula

The pro-étale definitions for the ordinary Künneth formula, at a Noetherian commutative
coefficient ring `Λ` (typically the finite ring `𝒪_E/ϖⁿ`): they are the pro-étale functors and
projection maps of the repository specialised to the coefficients `ModuleCat Λ`.

- `AlgebraicGeometry.ProEtale.rightDerivedGlobalSectionsModule` (derived sections, pro-étale
  case).
- `AlgebraicGeometry.ProEtale.IndEtaleTestObject` (affine ind-étale test objects) and the
  restriction `AlgebraicGeometry.ProEtale.IndEtaleTestObject.restrict`.
- `AlgebraicGeometry.ProEtale.starProjectionMapModule` (direct-image projection map).
- `AlgebraicGeometry.ProEtale.openProjectionMapModule` (open-extension projection map).
- `AlgebraicGeometry.ProEtale.shriekProjectionMapModule` (compact-support projection map).

## Implementation notes

The three projection maps are stated as natural transformations of bifunctors, whose
`(K, L)`-components are the expected morphisms: stating the components for objects `K`
of `D(X_proét, Λ)` elaborated afresh at `ModuleCat Λ` makes the kernel compare instances of
the sheaf categories found along different paths, which it fails to do in reasonable time.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Derived sections (pro-étale case).

For a scheme `W`, `RΓ_{W,proét,Λ} : D(W_proét, Λ) ⥤ D(Mod_Λ)` is the total right derived
functor, computed on K-injective resolutions, of the global sections functor `Γ(W_proét, -)` on
pro-étale sheaves of `Λ`-modules (`AlgebraicGeometry.ProEtale.rightDerivedGlobalSections` for
`A = ModuleCat Λ`). The étale case is `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsModule`. -/
noncomputable abbrev rightDerivedGlobalSectionsModule (W : Scheme.{u}) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ) :=
  rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W

/-- Affine ind-étale test objects.

A test object of `W_proét` is a morphism `u_B : B ⟶ W` factoring as `B ⟶ V ⟶ W` through an
affine open `V ⊆ W`, where `B ⟶ V` is a cofiltered limit of affine schemes étale over `V`
(`AlgebraicGeometry.proAffineEtale`). -/
structure IndEtaleTestObject (W : Scheme.{u}) where
  /-- The affine open `V ⊆ W` through which the test object factors. -/
  V : W.affineOpens
  /-- The test scheme `B = lim_i B_i`. -/
  B : Scheme.{u}
  /-- The morphism `B ⟶ V`. -/
  toOpen : B ⟶ (V : W.Opens).toScheme
  /-- `B ⟶ V` is a cofiltered limit of affine schemes étale over `V`. -/
  proAffineEtale_toOpen : proAffineEtale toOpen

namespace IndEtaleTestObject

variable {W : Scheme.{u}} (T : IndEtaleTestObject W)

/-- The structure morphism `u_B : B ⟶ V ⟶ W` of a test object. -/
noncomputable def hom : T.B ⟶ W :=
  T.toOpen ≫ (T.V : W.Opens).ι

instance : WeaklyEtale T.hom :=
  have : WeaklyEtale T.toOpen := proAffineEtale_le_weaklyEtale _ T.proAffineEtale_toOpen
  inferInstanceAs (WeaklyEtale (T.toOpen ≫ (T.V : W.Opens).ι))

/-- A test object as an object of the pro-étale site of `W`. -/
noncomputable def toProEt : W.ProEt :=
  ProEt.mk T.hom

/-- The restriction `K ↦ Lu_B^* K` of complexes of pro-étale sheaves of `Λ`-modules to a test
object `u_B : B ⟶ W`, with constant coefficients `Λ`. -/
noncomputable abbrev restrict :
    DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T.B) (ModuleCat.{u + 1} Λ)) :=
  L((T.hom)^*[ModuleCat.{u + 1} Λ])

end IndEtaleTestObject

variable [IsNoetherianRing Λ]

/-- Direct-image projection transformation, finite coefficients.

For `f : X ⟶ Y`, `K ∈ D(X_proét, Λ)` and `L ∈ D(Y_proét, Λ)`, this is the natural transformation
of bifunctors with components `P_{f,K,L} : Rf_* K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^* L)`. -/
noncomputable abbrev starProjectionMapModule {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedTensorRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f ⟶
      rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) f :=
  rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f

/-- Open-extension projection map, finite coefficients.

For an open immersion `j : U ⟶ X`, `K ∈ D(U_proét, Λ)` and `N ∈ D(X_proét, Λ)`, this is the natural
transformation of bifunctors with components
`σ_{j,K,N} : D(j_!)(K ⊗ᴸ D(j^*) N) ⟶ D(j_!) K ⊗ᴸ N`. -/
noncomputable abbrev openProjectionMapModule {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Functor.postcompose₂.obj D((j)_!open[ModuleCat.{u + 1} Λ])).obj
        (derivedTensorWhiskeringRightLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) j) ⟶
      derivedTensorWhiskeringLeftOpenImmersionLowerShriek (ModuleCat.{u + 1} Λ) j :=
  derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} Λ) j

/-- Compact-support projection transformation, finite coefficients.

For a compactification `d = (j, p)` of `f`, `K ∈ D(X_proét, Λ)` and `L ∈ D(Y_proét, Λ)`, this is
the natural transformation of bifunctors with components
`PF_{d,K,L} : R_d K ⊗ᴸ L ⟶ R_d(K ⊗ᴸ Lf^* L)`, where `R_d = Rp_* ∘ D(j_!)`. -/
noncomputable abbrev shriekProjectionMapModule {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} Λ) c ⟶
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) c :=
  projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c

end ProEtale

end AlgebraicGeometry
