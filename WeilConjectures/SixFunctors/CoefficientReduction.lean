/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeLowerStarDualizable
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsHom
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerStarFree
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.CoefficientChange.CoefficientTransformationComparisons

/-!
# The basic operations and reduction of the coefficients

Let `Λ` be a commutative ring and `ϖ` a nonzerodivisor of `Λ`, the intended case being
`Λ = 𝒪_E` with a uniformizer `ϖ`, so that `Λ ⧸ (ϖ)ⁿ = A_{E,n}`. The reduction of a complex `K`
of sheaves of `Λ`-modules is its derived base change `K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`, characterised by
its universal property (`CategoryTheory.Sheaf.IsDerivedBaseChange`) and read in `D(Λ)` through
restriction of scalars. The main statement is that this reduction commutes with the basic
operations, compatibly with the units and counits out of which the projection and exchange
transformations are built.

The compatibilities are recorded as propositions: reduction `Λ → Λ ⧸ (ϖ)ⁿ` for the étale and for
the pro-étale model of the coefficient categories, reduction between finite quotients, and the
common-stage scalar extension `𝒪_E → 𝒪_{E'}` with its rationalization. They are assembled in
`AlgebraicGeometry.CoefficientChangeCompatibility`, and the main statement is
`AlgebraicGeometry.coefficientChangeCompatibility`.

## Main definitions

- `AlgebraicGeometry.Etale.projectionMapApp`: the component `PF_{f, K, L}` of the étale
  projection map over a coefficient ring `Λ'`.
- `AlgebraicGeometry.Etale.ReductionCompatibility`,
  `AlgebraicGeometry.ProEtale.ReductionCompatibility`: reduction modulo `Iⁿ` commutes with the
  basic operations (including `Rf^!`), the projection map, the unit and counit of `Rf_! ⊣ Rf^!`
  and the compact-support exchange map.
- `AlgebraicGeometry.Etale.BaseChangeCompatibility`,
  `AlgebraicGeometry.ProEtale.BaseChangeCompatibility`: derived base change along a ring
  morphism commutes with the basic operations and the projection (resp. exchange) map.
- `AlgebraicGeometry.Etale.FiniteReductionCompatibility`,
  `AlgebraicGeometry.Etale.ScalarExtensionCompatibility` and their pro-étale analogues: the
  instances for the reduction between finite quotients and for the scalar extension between
  finite extensions of `ℚ_ℓ`.

## Main statements

- `AlgebraicGeometry.coefficientChangeCompatibility`: the reduction of coefficients commutes with
  the basic operations.
- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_leftDerivedUpperStar`,
  `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_derivedTensor` and their pro-étale
  analogues: derived pullback and derived tensor product commute with derived base change along
  any ring morphism.
- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_rightDerivedLowerStar_of_isIso`,
  `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_rightDerivedLowerShriek_of_isIso` and their
  pro-étale analogues: the (compact-support) direct image commutes with derived base change as
  soon as the base change map of `Rg_*` is an isomorphism, which holds for the reduction modulo
  `(ϖ)ⁿ` and for finite free scalar extensions.
- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap`:
  the reduction of `PF_{f, K, L}` modulo `(ϖ)ⁿ` is isomorphic, as an arrow, to the restriction
  of scalars of `PF_{f, K_n, L_n}`.
- `nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap`
  (in the namespace `AlgebraicGeometry.ProEtale`): the reduction of the pro-étale exchange map
  `Ex_!(c)` at `K` is isomorphic, as an arrow, to the restriction of scalars of `Ex_!(c)` at
  `K_n`.

## Implementation details

The two clauses are proved in this file, from `coefficientChangeCompatibility`, rather than in
the files using them: restating a statement involving the monoidal structure of the derived
categories over a quotient ring in another module and closing it with that theorem makes the kernel
compare independently elaborated instances, which does not terminate in practice.

`coefficientChangeCompatibility` is assembled from one theorem per coefficient change
(`AlgebraicGeometry.Etale.reductionCompatibility` and its siblings), so that each field is proved
in place, without restating its statement.
-/

@[expose] public section

-- Elaborate the derived-category helpers sequentially to bound memory use.
set_option Elab.async false

universe u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

noncomputable section
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.Sheaf
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (φ : A →+* B)

attribute [local instance 2000] CommRing.toRing
attribute [local instance high] SymmetricCategory.toBraidedCategory

omit [EssentiallySmall.{u + 1} C] in
private lemma coefficientCountableCoproducts (R : Type (u + 1)) [CommRing R] :
    HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
  ⟨fun _ _ => (inferInstance : HasColimitsOfSize.{0, 0}
    (Sheaf J (ModuleCat.{u + 1} R))).has_colimits_of_shape _⟩

attribute [local instance] coefficientCountableCoproducts

private lemma scalar_preservesKFlatQuasiIso :
    (extendScalars J φ).PreservesKFlatQuasiIso := by
  let : Algebra A B := φ.toAlgebra
  have := reflectsIsomorphisms_restrictScalars J φ
  exact ⟨fun hK hL f _ => CochainComplex.quasiIso_map_of_iso_tensorRight _ _
    (extendScalarsCompRestrictScalarsIso J A B) f hK hL⟩

@[irreducible] private noncomputable def scalarDerivedAdjunction :
    have := scalar_preservesKFlatQuasiIso J φ
    (extendScalars J φ).leftDerivedFunctor ⊣ derivedRestrictScalars J φ :=
  have := scalar_preservesKFlatQuasiIso J φ
  (extendScalarsAdjunction J φ).derivedAdjunction.ofNatIsoRight
    (restrictScalars J φ).rightDerivedFunctorIsoMapDerivedCategory

end CategoryTheory.Sheaf

end

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The component `PF_{f, K, L}` of the projection map over a coefficient ring `Λ'`.

Stating results at a quotient ring `Λ ⧸ (ϖ)ⁿ` through this constant keeps the monoidal structure
of the derived categories out of their statements: comparing a freshly elaborated projection map
over `Λ ⧸ (ϖ)ⁿ` with an instance of a generic one makes the kernel compare the nested proofs of
the two elaborated monoidal instances, which does not terminate in practice. -/
noncomputable def projectionMapApp (Λ' : Type (u + 1)) [CommRing Λ'] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : 𝐃(X, Λ')) (L : 𝐃(Y, Λ')) :=
  ((projectionMap (ModuleCat.{u + 1} Λ') f).app K).app L

/-- Restriction of scalars `D(X_ét, Λ ⧸ Iⁿ) ⥤ D(X_ét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " I ", " n "]" =>
  derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X

/-- The compatibility of the reduction `Λ → Λ ⧸ Iⁿ` with the basic operations of the étale
derived categories: every object has a reduction (a derived base change along `Λ → Λ ⧸ Iⁿ`);
the derived pullback, tensor product, direct image, compact-support direct image, internal Hom
and exceptional inverse image `Rf^!` of reductions are reductions of the corresponding
operations; and the reductions of the projection map `PF_{f, K, L}` and of the unit and counit of
`Rf_! ⊣ Rf^!` are, as arrows, the restrictions of scalars of the corresponding maps over
`Λ ⧸ Iⁿ`. -/
structure ReductionCompatibility (Λ : Type (u + 1)) [CommRing Λ] (I : Ideal Λ) (n : ℕ) :
    Prop where
  /-- Every object has a reduction modulo `Iⁿ`. -/
  exists_isDerivedBaseChange (X : Scheme.{u}) (K : 𝐃(X, Λ)) :
    ∃ (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn), IsDerivedBaseChange η
  /-- The derived pullback commutes with reduction modulo `Iⁿ`. -/
  leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (L : 𝐃(Y, Λ))
    (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln) (hη : IsDerivedBaseChange η) :
    ∃ θ : L((f)^*[ModuleCat.{u + 1} Λ]).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (L((f)^*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Ln),
      IsDerivedBaseChange θ
  /-- The derived tensor product commutes with reduction modulo `Iⁿ`. -/
  derivedTensor {X : Scheme.{u}} (K L : 𝐃(X, Λ)) (Kn Ln : 𝐃(X, Λ ⧸ I ^ n))
    (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (η' : L ⟶ 𝐑𝐞𝐬[X, I, n].obj Ln)
    (hη : IsDerivedBaseChange η) (hη' : IsDerivedBaseChange η') :
    ∃ θ : ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn).obj Ln),
      IsDerivedBaseChange θ
  /-- The derived direct image commutes with reduction modulo `Iⁿ`. -/
  rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (hη : IsDerivedBaseChange η) :
    ∃ θ : R((f)_*[ModuleCat.{u + 1} Λ]).obj K ⟶
      𝐑𝐞𝐬[Y, I, n].obj (R((f)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn),
      IsDerivedBaseChange θ
  /-- The compact-support direct image commutes with reduction modulo `Iⁿ`. -/
  rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃(X, Λ)) (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn)
    (hη : IsDerivedBaseChange η) :
    ∃ θ : (R(f)_![ModuleCat.{u + 1} Λ]).obj K ⟶
      𝐑𝐞𝐬[Y, I, n].obj ((R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn),
      IsDerivedBaseChange θ
  /-- The reduction of the projection map is the projection map of the reductions. -/
  projectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (K : 𝐃(X, Λ))
    (L : 𝐃(Y, Λ)) (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn)
    (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η' : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln) (hη : IsDerivedBaseChange η)
    (hη' : IsDerivedBaseChange η') :
    Nonempty (Arrow.mk ((reductionModIdeal Λ Y (I ^ n)).map (projectionMapApp Λ f K L)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y, I, n].map (projectionMapApp (Λ ⧸ I ^ n) f Kn Ln)))
  /-- The internal Hom, with arbitrary first variable, commutes with reduction modulo `Iⁿ`. -/
  derivedHom {X : Scheme.{u}} (K L : 𝐃(X, Λ)) (Kn Ln : 𝐃(X, Λ ⧸ I ^ n))
    (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (η' : L ⟶ 𝐑𝐞𝐬[X, I, n].obj Ln)
    (hη : IsDerivedBaseChange η) (hη' : IsDerivedBaseChange η') :
    ∃ θ : ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X).obj (op Kn)).obj Ln),
      IsDerivedBaseChange θ
  /-- The exceptional inverse image `Rf^!`, the right adjoint of `Rf_!`, commutes with
  reduction modulo `Iⁿ`. -/
  rightDerivedUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).IsLeftAdjoint]
    (L : 𝐃(Y, Λ)) (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln)
    (hη : IsDerivedBaseChange η) :
    ∃ θ : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj ((R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).rightAdjoint.obj Ln),
      IsDerivedBaseChange θ
  /-- The reduction of the counit `Rf_! Rf^! L ⟶ L` of `Rf_! ⊣ Rf^!` is the counit over
  `Λ ⧸ Iⁿ` at the reduction `L_n`. -/
  upperShriekCounit {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).IsLeftAdjoint]
    (L : 𝐃(Y, Λ)) (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln)
    (hη : IsDerivedBaseChange η) :
    Nonempty (Arrow.mk ((reductionModIdeal Λ Y (I ^ n)).map
        ((Adjunction.ofIsLeftAdjoint
          (R(f)_![ModuleCat.{u + 1} Λ])).counit.app L)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y, I, n].map
        ((Adjunction.ofIsLeftAdjoint
          (R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)])).counit.app Ln)))
  /-- The reduction of the unit `K ⟶ Rf^! Rf_! K` of `Rf_! ⊣ Rf^!` is the unit over `Λ ⧸ Iⁿ`
  at the reduction `K_n`. -/
  upperShriekUnit {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).IsLeftAdjoint]
    (K : 𝐃(X, Λ)) (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn)
    (hη : IsDerivedBaseChange η) :
    Nonempty (Arrow.mk ((reductionModIdeal Λ X (I ^ n)).map
        ((Adjunction.ofIsLeftAdjoint
          (R(f)_![ModuleCat.{u + 1} Λ])).unit.app K)) ≅
      Arrow.mk (𝐑𝐞𝐬[X, I, n].map
        ((Adjunction.ofIsLeftAdjoint
          (R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)])).unit.app Kn)))

/-- Compatibility of the derived base change along a ring morphism `φ : Λ →+* Λ'` with the basic
operations of the étale derived categories, on the objects satisfying `P`: the derived pullback,
tensor product and compact-support direct image of derived base changes are derived base changes
of the corresponding operations, and the projection map `PF_{f, K', L'}` of the base changes is
the base change of `PF_{f, K, L}`: there is a commutative square from `PF_{f, K, L}` to the
restriction of scalars of `PF_{f, K', L'}` whose two sides exhibit derived base changes. -/
structure BaseChangeCompatibility {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ']
    (φ : Λ →+* Λ') (P : ∀ X : Scheme.{u}, ObjectProperty 𝐃(X, Λ)) : Prop where
  /-- The derived pullback commutes with derived base change. -/
  leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (L : 𝐃(Y, Λ)) (hL : P Y L)
    (L' : 𝐃(Y, Λ')) (η : L ⟶ (derivedRestrictScalars φ Y).obj L')
    (hη : IsDerivedBaseChange η) :
    ∃ θ : L((f)^*[ModuleCat.{u + 1} Λ]).obj L ⟶
      (derivedRestrictScalars φ X).obj (L((f)^*[ModuleCat.{u + 1} Λ']).obj L'),
      IsDerivedBaseChange θ
  /-- The derived tensor product commutes with derived base change. -/
  derivedTensor {X : Scheme.{u}} (K L : 𝐃(X, Λ)) (hK : P X K) (hL : P X L) (K' L' : 𝐃(X, Λ'))
    (η : K ⟶ (derivedRestrictScalars φ X).obj K') (η' : L ⟶ (derivedRestrictScalars φ X).obj L')
    (hη : IsDerivedBaseChange η) (hη' : IsDerivedBaseChange η') :
    ∃ θ : ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj L ⟶
      (derivedRestrictScalars φ X).obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ']).obj K').obj L'),
      IsDerivedBaseChange θ
  /-- The compact-support direct image commutes with derived base change. -/
  rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃(X, Λ)) (hK : P X K) (K' : 𝐃(X, Λ')) (η : K ⟶ (derivedRestrictScalars φ X).obj K')
    (hη : IsDerivedBaseChange η) :
    ∃ θ : (R(f)_![ModuleCat.{u + 1} Λ]).obj K ⟶
      (derivedRestrictScalars φ Y).obj ((R(f)_![ModuleCat.{u + 1} Λ']).obj K'),
      IsDerivedBaseChange θ
  /-- The projection map of the derived base changes is the base change of the projection
  map. -/
  projectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (K : 𝐃(X, Λ))
    (L : 𝐃(Y, Λ)) (hK : P X K) (hL : P Y L) (K' : 𝐃(X, Λ'))
    (η : K ⟶ (derivedRestrictScalars φ X).obj K') (L' : 𝐃(Y, Λ'))
    (η' : L ⟶ (derivedRestrictScalars φ Y).obj L') (hη : IsDerivedBaseChange η)
    (hη' : IsDerivedBaseChange η') :
    ∃ (θ₁ : (Arrow.mk (projectionMapApp Λ f K L)).left ⟶
        (derivedRestrictScalars φ Y).obj (Arrow.mk (projectionMapApp Λ' f K' L')).left)
      (θ₂ : (Arrow.mk (projectionMapApp Λ f K L)).right ⟶
        (derivedRestrictScalars φ Y).obj (Arrow.mk (projectionMapApp Λ' f K' L')).right),
      IsDerivedBaseChange θ₁ ∧ IsDerivedBaseChange θ₂ ∧
        θ₁ ≫ (derivedRestrictScalars φ Y).map (projectionMapApp Λ' f K' L') =
          projectionMapApp Λ f K L ≫ θ₂

/-- The compatibility of the reduction `Λ ⧸ Iⁿ → Λ ⧸ Iᵐ` between two finite quotients, for
`m ≤ n` (for `Λ = 𝒪_E`, the reduction `A_{E,n} → A_{E,m}`), with the basic operations of the
étale derived categories: derived pullback, derived tensor product, compact-support direct image
and the projection map commute with it on `Dctf`, the bounded constructible objects of finite
Tor amplitude; and the internal
Hom commutes with it when its first variable is perfect on the coefficient site. -/
structure FiniteReductionCompatibility (Λ : Type (u + 1)) [CommRing Λ] (I : Ideal Λ) {m n : ℕ}
    (h : m ≤ n) : Prop extends
    BaseChangeCompatibility (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) h))
      fun X ↦ DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X where
  /-- The internal Hom with site-perfect first variable commutes with reduction. -/
  derivedHom {X : Scheme.{u}} (K L : 𝐃(X, Λ ⧸ I ^ n)) (hK : DerivedCategory.IsSitePerfect K)
    (K' L' : 𝐃(X, Λ ⧸ I ^ m))
    (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) X).obj K')
    (η' : L ⟶
      (derivedRestrictScalars (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) X).obj L')
    (hη : IsDerivedBaseChange η) (hη' : IsDerivedBaseChange η') :
    ∃ θ : ((derivedHom (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X).obj (op K)).obj L ⟶
      (derivedRestrictScalars (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) X).obj
        (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ I ^ m)) X).obj (op K')).obj L'),
      IsDerivedBaseChange θ

section ScalarExtension

set_option hygiene false in
/-- The derived category `D(X_ét, 𝒪_E)` of the integral stage. The ring structure is written as
the one underlying the commutative ring structure, as in the statements for general commutative
coefficient rings. -/
local notation "𝐃𝐎(" X ", " E ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X)
    (@ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)) CommRing.toRing))

/-- The compatibility of the scalar extension `𝒪_E → 𝒪_{E'}` between two finite extensions
`E ⊆ E'` of `ℚ_ℓ` inside `ℚ̄_ℓ` with the basic operations: derived pullback, derived tensor
product, derived direct image, compact-support direct image and the projection map commute with
the derived base change along `𝒪_E → 𝒪_{E'}`; and after rationalization, the scalar extension
`- ⊗_E E' : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, E')` of the projection map over `E` is, as an arrow,
the projection map over `E'` of the scalar extensions. -/
structure ScalarExtensionCompatibility (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E]
    [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E'] : Prop extends
    BaseChangeCompatibility.{u} (PadicAlgCl.integersShrinkMap l E E') fun _ _ ↦ True where
  /-- The derived direct image commutes with the scalar extension. -/
  rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝐃𝐎(X, E)) (K' : 𝐃𝐎(X, E'))
    (η : K ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E E') X).obj K')
    (hη : IsDerivedBaseChange η) :
    ∃ θ : R((f)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj K ⟶
      (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E E') Y).obj
        (R((f)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E'))]).obj K'),
      IsDerivedBaseChange θ
  /-- The rational scalar extension of the projection map over `E` is the projection map over
  `E'` of the scalar extensions. -/
  rationalProjectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃𝐎(X, E)) (L : 𝐃𝐎(Y, E)) (K' : 𝐃𝐎(X, E'))
    (η : K ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E E') X).obj K')
    (L' : 𝐃𝐎(Y, E'))
    (η' : L ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E E') Y).obj L')
    (hη : IsDerivedBaseChange η) (hη' : IsDerivedBaseChange η') :
    Nonempty (Arrow.mk ((derivedCompleteRationalScalarExtension l E E').map
        ((DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).map
          ((DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E).map
            (projectionMapApp (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L)))) ≅
      Arrow.mk ((DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E').map
          ((DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E').map
            (projectionMapApp (Shrink.{u + 1} (PadicAlgCl.integers l E')) f K' L'))))

end ScalarExtension
end Etale

namespace ProEtale

set_option hygiene false in
/-- The derived category `D(X_proét, Λ)` of pro-étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

/-- Restriction of scalars `D(X_proét, Λ ⧸ Iⁿ) ⥤ D(X_proét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " I ", " n "]" =>
  Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk (I ^ n))

/-- The compatibility of the reduction `Λ → Λ ⧸ Iⁿ` with the basic operations of the pro-étale
derived categories: every object has a reduction (a derived base change along `Λ → Λ ⧸ Iⁿ`);
the derived pullback, tensor product, direct image, compact-support direct image, internal Hom
and exceptional inverse image of reductions are reductions of the corresponding operations; and
the reduction of the compact-support exchange map `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` at
`K` is isomorphic, as an arrow, to the restriction of scalars of the exchange map over `Λ ⧸ Iⁿ`
at `K_n`. -/
structure ReductionCompatibility (Λ : Type (u + 1)) [CommRing Λ] (I : Ideal Λ) (n : ℕ) :
    Prop where
  /-- Every object has a reduction modulo `Iⁿ`. -/
  exists_isDerivedBaseChange (X : Scheme.{u}) (K : 𝐃(X, Λ)) :
    ∃ (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn), Sheaf.IsDerivedBaseChange η
  /-- The derived pullback commutes with reduction modulo `Iⁿ`. -/
  leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (L : 𝐃(Y, Λ))
    (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln) (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : L((f)^*[ModuleCat.{u + 1} Λ]).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (L((f)^*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Ln),
      Sheaf.IsDerivedBaseChange θ
  /-- The compact-support direct image commutes with reduction modulo `Iⁿ`. -/
  rightDerivedLowerShriekOfCompactification {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : 𝐃(X, Λ)) (Kn : 𝐃(X, Λ ⧸ I ^ n))
    (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : (Rf_!(c)[ModuleCat.{u + 1} Λ]).obj K ⟶
      𝐑𝐞𝐬[Y, I, n].obj ((Rf_!(c)[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn),
      Sheaf.IsDerivedBaseChange θ
  /-- The reduction of the compact-support exchange map is the exchange map of the
  reduction. -/
  exchange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty (Arrow.mk
        ((_root_.DerivedCategory.reductionModIdeal (Scheme.ProEt.topology Y') (I ^ n)).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
          c).app K)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y', I, n].map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) sq c).app Kn)))
  /-- The derived tensor product commutes with reduction modulo `Iⁿ`. -/
  derivedTensor {X : Scheme.{u}} (K L : 𝐃(X, Λ)) (Kn Ln : 𝐃(X, Λ ⧸ I ^ n))
    (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (η' : L ⟶ 𝐑𝐞𝐬[X, I, n].obj Ln)
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn).obj Ln),
      Sheaf.IsDerivedBaseChange θ
  /-- The derived direct image commutes with reduction modulo `Iⁿ`. -/
  rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : R((f)_*[ModuleCat.{u + 1} Λ]).obj K ⟶
      𝐑𝐞𝐬[Y, I, n].obj (R((f)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn),
      Sheaf.IsDerivedBaseChange θ
  /-- The internal Hom, with arbitrary first variable, commutes with reduction modulo `Iⁿ`. -/
  derivedHom {X : Scheme.{u}} (K L : 𝐃(X, Λ)) (Kn Ln : 𝐃(X, Λ ⧸ I ^ n))
    (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (η' : L ⟶ 𝐑𝐞𝐬[X, I, n].obj Ln)
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X).obj (op Kn)).obj Ln),
      Sheaf.IsDerivedBaseChange θ
  /-- The exceptional inverse image commutes with reduction modulo `Iⁿ`. -/
  rightDerivedUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) f).IsLeftAdjoint]
    (L : 𝐃(Y, Λ)) (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln)
    (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙
          (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).rightAdjoint ⋙
          D(ν^*(X)[ModuleCat.{u + 1} Λ])).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj ((R(ν_*(Y)[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]) ⋙
          (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) f).rightAdjoint ⋙
          D(ν^*(X)[ModuleCat.{u + 1} (Λ ⧸ I ^ n)])).obj Ln),
      Sheaf.IsDerivedBaseChange θ

/-- Compatibility of the derived base change along a ring morphism `φ : Λ →+* Λ'` with the basic
operations of the pro-étale derived categories, on the objects satisfying `P`: the derived
pullback, tensor product and compact-support direct image of derived base changes are derived
base changes of the corresponding operations, and the compact-support exchange map `Ex_!(c)` at
`K'` is the base change of `Ex_!(c)` at `K`: there is a commutative square from `Ex_!(c)` at `K`
to the restriction of scalars of `Ex_!(c)` at `K'` whose two sides exhibit derived base
changes. -/
structure BaseChangeCompatibility {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ']
    (φ : Λ →+* Λ') (P : ∀ X : Scheme.{u}, ObjectProperty 𝐃(X, Λ)) : Prop where
  /-- The derived pullback commutes with derived base change. -/
  leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (L : 𝐃(Y, Λ)) (hL : P Y L)
    (L' : 𝐃(Y, Λ')) (η : L ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).obj L')
    (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : L((f)^*[ModuleCat.{u + 1} Λ]).obj L ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj
        (L((f)^*[ModuleCat.{u + 1} Λ']).obj L'),
      Sheaf.IsDerivedBaseChange θ
  /-- The derived tensor product commutes with derived base change. -/
  derivedTensor {X : Scheme.{u}} (K L : 𝐃(X, Λ)) (hK : P X K) (hL : P X L) (K' L' : 𝐃(X, Λ'))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K')
    (η' : L ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L')
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj L ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ']).obj K').obj L'),
      Sheaf.IsDerivedBaseChange θ
  /-- The compact-support direct image commutes with derived base change. -/
  rightDerivedLowerShriekOfCompactification {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : 𝐃(X, Λ)) (hK : P X K) (K' : 𝐃(X, Λ'))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K')
    (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : (Rf_!(c)[ModuleCat.{u + 1} Λ]).obj K ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).obj
        ((Rf_!(c)[ModuleCat.{u + 1} Λ']).obj K'),
      Sheaf.IsDerivedBaseChange θ
  /-- The exchange map at the derived base change is the base change of the exchange map. -/
  exchange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃(X, Λ)) (hK : P X K)
    (K' : 𝐃(X, Λ')) (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K')
    (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ (θ₁ : (Arrow.mk ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c).app K)).left ⟶
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y') φ).obj
          (Arrow.mk ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} Λ') sq c).app K')).left)
      (θ₂ : (Arrow.mk ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c).app K)).right ⟶
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y') φ).obj
          (Arrow.mk ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} Λ') sq c).app K')).right),
      Sheaf.IsDerivedBaseChange θ₁ ∧ Sheaf.IsDerivedBaseChange θ₂ ∧
        θ₁ ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y') φ).map
            ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
              (ModuleCat.{u + 1} Λ') sq c).app K') =
          (rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} Λ) sq c).app K ≫ θ₂

/-- The compatibility of the reduction `Λ ⧸ Iⁿ → Λ ⧸ Iᵐ` between two finite quotients, for
`m ≤ n` (for `Λ = 𝒪_E`, the reduction `A_{E,n} → A_{E,m}`), with the derived pullback, the
derived tensor product, the compact-support direct image and the compact-support exchange map of
the pro-étale derived categories, on `Dctf`, the bounded constructible objects of finite Tor
amplitude (at the finite coefficient stages, `Dctf(X, A_{E,n})`). -/
abbrev FiniteReductionCompatibility (Λ : Type (u + 1)) [CommRing Λ] (I : Ideal Λ) {m n : ℕ}
    (h : m ≤ n) : Prop :=
  BaseChangeCompatibility (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) h))
    fun X ↦ DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X

/-- The compatibility of the common-stage scalar extension `𝒪_E → 𝒪_{E'}` between two finite
extensions `E ⊆ E'` of `ℚ_ℓ` inside `ℚ̄_ℓ` with the basic operations of the pro-étale derived
categories: derived pullback, derived tensor product, compact-support direct image and the
compact-support exchange map commute with it, and so does the derived direct image. -/
structure ScalarExtensionCompatibility (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E]
    [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E'] : Prop extends
    BaseChangeCompatibility.{u} (PadicAlgCl.integersShrinkMap l E E') fun _ _ ↦ True where
  /-- The derived direct image commutes with the scalar extension. -/
  rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (K' : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E')))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
      (PadicAlgCl.integersShrinkMap l E E')).obj K')
    (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : R((f)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj K ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y)
        (PadicAlgCl.integersShrinkMap l E E')).obj
        (R((f)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E'))]).obj K'),
      Sheaf.IsDerivedBaseChange θ

end ProEtale

/-- The statement that reduction of coefficients commutes with the basic operations, assembled from
its parts:

* `reduction`, `proEtaleReduction`: for a nonzerodivisor `ϖ` of `Λ` (for `Λ = 𝒪_E` a
  uniformizer, so that `Λ → Λ ⧸ (ϖ)ⁿ` is `𝒪_E → A_{E,n}`), reduction modulo `(ϖ)ⁿ` commutes with
  derived pullback, derived tensor product, ordinary and compact-support direct image, internal
  Hom with arbitrary first variable and the exceptional inverse image `Rf^!`, in the étale and
  in the pro-étale model; it is compatible with the projection map, with the unit and counit of
  `Rf_! ⊣ Rf^!` (étale) and with the compact-support exchange map (pro-étale);
* `finiteReduction`, `proEtaleFiniteReduction`: the reduction `Λ ⧸ (ϖ)ⁿ → Λ ⧸ (ϖ)ᵐ` between
  finite quotients commutes with derived pullback, tensor product and compact-support direct
  image on `Dctf`, compatibly with the projection map (étale) and the exchange map
  (pro-étale), and with internal Hom for site-perfect first variable (étale);
* `scalarExtension`, `proEtaleScalarExtension`: the common-stage scalar extension
  `𝒪_E → 𝒪_{E'}` commutes with the same operations, the projection map (étale) and the exchange
  map (pro-étale), and, in the étale model, also after rationalization. -/
structure CoefficientChangeCompatibility : Prop where
  /-- Reduction `Λ → Λ ⧸ (ϖ)ⁿ` and the étale operations. -/
  reduction {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) :
    Etale.ReductionCompatibility.{u} Λ (Ideal.span {ϖ}) n
  /-- Reduction `Λ → Λ ⧸ (ϖ)ⁿ` and the pro-étale operations. -/
  proEtaleReduction {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) : ProEtale.ReductionCompatibility.{u} Λ (Ideal.span {ϖ}) n
  /-- Reduction `Λ ⧸ (ϖ)ⁿ → Λ ⧸ (ϖ)ᵐ` between finite quotients and the étale operations. -/
  finiteReduction {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    {m n : ℕ} (h : m ≤ n) : Etale.FiniteReductionCompatibility.{u} Λ (Ideal.span {ϖ}) h
  /-- Common-stage scalar extension `𝒪_E → 𝒪_{E'}`, and rationalization. -/
  scalarExtension (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E] [Field E']
    [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E'] :
    Etale.ScalarExtensionCompatibility.{u} l E E'
  /-- Reduction `Λ ⧸ (ϖ)ⁿ → Λ ⧸ (ϖ)ᵐ` between finite quotients and the pro-étale operations. -/
  proEtaleFiniteReduction {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) {m n : ℕ} (h : m ≤ n) :
    ProEtale.FiniteReductionCompatibility.{u} Λ (Ideal.span {ϖ}) h
  /-- Common-stage scalar extension `𝒪_E → 𝒪_{E'}` and the pro-étale operations. -/
  proEtaleScalarExtension (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E] [Field E']
    [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E'] :
    ProEtale.ScalarExtensionCompatibility.{u} l E E'

section CoefficientProofs

-- Keep derived-functor constructions folded while checking their comparisons.
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

-- Elaborate each large proof before starting the next one.
set_option Elab.async false

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

 -- Use the generic commutative coefficient ring instance in proof constructions.
attribute [local instance 2000] CommRing.toRing

private lemma coefficientUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    Sheaf.IsDerivedBaseChange (ad.unit.app K) := by
  intro N
  convert (ad.homEquiv K N).bijective using 1
  funext g
  exact (ad.homEquiv_unit K N g).symm

private lemma coefficientIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
    {K' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) : Nonempty (S.obj K ≅ K') := by
  have := (coefficientUnit J φ ad K).isIso hη ((ad.homEquiv K K').symm η)
    ((ad.homEquiv_unit K K' _).symm.trans ((ad.homEquiv K K').apply_symm_apply η))
  exact ⟨asIso ((ad.homEquiv K K').symm η)⟩

/-- Every object of `D(J, A)` has a derived base change along a ring morphism `φ : A →+* B`: the
unit of derived extension of scalars. -/
theorem _root_.CategoryTheory.Sheaf.exists_isDerivedBaseChange
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    ∃ (K' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
      (η : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj K'), Sheaf.IsDerivedBaseChange η :=
  ⟨_, _, coefficientUnit J φ (Sheaf.scalarDerivedAdjunction J φ) K⟩

private lemma coefficientArrow
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    {K L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))} (a : K ⟶ L)
    {K' L' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))} (b : K' ⟶ L')
    (e : Nonempty (Arrow.mk (S.map a) ≅ Arrow.mk b)) :
    ∃ (θ₁ : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj K')
      (θ₂ : L ⟶ (Sheaf.derivedRestrictScalars J φ).obj L'),
      Sheaf.IsDerivedBaseChange θ₁ ∧ Sheaf.IsDerivedBaseChange θ₂ ∧
      θ₁ ≫ (Sheaf.derivedRestrictScalars J φ).map b = a ≫ θ₂ := by
  obtain ⟨e⟩ := e
  let l : S.obj K ≅ K' := Arrow.leftFunc.mapIso e
  let r : S.obj L ≅ L' := Arrow.rightFunc.mapIso e
  let R := Sheaf.derivedRestrictScalars J φ
  refine ⟨ad.unit.app K ≫ R.map l.hom, ad.unit.app L ≫ R.map r.hom,
    (coefficientUnit J φ ad K).comp_map_iso l,
    (coefficientUnit J φ ad L).comp_map_iso r, ?_⟩
  have he : l.hom ≫ b = S.map a ≫ r.hom := e.hom.w
  have hu : ad.unit.app K ≫ R.map (S.map a) = a ≫ ad.unit.app L := by
    simpa only [Functor.id_map, Functor.comp_map] using (ad.unit.naturality a).symm
  rw [Category.assoc, ← R.map_comp, he, R.map_comp, ← Category.assoc, hu,
    Category.assoc]

namespace Etale

attribute [local instance 2000] CommRing.toRing

-- Keep the two complex-composition comparisons explicit before specializing the sites.
@[irreducible] private noncomputable def cochainSquareIso
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (H : C₁ ⥤ C₃) (I : C₃ ⥤ C₄)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive] (e : F ⋙ G ≅ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).symm

private noncomputable def cochainCounit
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] :
    _root_.DerivedCategory.Q ⋙ F.leftDerivedFunctor ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q :=
  Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) F.leftDerivedFunctorCounit ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom _root_.DerivedCategory.Qh

private lemma cochainCounit_isIso
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
    (P : CochainComplex C ℤ) (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso ((cochainCounit F).app P) := by
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  dsimp only [cochainCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

private lemma comparisonFromResolution
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (F G : D ⥤ E) (H : C ⥤ E) (s : Q ⋙ G ⟶ H) (t : Q ⋙ F ⟶ H)
    (R : C ⥤ C) (π : R ⟶ 𝟭 C)
    (hπ : ∀ X, IsIso (Q.map (π.app X)))
    (hs : ∀ X, IsIso (s.app (R.obj X)))
    (ht : ∀ X, IsIso (t.app (R.obj X))) : Nonempty (F ≅ G) := by
  let : ∀ X, IsIso (Q.map (π.app X)) := hπ
  let : ∀ X, IsIso (s.app (R.obj X)) := hs
  let : ∀ X, IsIso (t.app (R.obj X)) := ht
  have : IsIso (Functor.whiskerRight π (Q ⋙ F)) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    dsimp only [Functor.whiskerRight_app, Functor.comp_map]
    infer_instance
  have : IsIso (Functor.whiskerRight π (Q ⋙ G)) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    dsimp only [Functor.whiskerRight_app, Functor.comp_map]
    infer_instance
  have : IsIso (Functor.whiskerLeft R s) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    exact hs
  have : IsIso (Functor.whiskerLeft R t) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    exact ht
  let e : Q ⋙ F ≅ Q ⋙ G :=
    (asIso (Functor.whiskerRight π (Q ⋙ F))).symm ≪≫
      asIso (Functor.whiskerLeft R t) ≪≫
      (asIso (Functor.whiskerLeft R s)).symm ≪≫
      asIso (Functor.whiskerRight π (Q ⋙ G))
  exact ⟨Localization.liftNatIso Q W (Q ⋙ F) (Q ⋙ G) F G e⟩

-- Prove the resolution comparison with abstract categories, before choosing the sites.
private lemma leftDerivedSquare
    {C D E F : Type*}
    [Category.{u + 1} C] [Category.{u + 1} D]
    [Category.{u + 1} E] [Category.{u + 1} F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [IsGrothendieckAbelian.{u + 1} F]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [MonoidalCategory F] [MonoidalPreadditive F] [MonoidalClosed F] [BraidedCategory F]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    [Abelian.HasFunctorialFlatResolution F]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    [HasDerivedCategory.{u + 1} E] [HasDerivedCategory.{u + 1} F]
    (FA : C ⥤ D) (EX : D ⥤ E) (EY : C ⥤ F) (FB : F ⥤ E)
    [FA.Additive] [EX.Additive] [EY.Additive] [FB.Additive]
    [FA.PreservesKFlatQuasiIso] [EX.PreservesKFlatQuasiIso]
    [EY.PreservesKFlatQuasiIso] [FB.PreservesKFlatQuasiIso]
    [FA.PreservesFlat] [EY.PreservesFlat]
    [PreservesColimitsOfShape ℤ FA] [PreservesColimitsOfShape ℤ EY]
    (e : EY ⋙ FB ≅ FA ⋙ EX) :
    Nonempty (EY.leftDerivedFunctor ⋙ FB.leftDerivedFunctor ≅
      FA.leftDerivedFunctor ⋙ EX.leftDerivedFunctor) := by
  let eC := cochainSquareIso EY FB FA EX e
  let F := EY.leftDerivedFunctor ⋙ FB.leftDerivedFunctor
  let G := FA.leftDerivedFunctor ⋙ EX.leftDerivedFunctor
  let H := FA.mapHomologicalComplex (.up ℤ) ⋙ EX.mapHomologicalComplex (.up ℤ) ⋙
    _root_.DerivedCategory.Q
  let s : _root_.DerivedCategory.Q ⋙ G ⟶ H :=
    Functor.whiskerRight (cochainCounit FA) EX.leftDerivedFunctor ≫
      Functor.whiskerLeft (FA.mapHomologicalComplex (.up ℤ)) (cochainCounit EX)
  let t : _root_.DerivedCategory.Q ⋙ F ⟶ H :=
    Functor.whiskerRight (cochainCounit EY) FB.leftDerivedFunctor ≫
      Functor.whiskerLeft (EY.mapHomologicalComplex (.up ℤ)) (cochainCounit FB) ≫
      Functor.whiskerRight eC.hom _root_.DerivedCategory.Q
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  have hs : ∀ K, IsIso (s.app (Λ.reduced.resolutionFunctor.obj K)) := by
    intro K
    have hF := FA.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
      ObjectProperty.flat.essImage_ι_le K
    have := cochainCounit_isIso EX _ hF
    have := cochainCounit_isIso FA _
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K)
    dsimp only [s, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have ht : ∀ K, IsIso (t.app (Λ.reduced.resolutionFunctor.obj K)) := by
    intro K
    have := cochainCounit_isIso EY _
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K)
    have hE := EY.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
      ObjectProperty.flat.essImage_ι_le K
    have := cochainCounit_isIso FB _ hE
    dsimp only [t, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  exact comparisonFromResolution _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) F G H s t
    Λ.reduced.resolutionFunctor Λ.reduced.resolutionNatTrans (fun _ => inferInstance) hs ht

private lemma scalarPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    have := Sheaf.scalar_preservesKFlatQuasiIso Y.smallEtaleTopology φ
    have := Sheaf.scalar_preservesKFlatQuasiIso X.smallEtaleTopology φ
    Nonempty ((Sheaf.extendScalars Y.smallEtaleTopology φ).leftDerivedFunctor ⋙ L(upperStar
      (ModuleCat.{u + 1} B) f) ≅
      L(upperStar (ModuleCat.{u + 1} A) f) ⋙ (Sheaf.extendScalars X.smallEtaleTopology
        φ).leftDerivedFunctor) := by
  let FA := upperStar (ModuleCat.{u + 1} A) f
  let FB := upperStar (ModuleCat.{u + 1} B) f
  let EY := Sheaf.extendScalars Y.smallEtaleTopology φ
  let EX := Sheaf.extendScalars X.smallEtaleTopology φ
  let : EY.PreservesKFlatQuasiIso := Sheaf.scalar_preservesKFlatQuasiIso Y.smallEtaleTopology φ
  let : EX.PreservesKFlatQuasiIso := Sheaf.scalar_preservesKFlatQuasiIso X.smallEtaleTopology φ
  have := Sheaf.preservesFlat_extendScalars Y.smallEtaleTopology (f := φ)
  let e : EY ⋙ FB ≅ FA ⋙ EX :=
    (conjugateIsoEquiv
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
        (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ))
      ((Sheaf.extendScalarsAdjunction Y.smallEtaleTopology φ).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
      (lowerStarRestrictScalarsIso φ f).symm
  exact leftDerivedSquare FA EX EY FB e

-- Both composites are left adjoint to restriction of scalars followed by `D(j^*)`.
private lemma scalarOpenLowerShriek
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (L(sheafExtendScalars φ U) ⋙ D((j)_!open[ModuleCat.{u + 1} B]) ≅
      D((j)_!open[ModuleCat.{u + 1} A]) ⋙ L(sheafExtendScalars φ X)) :=
  ⟨(conjugateIsoEquiv
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (leftDerivedEtaleSheafExtendScalarsAdjunction φ X))
      ((leftDerivedEtaleSheafExtendScalarsAdjunction φ U).comp
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j))).symm
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j))⟩

end Etale

namespace ProEtale

attribute [local instance 2000] CommRing.toRing

private lemma scalarPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    have := Sheaf.scalar_preservesKFlatQuasiIso (Scheme.ProEt.topology Y) φ
    have := Sheaf.scalar_preservesKFlatQuasiIso (Scheme.ProEt.topology X) φ
    Nonempty ((Sheaf.extendScalars (Scheme.ProEt.topology Y) φ).leftDerivedFunctor ⋙
        L((f)^*[ModuleCat.{u + 1} B]) ≅
      L((f)^*[ModuleCat.{u + 1} A]) ⋙
        (Sheaf.extendScalars (Scheme.ProEt.topology X) φ).leftDerivedFunctor) := by
  let FA := (f)^*[ModuleCat.{u + 1} A]
  let FB := (f)^*[ModuleCat.{u + 1} B]
  let EY := Sheaf.extendScalars (Scheme.ProEt.topology Y) φ
  let EX := Sheaf.extendScalars (Scheme.ProEt.topology X) φ
  let : EY.PreservesKFlatQuasiIso :=
    Sheaf.scalar_preservesKFlatQuasiIso (Scheme.ProEt.topology Y) φ
  let : EX.PreservesKFlatQuasiIso :=
    Sheaf.scalar_preservesKFlatQuasiIso (Scheme.ProEt.topology X) φ
  have : FA.PreservesFlat :=
    ProEtale.UpperStarPreservesFlat.preservesFlat (A := ModuleCat.{u + 1} A) f
  have := Sheaf.preservesFlat_extendScalars (Scheme.ProEt.topology Y) (f := φ)
  -- the direct images commute with restriction of scalars, both being computed sectionwise
  let e : EY ⋙ FB ≅ FA ⋙ EX :=
    (conjugateIsoEquiv
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
        (Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ))
      ((Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology Y) φ).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm (Iso.refl _)
  exact Etale.leftDerivedSquare FA EX EY FB e

end ProEtale

attribute [local irreducible] ProEtale.pbcFixedScalarExtension Etale.projectionMap
  ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap

end CoefficientProofs

section CoefficientChangeComponents

attribute [local instance 2000] CommRing.toRing

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- The derived pullback commutes with derived base change along a ring morphism
`φ : Λ →+* Λ'`: if `L'` is a derived base change of `L`, then `Lf^* L'` is a derived base change
of `Lf^* L`. -/
theorem exists_isDerivedBaseChange_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : 𝐃(Y, Λ)) (L' : 𝐃(Y, Λ')) (η : L ⟶ (derivedRestrictScalars φ Y).obj L')
    (hη : IsDerivedBaseChange η) :
    ∃ θ : L((f)^*[ModuleCat.{u + 1} Λ]).obj L ⟶
      (derivedRestrictScalars φ X).obj (L((f)^*[ModuleCat.{u + 1} Λ']).obj L'),
      IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := coefficientIso _ φ (Sheaf.scalarDerivedAdjunction Y.smallEtaleTopology φ) hη
  obtain ⟨σ⟩ := scalarPullback φ f
  exact ⟨_, (coefficientUnit _ φ (Sheaf.scalarDerivedAdjunction X.smallEtaleTopology φ) _)
    |>.comp_map_iso (σ.symm.app L ≪≫ (L((f)^*[ModuleCat.{u + 1} Λ'])).mapIso e)⟩

/-- The derived direct image commutes with derived base change along a ring morphism
`φ : Λ →+* Λ'` at `K` as soon as the base change map `(Rf_* K) ⊗ᴸ_Λ Λ' ⟶ Rf_* (K ⊗ᴸ_Λ Λ')` is an
isomorphism: if `K'` is a derived base change of `K`, then `Rf_* K'` is a derived base change of
`Rf_* K`. -/
theorem exists_isDerivedBaseChange_rightDerivedLowerStar_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : 𝐃(X, Λ)) (K' : 𝐃(X, Λ')) (η : K ⟶ (derivedRestrictScalars φ X).obj K')
    (hη : IsDerivedBaseChange η) (h : IsIso ((rightDerivedLowerStarExtendScalarsMap φ f).app K)) :
    ∃ θ : R((f)_*[ModuleCat.{u + 1} Λ]).obj K ⟶
      (derivedRestrictScalars φ Y).obj (R((f)_*[ModuleCat.{u + 1} Λ']).obj K'),
      IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := coefficientIso _ φ (leftDerivedEtaleSheafExtendScalarsAdjunction φ X) hη
  exact ⟨_, (coefficientUnit _ φ (leftDerivedEtaleSheafExtendScalarsAdjunction φ Y) _)
    |>.comp_map_iso (asIso ((rightDerivedLowerStarExtendScalarsMap φ f).app K) ≪≫
      (R((f)_*[ModuleCat.{u + 1} Λ'])).mapIso e)⟩

/-- The compact-support direct image commutes with derived base change along a ring morphism
`φ : Λ →+* Λ'` as soon as the base change maps `(Rg_* M) ⊗ᴸ_Λ Λ' ⟶ Rg_* (M ⊗ᴸ_Λ Λ')` along the
proper part `g` of the chosen compactification of `f` are isomorphisms: if `K'` is a derived base
change of `K`, then `Rf_! K'` is a derived base change of `Rf_! K`. -/
theorem exists_isDerivedBaseChange_rightDerivedLowerShriek_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : 𝐃(X, Λ)) (K' : 𝐃(X, Λ'))
    (η : K ⟶ (derivedRestrictScalars φ X).obj K') (hη : IsDerivedBaseChange η)
    (h : ∀ M, IsIso ((rightDerivedLowerStarExtendScalarsMap φ
      (HasCompactification.compactification f).g).app M)) :
    ∃ θ : (R(f)_![ModuleCat.{u + 1} Λ]).obj K ⟶
      (derivedRestrictScalars φ Y).obj ((R(f)_![ModuleCat.{u + 1} Λ']).obj K'),
      IsDerivedBaseChange θ := by
  let c := HasCompactification.compactification f
  have := c.isOpenImmersion
  obtain ⟨e⟩ := coefficientIso _ φ (leftDerivedEtaleSheafExtendScalarsAdjunction φ X) hη
  obtain ⟨σ⟩ := scalarOpenLowerShriek φ c.i
  have := h ((D((c.i)_!open[ModuleCat.{u + 1} Λ])).obj K)
  exact ⟨_, (coefficientUnit _ φ (leftDerivedEtaleSheafExtendScalarsAdjunction φ Y) _)
    |>.comp_map_iso (asIso ((rightDerivedLowerStarExtendScalarsMap φ c.g).app
        ((D((c.i)_!open[ModuleCat.{u + 1} Λ])).obj K)) ≪≫
      (R((c.g)_*[ModuleCat.{u + 1} Λ'])).mapIso
        (σ.symm.app K ≪≫ (D((c.i)_!open[ModuleCat.{u + 1} Λ'])).mapIso e))⟩

section Tensor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

/-- The derived tensor product commutes with derived base change along a ring morphism
`φ : Λ →+* Λ'`: if `K'` and `L'` are derived base changes of `K` and `L`, then `K' ⊗ᴸ L'` is a
derived base change of `K ⊗ᴸ L`. -/
theorem exists_isDerivedBaseChange_derivedTensor {X : Scheme.{u}} (K L : 𝐃(X, Λ))
    (K' L' : 𝐃(X, Λ'))
    (η : K ⟶ (derivedRestrictScalars φ X).obj K') (η' : L ⟶ (derivedRestrictScalars φ X).obj L')
    (hη : IsDerivedBaseChange η) (hη' : IsDerivedBaseChange η') :
    ∃ θ : ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj L ⟶
      (derivedRestrictScalars φ X).obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ']).obj K').obj L'),
      IsDerivedBaseChange θ := by
  let ad := Sheaf.scalarDerivedAdjunction X.smallEtaleTopology φ
  obtain ⟨eK⟩ := coefficientIso _ φ ad hη
  obtain ⟨eL⟩ := coefficientIso _ φ ad hη'
  have := Sheaf.scalar_preservesKFlatQuasiIso X.smallEtaleTopology φ
  have := Sheaf.preservesFlat_extendScalars X.smallEtaleTopology (f := φ)
  have : (Sheaf.extendScalars X.smallEtaleTopology φ).IsLeftAdjoint :=
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).isLeftAdjoint
  exact ⟨_, (coefficientUnit _ φ ad _).comp_map_iso
    (((Sheaf.extendScalars X.smallEtaleTopology φ).leftDerivedTensorIso K).app L ≪≫
      MonoidalCategory.tensorIso eK eL)⟩

/-- The internal Hom out of a complex which is perfect on the coefficient site commutes with
derived base change along any ring morphism `φ : Λ →+* Λ'`: if `K'` and `L'` are derived base
changes of `K` and `L`, then `RHom(K', L')` is a derived base change of `RHom(K, L)`. Indeed `K` is
dualizable, and the monoidal functor `- ⊗ᴸ_Λ Λ'` preserves internal Homs out of dualizable
objects. -/
theorem exists_isDerivedBaseChange_derivedHom_of_isSitePerfect {X : Scheme.{u}} {K L : 𝐃(X, Λ)}
    (hK : DerivedCategory.IsSitePerfect K) {K' L' : 𝐃(X, Λ')}
    {η : K ⟶ (derivedRestrictScalars φ X).obj K'} {η' : L ⟶ (derivedRestrictScalars φ X).obj L'}
    (hη : IsDerivedBaseChange η) (hη' : IsDerivedBaseChange η') :
    ∃ θ : ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L ⟶
      (derivedRestrictScalars φ X).obj (((derivedHom (ModuleCat.{u + 1} Λ') X).obj (op K')).obj L'),
      IsDerivedBaseChange θ := by
  let := (sheafExtendScalars φ X).leftDerivedFunctorMonoidal
  obtain ⟨eK⟩ := nonempty_iso_leftDerivedSheafExtendScalars_of_isDerivedBaseChange φ X hη
  obtain ⟨eL⟩ := nonempty_iso_leftDerivedSheafExtendScalars_of_isDerivedBaseChange φ X hη'
  obtain ⟨_⟩ := hK.isDualizable
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let := BraidedCategory.exactPairing_swap K Kᘁ
  have := Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing L(sheafExtendScalars φ X)
    Kᘁ K L
  exact ⟨_, (isDerivedBaseChange_leftDerivedEtaleSheafExtendScalarsAdjunction_unit φ X _)
    |>.comp_map_iso
      (asIso ((Functor.LaxMonoidal.ihomComparison L(sheafExtendScalars φ X) K).app L) ≪≫
      ((derivedHom (ModuleCat.{u + 1} Λ') X).mapIso eK.symm.op).app _ ≪≫
      ((derivedHom (ModuleCat.{u + 1} Λ') X).obj (op K')).mapIso eL)⟩

end Tensor

/-- Reduction `Λ → Λ ⧸ (ϖ)ⁿ` commutes with the basic operations of the étale derived
categories. -/
theorem reductionCompatibility {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) :
    ReductionCompatibility.{u} Λ (Ideal.span {ϖ}) n where
  exists_isDerivedBaseChange X := Sheaf.exists_isDerivedBaseChange _ _
  leftDerivedUpperStar f L Ln η hη :=
    exists_isDerivedBaseChange_leftDerivedUpperStar _ f L Ln η hη
  derivedTensor K L Kn Ln η η' hη hη' :=
    exists_isDerivedBaseChange_derivedTensor _ K L Kn Ln η η' hη hη'
  rightDerivedLowerStar f K Kn η hη :=
    exists_isDerivedBaseChange_rightDerivedLowerStar_of_isIso _ f K Kn η hη
      (isIso_rightDerivedLowerStarExtendScalarsMap_app_quotient_span_pow hϖ n f K)
  rightDerivedLowerShriek f _ K Kn η hη :=
    exists_isDerivedBaseChange_rightDerivedLowerShriek_of_isIso _ f K Kn η hη
      (isIso_rightDerivedLowerStarExtendScalarsMap_app_quotient_span_pow hϖ n _)
  projectionMap := sorry
  derivedHom K L Kn Ln η η' hη hη' :=
    exists_isDerivedBaseChange_derivedHom_quotient_span_pow _ hϖ n hη hη'
  rightDerivedUpperShriek := sorry
  upperShriekCounit := sorry
  upperShriekUnit := sorry

/-- Reduction `Λ ⧸ (ϖ)ⁿ → Λ ⧸ (ϖ)ᵐ` between finite quotients commutes with the basic operations
of the étale derived categories on `Dctf`. -/
theorem finiteReductionCompatibility {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) {m n : ℕ}
    (h : m ≤ n) : FiniteReductionCompatibility.{u} Λ (Ideal.span {ϖ}) h where
  leftDerivedUpperStar f L _ L' η hη :=
    exists_isDerivedBaseChange_leftDerivedUpperStar _ f L L' η hη
  derivedTensor K L _ _ K' L' η η' hη hη' :=
    exists_isDerivedBaseChange_derivedTensor _ K L K' L' η η' hη hη'
  rightDerivedLowerShriek := sorry
  projectionMap := sorry
  derivedHom _ _ hK _ _ _ _ hη hη' :=
    exists_isDerivedBaseChange_derivedHom_of_isSitePerfect _ hK hη hη'

/-- The base change map `(Rf_* K) ⊗ᴸ 𝒪_{E'} ⟶ Rf_* (K ⊗ᴸ 𝒪_{E'})` of the common-stage scalar
extension `𝒪_E → 𝒪_{E'}` is an isomorphism, `𝒪_{E'}` being a finite free `𝒪_E`-module. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_integersShrinkMap (l : ℕ) [Fact l.Prime]
    (E E' : Type) [Field E] [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)]
    [Algebra E E'] [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E]
    [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E']
    [IsScalarTower ℚ_[l] E' (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E]
    [Small.{u + 1} E'] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap (PadicAlgCl.integersShrinkMap l E E') f).app
      K) := by
  let := (PadicAlgCl.integersShrinkMap.{0, u} l E E').toAlgebra
  obtain ⟨n, b, -, -⟩ := PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap.{0, u} l E E'
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  exact isIso_rightDerivedLowerStarExtendScalarsMap_app_of_free f K

/-- The common-stage scalar extension `𝒪_E → 𝒪_{E'}` commutes with the basic operations of the
étale derived categories, also after rationalization. -/
theorem scalarExtensionCompatibility (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E]
    [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E'] :
    ScalarExtensionCompatibility.{u} l E E' where
  leftDerivedUpperStar f L _ L' η hη :=
    exists_isDerivedBaseChange_leftDerivedUpperStar _ f L L' η hη
  derivedTensor K L _ _ K' L' η η' hη hη' :=
    exists_isDerivedBaseChange_derivedTensor _ K L K' L' η η' hη hη'
  rightDerivedLowerShriek f _ K _ K' η hη :=
    exists_isDerivedBaseChange_rightDerivedLowerShriek_of_isIso _ f K K' η hη
      (isIso_rightDerivedLowerStarExtendScalarsMap_app_integersShrinkMap l E E' _)
  projectionMap := sorry
  rightDerivedLowerStar f K K' η hη :=
    exists_isDerivedBaseChange_rightDerivedLowerStar_of_isIso _ f K K' η hη
      (isIso_rightDerivedLowerStarExtendScalarsMap_app_integersShrinkMap l E E' f K)
  rationalProjectionMap := sorry

end Etale

namespace ProEtale

set_option hygiene false in
/-- The derived category `D(X_proét, Λ)` of pro-étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- The derived pullback of pro-étale sheaves commutes with derived base change along a ring
morphism `φ : Λ →+* Λ'`: if `L'` is a derived base change of `L`, then `Lf^* L'` is a derived
base change of `Lf^* L`. -/
theorem exists_isDerivedBaseChange_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : 𝐃(Y, Λ)) (L' : 𝐃(Y, Λ'))
    (η : L ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).obj L')
    (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : L((f)^*[ModuleCat.{u + 1} Λ]).obj L ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj
        (L((f)^*[ModuleCat.{u + 1} Λ']).obj L'),
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := coefficientIso _ φ (Sheaf.scalarDerivedAdjunction (Scheme.ProEt.topology Y) φ) hη
  obtain ⟨σ⟩ := scalarPullback φ f
  exact ⟨_, (coefficientUnit _ φ (Sheaf.scalarDerivedAdjunction (Scheme.ProEt.topology X) φ) _)
    |>.comp_map_iso (σ.symm.app L ≪≫ (L((f)^*[ModuleCat.{u + 1} Λ'])).mapIso e)⟩

/-- The derived direct image of pro-étale sheaves commutes with derived base change along
`R → S` at `K` as soon as the base change map `(Rf_* K) ⊗ᴸ_R S ⟶ Rf_* (K ⊗ᴸ_R S)` is an
isomorphism: if `K'` is a derived base change of `K`, then `Rf_* K'` is a derived base change of
`Rf_* K`. -/
theorem exists_isDerivedBaseChange_rightDerivedLowerStar_of_isIso (R S : Type (u + 1))
    [CommRing R] [CommRing S] [Algebra R S] {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝐃(X, R))
    (K' : 𝐃(X, S))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (algebraMap R S)).obj K')
    (hη : Sheaf.IsDerivedBaseChange η)
    (h : IsIso ((rightDerivedLowerStarExtendScalarsMap R S f).app K)) :
    ∃ θ : R((f)_*[ModuleCat.{u + 1} R]).obj K ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) (algebraMap R S)).obj
        (R((f)_*[ModuleCat.{u + 1} S]).obj K'),
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := coefficientIso _ _ (leftDerivedSheafExtendScalarsAdjunction R S X) hη
  exact ⟨_, (coefficientUnit _ _ (leftDerivedSheafExtendScalarsAdjunction R S Y) _)
    |>.comp_map_iso (asIso ((rightDerivedLowerStarExtendScalarsMap R S f).app K) ≪≫
      (R((f)_*[ModuleCat.{u + 1} S])).mapIso e)⟩

/-- The compact-support direct image of pro-étale sheaves along a compactification `c` commutes
with derived base change along `R → S` as soon as the base change maps
`(Rg_* M) ⊗ᴸ_R S ⟶ Rg_* (M ⊗ᴸ_R S)` along the proper part `g` of `c` are isomorphisms: if `K'`
is a derived base change of `K`, then `Rf_!(c) K'` is a derived base change of `Rf_!(c) K`. -/
theorem exists_isDerivedBaseChange_rightDerivedLowerShriekOfCompactification_of_isIso
    (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (K : 𝐃(X, R)) (K' : 𝐃(X, S))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (algebraMap R S)).obj K')
    (hη : Sheaf.IsDerivedBaseChange η)
    (h : ∀ M, IsIso ((rightDerivedLowerStarExtendScalarsMap R S c.g).app M)) :
    ∃ θ : (Rf_!(c)[ModuleCat.{u + 1} R]).obj K ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) (algebraMap R S)).obj
        ((Rf_!(c)[ModuleCat.{u + 1} S]).obj K'),
      Sheaf.IsDerivedBaseChange θ := by
  have := c.isOpenImmersion
  obtain ⟨e⟩ := coefficientIso _ _ (leftDerivedSheafExtendScalarsAdjunction R S X) hη
  have := h ((D((c.i)_!open[ModuleCat.{u + 1} R])).obj K)
  exact ⟨_, (coefficientUnit _ _ (leftDerivedSheafExtendScalarsAdjunction R S Y) _)
    |>.comp_map_iso (asIso ((rightDerivedLowerStarExtendScalarsMap R S c.g).app
        ((D((c.i)_!open[ModuleCat.{u + 1} R])).obj K)) ≪≫
      (R((c.g)_*[ModuleCat.{u + 1} S])).mapIso
        ((openImmersionLowerShriekExtendScalarsIso R S c.i).app K ≪≫
          (D((c.i)_!open[ModuleCat.{u + 1} S])).mapIso e))⟩

section Tensor

attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- The derived tensor product of pro-étale sheaves commutes with derived base change along a
ring morphism `φ : Λ →+* Λ'`: if `K'` and `L'` are derived base changes of `K` and `L`, then
`K' ⊗ᴸ L'` is a derived base change of `K ⊗ᴸ L`. -/
theorem exists_isDerivedBaseChange_derivedTensor {X : Scheme.{u}} (K L : 𝐃(X, Λ))
    (K' L' : 𝐃(X, Λ'))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K')
    (η' : L ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L')
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj L ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ']).obj K').obj L'),
      Sheaf.IsDerivedBaseChange θ := by
  let ad := Sheaf.scalarDerivedAdjunction (Scheme.ProEt.topology X) φ
  obtain ⟨eK⟩ := coefficientIso _ φ ad hη
  obtain ⟨eL⟩ := coefficientIso _ φ ad hη'
  have := Sheaf.scalar_preservesKFlatQuasiIso (Scheme.ProEt.topology X) φ
  have := Sheaf.preservesFlat_extendScalars (Scheme.ProEt.topology X) (f := φ)
  have : (Sheaf.extendScalars (Scheme.ProEt.topology X) φ).IsLeftAdjoint :=
    (Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ).isLeftAdjoint
  exact ⟨_, (coefficientUnit _ φ ad _).comp_map_iso
    (((Sheaf.extendScalars (Scheme.ProEt.topology X) φ).leftDerivedTensorIso K).app L ≪≫
      MonoidalCategory.tensorIso eK eL)⟩

end Tensor

/-- Reduction `Λ → Λ ⧸ (ϖ)ⁿ` commutes with the basic operations of the pro-étale derived
categories. -/
theorem reductionCompatibility {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) :
    ReductionCompatibility.{u} Λ (Ideal.span {ϖ}) n where
  exists_isDerivedBaseChange X := Sheaf.exists_isDerivedBaseChange _ _
  leftDerivedUpperStar f L Ln η hη :=
    exists_isDerivedBaseChange_leftDerivedUpperStar _ f L Ln η hη
  rightDerivedLowerShriekOfCompactification c K Kn η hη :=
    exists_isDerivedBaseChange_rightDerivedLowerShriekOfCompactification_of_isIso _ _ c K Kn η hη
      (isIso_rightDerivedLowerStarExtendScalarsMap_app_quotient_span_pow hϖ n _)
  exchange := sorry
  derivedTensor K L Kn Ln η η' hη hη' :=
    exists_isDerivedBaseChange_derivedTensor _ K L Kn Ln η η' hη hη'
  rightDerivedLowerStar f K Kn η hη :=
    exists_isDerivedBaseChange_rightDerivedLowerStar_of_isIso _ _ f K Kn η hη
      (isIso_rightDerivedLowerStarExtendScalarsMap_app_quotient_span_pow hϖ n f K)
  derivedHom K L Kn Ln η η' hη hη' :=
    exists_isDerivedBaseChange_derivedHom_quotient_span_pow _ hϖ n hη hη'
  rightDerivedUpperShriek := sorry

/-- Reduction `Λ ⧸ (ϖ)ⁿ → Λ ⧸ (ϖ)ᵐ` between finite quotients commutes with the basic operations
of the pro-étale derived categories on `Dctf`. -/
theorem finiteReductionCompatibility {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) {m n : ℕ}
    (h : m ≤ n) : FiniteReductionCompatibility.{u} Λ (Ideal.span {ϖ}) h where
  leftDerivedUpperStar f L _ L' η hη :=
    exists_isDerivedBaseChange_leftDerivedUpperStar _ f L L' η hη
  derivedTensor K L _ _ K' L' η η' hη hη' :=
    exists_isDerivedBaseChange_derivedTensor _ K L K' L' η η' hη hη'
  rightDerivedLowerShriekOfCompactification := sorry
  exchange := sorry

/-- The common-stage scalar extension `𝒪_E → 𝒪_{E'}` commutes with the basic operations of the
pro-étale derived categories. -/
theorem scalarExtensionCompatibility (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E]
    [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E'] :
    ScalarExtensionCompatibility.{u} l E E' where
  leftDerivedUpperStar f L _ L' η hη :=
    exists_isDerivedBaseChange_leftDerivedUpperStar _ f L L' η hη
  derivedTensor K L _ _ K' L' η η' hη hη' :=
    exists_isDerivedBaseChange_derivedTensor _ K L K' L' η η' hη hη'
  rightDerivedLowerShriekOfCompactification c K _ K' η hη := by
    let := (PadicAlgCl.integersShrinkMap.{0, u} l E E').toAlgebra
    exact exists_isDerivedBaseChange_rightDerivedLowerShriekOfCompactification_of_isIso _ _ c K
      K' η hη (isIso_rightDerivedLowerStarExtendScalarsMap_app_integersShrinkMap l E E' _)
  exchange := sorry
  rightDerivedLowerStar f K K' η hη := by
    let := (PadicAlgCl.integersShrinkMap.{0, u} l E E').toAlgebra
    exact exists_isDerivedBaseChange_rightDerivedLowerStar_of_isIso _ _ f K K' η hη
      (isIso_rightDerivedLowerStarExtendScalarsMap_app_integersShrinkMap l E E' f K)

end ProEtale

end CoefficientChangeComponents

/-- Basic operations and coefficient reduction: reduction `𝒪_E → A_{E,n}` commutes with derived
pullback, tensor, ordinary direct image and compact-support direct image; finite reduction
`A_{E,n} → A_{E,m}` commutes with pullback, tensor and compact-support direct image on the
finite-Tor domains; internal Hom commutes with reduction for arbitrary first variables, and
between finite quotients for site-perfect first variables; the same operations commute with
rationalization and common-stage scalar extension. Here `𝒪_E` is generalised to a commutative
ring `Λ` with a nonzerodivisor `ϖ`, and both the étale and the pro-étale model are covered. -/
theorem coefficientChangeCompatibility : CoefficientChangeCompatibility.{u} where
  reduction := Etale.reductionCompatibility
  proEtaleReduction := ProEtale.reductionCompatibility
  finiteReduction := Etale.finiteReductionCompatibility
  scalarExtension := Etale.scalarExtensionCompatibility
  proEtaleFiniteReduction := ProEtale.finiteReductionCompatibility
  proEtaleScalarExtension := ProEtale.scalarExtensionCompatibility

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} {X Y : Scheme.{u}}

/-- Compatibility of the reduction `Λ → Λ ⧸ (ϖ)ⁿ` with the projection transformation.
For a nonzerodivisor `ϖ` of `Λ`, `f : X ⟶ Y` admitting a compactification, `K ∈ D(X_ét, Λ)` and
`L ∈ D(Y_ét, Λ)`, there are reductions `K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ` and `L_n = L ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`
(derived base changes) such that the reduction of the projection map `PF_{f, K, L}` is isomorphic
as an arrow to the restriction of scalars of `PF_{f, K_n, L_n}` over `Λ ⧸ (ϖ)ⁿ`. -/
theorem exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃(X, Λ)) (L : 𝐃(Y, Λ)) :
    ∃ (Kn : 𝐃(X, Λ ⧸ Ideal.span {ϖ} ^ n))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X).obj Kn)
      (Ln : 𝐃(Y, Λ ⧸ Ideal.span {ϖ} ^ n))
      (η' : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).obj Ln),
      IsDerivedBaseChange η ∧ IsDerivedBaseChange η' ∧
        Nonempty (Arrow.mk ((reductionModIdeal Λ Y (Ideal.span {ϖ} ^ n)).map
            (projectionMapApp Λ f K L)) ≅
          Arrow.mk ((derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).map
            (projectionMapApp (Λ ⧸ Ideal.span {ϖ} ^ n) f Kn Ln))) := by
  have h := coefficientChangeCompatibility.reduction hϖ n
  obtain ⟨Kn, η, hη⟩ := h.exists_isDerivedBaseChange X K
  obtain ⟨Ln, η', hη'⟩ := h.exists_isDerivedBaseChange Y L
  exact ⟨Kn, η, Ln, η', hη, hη', h.projectionMap f K L Kn η Ln η' hη hη'⟩

end Etale

namespace ProEtale

set_option hygiene false in
/-- The derived category `D(X_proét, Λ)` of pro-étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ}
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Restriction of scalars `D(X_proét, Λ/Iⁿ) ⥤ D(X_proét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " n "]" =>
  Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk (I ^ n))

/-- Compatibility of the reduction `Λ → Λ/Iⁿ` with the compact-support exchange transformation.
For an ideal `I` of `Λ` generated by a nonzerodivisor, a cartesian square `g' ≫ f = f' ≫ g`, a
compactification `c` of `f` and `K ∈ D(X_proét, Λ)` with a reduction `K_n = K ⊗ᴸ_Λ Λ/Iⁿ`, the
reduction modulo `Iⁿ` of the exchange map `Ex_!(c)` at `K` is isomorphic, as an arrow, to the
restriction of scalars of the exchange map `Ex_!(c)` over `Λ/Iⁿ` at `K_n`. -/
theorem nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (hI : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})
    (n : ℕ) (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty (Arrow.mk
        ((_root_.DerivedCategory.reductionModIdeal (Scheme.ProEt.topology Y') (I ^ n)).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
          c).app K)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y', n].map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) sq c).app Kn))) := by
  obtain ⟨ϖ, hϖ, rfl⟩ := hI
  exact (coefficientChangeCompatibility.proEtaleReduction hϖ n).exchange sq c K Kn η hη

end ProEtale

end AlgebraicGeometry
