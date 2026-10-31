/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientChange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
import WeilConjectures.AlgebraicGeometry.CoefficientTransformationComparisons

/-!
# The basic operations and reduction of the coefficients

Let `Λ` be a commutative ring and `ϖ` a nonzerodivisor of `Λ`, the intended case being
`Λ = 𝒪_E` with a uniformizer `ϖ`, so that `Λ ⧸ (ϖ)ⁿ = A_{E,n}`. The reduction of a complex `K`
of sheaves of `Λ`-modules is its derived base change `K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`, characterised by
its universal property (`CategoryTheory.Sheaf.IsDerivedBaseChange`) and read in `D(Λ)` through
restriction of scalars. Blueprint `lem-fix-operation-reduction` states that this reduction
commutes with the basic operations, compatibly with the units and counits out of which the
projection and exchange transformations are built.

The compatibilities are recorded as propositions: reduction `Λ → Λ ⧸ (ϖ)ⁿ` for the étale and for
the pro-étale model of the coefficient categories, reduction between finite quotients, and the
common-stage scalar extension `𝒪_E → 𝒪_{E'}` with its rationalization. They are assembled in
`AlgebraicGeometry.CoefficientChangeCompatibility`, and the node itself is
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

- `AlgebraicGeometry.coefficientChangeCompatibility` (`lem-fix-operation-reduction`).
- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap`:
  the reduction of `PF_{f, K, L}` modulo `(ϖ)ⁿ` is isomorphic, as an arrow, to the restriction
  of scalars of `PF_{f, K_n, L_n}`.
- `nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap`
  (in the namespace `AlgebraicGeometry.ProEtale`): the reduction of the pro-étale exchange map
  `Ex_!(c)` at `K` is isomorphic, as an arrow, to the restriction of scalars of `Ex_!(c)` at
  `K_n`.

## Implementation notes

The two clauses are proved in this file, from the node, rather than in the files using them:
restating a statement involving the monoidal structure of the derived categories over a
quotient ring in another module and closing it with the node makes the kernel compare
independently elaborated instances, which does not terminate in practice.
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

private lemma genericScalarTensor
    (K L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    Nonempty ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension J φ).obj (K ⊗ L) ≅
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension J φ).obj K ⊗
        (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension J φ).obj L) := by
  have := scalar_preservesKFlatQuasiIso J φ
  have := preservesFlat_extendScalars J (f := φ)
  let E := extendScalars J φ
  let S := AlgebraicGeometry.ProEtale.pbcFixedScalarExtension J φ
  let e : E.leftDerivedFunctor ≅ S :=
    (scalarDerivedAdjunction J φ).leftAdjointUniq
      (Adjunction.ofIsRightAdjoint (derivedRestrictScalars J φ))
  let T := curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
  exact ⟨(e.app (K ⊗ L)).symm ≪≫ (E.leftDerivedTensorIso K).app L ≪≫
    (T.mapIso (e.app K)).app (E.leftDerivedFunctor.obj L) ≪≫
    (T.obj (S.obj K)).mapIso (e.app L)⟩

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
derived categories (the étale part of blueprint `lem-fix-operation-reduction`): every object
has a reduction (a derived base change along `Λ → Λ ⧸ Iⁿ`); the derived pullback, the derived
tensor product, the derived direct image, the compact-support direct image and the internal Hom
of reductions are reductions of the corresponding operations; and the reduction of the
projection map `PF_{f, K, L}` (its image under `- ⊗ᴸ (Λ ⧸ Iⁿ)_Y`) is isomorphic as an arrow to the
restriction of scalars of the projection map `PF_{f, K_n, L_n}` over `Λ ⧸ Iⁿ`, which expresses
that the comparisons preserve the units, counits and associativity maps out of which the
projection map is built. The exceptional inverse image `Rf^!` (the right adjoint of `Rf_!`)
commutes with reduction, and the reductions of the unit and counit of `Rf_! ⊣ Rf^!` are, as
arrows, the restrictions of scalars of the unit and counit over `Λ ⧸ Iⁿ`; these are stated
whenever `Rf_!` is a left adjoint over `Λ` and over `Λ ⧸ Iⁿ`, which is how `Rf^!` is defined
(`AlgebraicGeometry.Etale.rightDerivedUpperShriek`). -/
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
the derived tensor product and the compact-support direct image of derived base changes are
derived base changes of the corresponding operations, and the projection map `PF_{f, K', L'}` of
the base changes is the base change of `PF_{f, K, L}`: there is a commutative square from
`PF_{f, K, L}` to the restriction of scalars of `PF_{f, K', L'}` whose two sides exhibit derived
base changes. This expresses that the comparisons preserve the units, counits and associativity
maps out of which the projection map is built. -/
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
`E ⊆ E'` of `ℚ_ℓ` inside `ℚ̄_ℓ` (the common-stage scalar extension of
`def-sfb-rationalization-quotient`) with the basic operations: derived pullback, derived tensor
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
derived categories (the pro-étale part of blueprint `lem-fix-operation-reduction`): every
object has a reduction (a derived base change along `Λ → Λ ⧸ Iⁿ`); the derived pullback, the
derived tensor product, the derived direct image, the compact-support direct image, the internal
Hom (with arbitrary first variable) and the exceptional inverse image of reductions are
reductions of the corresponding operations; and
the reduction of the compact-support exchange map `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`
at `K` (its image under `- ⊗ᴸ (Λ ⧸ Iⁿ)_{Y'}`) is isomorphic as an arrow to the restriction of
scalars of the exchange map over `Λ ⧸ Iⁿ` at `K_n`, which expresses that the comparisons
preserve the units and counits out of which the exchange map is built. -/
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
pullback, the derived tensor product and the compact-support direct image of derived base
changes are derived base changes of the corresponding operations, and the compact-support
exchange map `Ex_!(c)` at the base change `K'` is the base change of `Ex_!(c)` at `K`: there is
a commutative square from `Ex_!(c)` at `K` to the restriction of scalars of `Ex_!(c)` at `K'`
whose two sides exhibit derived base changes. -/
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
amplitude (at the finite coefficient stages, the blueprint `Dctf(X, A_{E,n})`). -/
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

/-- The statement of blueprint `lem-fix-operation-reduction`, assembled from its parts:

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

private lemma coefficientFromIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
    (N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
    (e : Nonempty (S.obj K ≅ N)) :
    ∃ θ : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj N,
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := e
  exact ⟨ad.unit.app K ≫ (Sheaf.derivedRestrictScalars J φ).map e.hom,
    (coefficientUnit J φ ad K).comp_map_iso e⟩

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

@[irreducible] private noncomputable def coefficientArrowUnary
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (a : F ⟶ G) {K L : C} (e : K ≅ L) :
    Arrow.mk (a.app K) ≅ Arrow.mk (a.app L) :=
  Arrow.isoMk (F.mapIso e) (G.mapIso e) (a.naturality e.hom)

@[irreducible] private noncomputable def coefficientArrowBinary
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D ⥤ E} (a : F ⟶ G)
    {K K' : C} {L L' : D} (eK : K ≅ K') (eL : L ≅ L') :
    Arrow.mk ((a.app K).app L) ≅ Arrow.mk ((a.app K').app L') :=
  Arrow.isoMk ((F.mapIso eK).app L ≪≫ (F.obj K').mapIso eL)
    ((G.mapIso eK).app L ≪≫ (G.obj K').mapIso eL) (by
      have h₁ := congr_app (a.naturality eK.hom) L
      have h₂ := (a.app K').naturality eL.hom
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Arrow.mk_hom,
        Category.assoc]
      change (F.map eK.hom).app L ≫ (F.obj K').map eL.hom ≫
          (a.app K').app L' =
        (a.app K).app L ≫ (G.map eK.hom).app L ≫ (G.obj K').map eL.hom
      dsimp only [NatTrans.comp_app] at h₁
      rw [h₂, ← Category.assoc, h₁, Category.assoc])





private lemma coefficientUnary
    {C₁ C₂ : Type (u + 1)} [Category.{u} C₁] [Category.{u} C₂]
    [EssentiallySmall.{u + 1} C₁] [EssentiallySmall.{u + 1} C₂]
    (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S₁ : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} B))}
    {S₂ : DerivedCategory (Sheaf J₂ (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J₂ (ModuleCat.{u + 1} B))}
    (ad₁ : S₁ ⊣ Sheaf.derivedRestrictScalars J₁ φ)
    (ad₂ : S₂ ⊣ Sheaf.derivedRestrictScalars J₂ φ)
    (F : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J₂ (ModuleCat.{u + 1} A)))
    (G : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} B)) ⥤
      DerivedCategory (Sheaf J₂ (ModuleCat.{u + 1} B)))
    (K : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} A)))
    (N : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} B)))
    (η : K ⟶ (Sheaf.derivedRestrictScalars J₁ φ).obj N)
    (hη : Sheaf.IsDerivedBaseChange η)
    (e : Nonempty (S₂.obj (F.obj K) ≅ G.obj (S₁.obj K))) :
    ∃ θ : F.obj K ⟶ (Sheaf.derivedRestrictScalars J₂ φ).obj (G.obj N),
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := e
  obtain ⟨eK⟩ := coefficientIso J₁ φ ad₁ (η := η) hη
  exact coefficientFromIso J₂ φ ad₂ _ _ ⟨e ≪≫ G.mapIso eK⟩

private lemma coefficientBinary
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    (F : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
    (G : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
    (K L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
    (K' L' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
    (η : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj K')
    (η' : L ⟶ (Sheaf.derivedRestrictScalars J φ).obj L')
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η')
    (e : Nonempty (S.obj ((F.obj K).obj L) ≅ (G.obj (S.obj K)).obj (S.obj L))) :
    ∃ θ : (F.obj K).obj L ⟶
      (Sheaf.derivedRestrictScalars J φ).obj ((G.obj K').obj L'),
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := e
  obtain ⟨eK⟩ := coefficientIso J φ ad (η := η) hη
  obtain ⟨eL⟩ := coefficientIso J φ ad (η := η') hη'
  exact coefficientFromIso J φ ad _ _
    ⟨e ≪≫ (G.mapIso eK).app (S.obj L) ≪≫ (G.obj K').mapIso eL⟩

private lemma coefficientHom
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    (F : (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))ᵒᵖ ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
    (G : (DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))ᵒᵖ ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
    (K L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
    (K' L' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
    (η : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj K')
    (η' : L ⟶ (Sheaf.derivedRestrictScalars J φ).obj L')
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η')
    (e : Nonempty (S.obj ((F.obj (op K)).obj L) ≅
      (G.obj (op (S.obj K))).obj (S.obj L))) :
    ∃ θ : (F.obj (op K)).obj L ⟶
      (Sheaf.derivedRestrictScalars J φ).obj ((G.obj (op K')).obj L'),
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := e
  obtain ⟨eK⟩ := coefficientIso J φ ad (η := η) hη
  obtain ⟨eL⟩ := coefficientIso J φ ad (η := η') hη'
  exact coefficientFromIso J φ ad _ _
    ⟨e ≪≫ (G.mapIso eK.symm.op).app (S.obj L) ≪≫ (G.obj (op K')).mapIso eL⟩



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

private lemma scalarPullbackCanonical
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (ProEtale.pbcFixedScalarExtension Y.smallEtaleTopology φ ⋙
        L(upperStar (ModuleCat.{u + 1} B) f) ≅
      L(upperStar (ModuleCat.{u + 1} A) f) ⋙
        ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ) := by
  let EY := Sheaf.extendScalars Y.smallEtaleTopology φ
  let EX := Sheaf.extendScalars X.smallEtaleTopology φ
  let FA := L(upperStar (ModuleCat.{u + 1} A) f)
  let FB := L(upperStar (ModuleCat.{u + 1} B) f)
  have := Sheaf.scalar_preservesKFlatQuasiIso Y.smallEtaleTopology φ
  have := Sheaf.scalar_preservesKFlatQuasiIso X.smallEtaleTopology φ
  let eY : EY.leftDerivedFunctor ≅
      ProEtale.pbcFixedScalarExtension Y.smallEtaleTopology φ :=
    (Sheaf.scalarDerivedAdjunction Y.smallEtaleTopology φ).leftAdjointUniq
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ))
  let eX : EX.leftDerivedFunctor ≅
      ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ :=
    (Sheaf.scalarDerivedAdjunction X.smallEtaleTopology φ).leftAdjointUniq
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
  obtain ⟨e⟩ := scalarPullback φ f
  exact ⟨Functor.isoWhiskerRight eY.symm FB ≪≫ e ≪≫ Functor.isoWhiskerLeft FA eX⟩


end Etale

namespace Etale
-- Match the monoidal structures of the public etale tensor and internal Hom.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
private lemma scalarHomSitePerfect
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.IsSitePerfect K) :
    Nonempty ((ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ).obj
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) ≅
      ((derivedHom (ModuleCat.{u + 1} B) X).obj
        (op ((ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ).obj K))).obj
          ((ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ).obj L)) := by
  have := Sheaf.scalar_preservesKFlatQuasiIso X.smallEtaleTopology φ
  have := Sheaf.preservesFlat_extendScalars X.smallEtaleTopology (f := φ)
  let E := Sheaf.extendScalars X.smallEtaleTopology φ
  let F := E.leftDerivedFunctor
  let S := ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ
  let : F.Monoidal := E.leftDerivedFunctorMonoidal
  let e : F ≅ S := (Sheaf.scalarDerivedAdjunction X.smallEtaleTopology φ).leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
  obtain ⟨_⟩ := hK.isDualizable
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap K Kᘁ
  let := ExactPairing.map F Kᘁ K
  let H := derivedHom (ModuleCat.{u + 1} B) X
  let eH : F.obj (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) ≅
      (H.obj (op (F.obj K))).obj (F.obj L) :=
    F.mapIso (MonoidalClosed.ihomObjIsoTensor Kᘁ K L) ≪≫
      (Functor.Monoidal.μIso F Kᘁ L).symm ≪≫
      (MonoidalClosed.ihomObjIsoTensor (F.obj Kᘁ) (F.obj K) (F.obj L)).symm
  exact ⟨(e.app _).symm ≪≫ eH ≪≫
    (H.mapIso (e.app K).symm.op).app (F.obj L) ≪≫
    (H.obj (op (S.obj K))).mapIso (e.app L)⟩


end Etale

namespace Etale
private lemma frobeniusDirectImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Finite ι] (b : Module.Basis ι A B) (ell : B →ₗ[A] A)
    (hell : Function.Bijective fun s : B => ell ∘ₗ LinearMap.mulLeft A s)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (η : K ⟶ (Etale.derivedRestrictScalars (algebraMap A B) X).obj K')
    (hη : Etale.IsDerivedBaseChange η) :
    ∃ θ : (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K ⟶
      (Etale.derivedRestrictScalars (algebraMap A B) Y).obj
        ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.obj K'),
      Etale.IsDerivedBaseChange θ := by
  let : Fintype ι := Fintype.ofFinite ι
  have := (coextendRestrictScalarsAdj b ell hell X).isLeftAdjoint
  have := (coextendRestrictScalarsAdj b ell hell Y).isLeftAdjoint
  let EX := coextendScalars (algebraMap A B) X
  let EY := coextendScalars (algebraMap A B) Y
  let PX := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  let PY := (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor
  obtain ⟨eK⟩ := coefficientIso X.smallEtaleTopology (algebraMap A B)
    (derivedCoextendRestrictScalarsAdj b ell hell X) (η := η) hη
  let e : EY.mapDerivedCategory.obj (PX.obj K) ≅ PY.obj K' :=
    (EY.rightDerivedFunctorIsoMapDerivedCategory.app (PX.obj K)).symm ≪≫
      (rightDerivedLowerStarCompCoextendScalarsIso (algebraMap A B) f).app K ≪≫
      PY.mapIso ((EX.rightDerivedFunctorIsoMapDerivedCategory.app K) ≪≫ eK)
  exact ⟨(derivedCoextendRestrictScalarsAdj b ell hell Y).unit.app _ ≫
    (Etale.derivedRestrictScalars (algebraMap A B) Y).map e.hom,
    (coefficientUnit Y.smallEtaleTopology (algebraMap A B) (derivedCoextendRestrictScalarsAdj
      b ell hell Y) _).comp_map_iso e⟩


@[irreducible] private noncomputable def fixedOpenScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        ProEtale.pbcFixedScalarExtension Y.smallEtaleTopology φ ≅
      ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((conjugateIsoEquiv
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (Adjunction.ofIsRightAdjoint (Etale.derivedRestrictScalars φ Y)))
    ((Adjunction.ofIsRightAdjoint (Etale.derivedRestrictScalars φ X)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j))).symm
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j))).symm

@[irreducible] private noncomputable def fixedFrobeniusDirectIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) (ell : B →ₗ[A] A)
    (hell : Function.Bijective fun s : B => ell ∘ₗ LinearMap.mulLeft A s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor ⋙
        ProEtale.pbcFixedScalarExtension Y.smallEtaleTopology (algebraMap A B) ≅
      ProEtale.pbcFixedScalarExtension X.smallEtaleTopology (algebraMap A B) ⋙
        (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor := by
  have := (coextendRestrictScalarsAdj b ell hell X).isLeftAdjoint
  have := (coextendRestrictScalarsAdj b ell hell Y).isLeftAdjoint
  let EX := coextendScalars (algebraMap A B) X
  let EY := coextendScalars (algebraMap A B) Y
  let PA := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  let PB := (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor
  let eX : ProEtale.pbcFixedScalarExtension X.smallEtaleTopology (algebraMap A B) ≅
      EX.mapDerivedCategory :=
    (Adjunction.ofIsRightAdjoint (Etale.derivedRestrictScalars (algebraMap A B)
      X)).leftAdjointUniq (derivedCoextendRestrictScalarsAdj b ell hell X)
  let eY : ProEtale.pbcFixedScalarExtension Y.smallEtaleTopology (algebraMap A B) ≅
      EY.mapDerivedCategory :=
    (Adjunction.ofIsRightAdjoint (Etale.derivedRestrictScalars (algebraMap A B)
      Y)).leftAdjointUniq (derivedCoextendRestrictScalarsAdj b ell hell Y)
  exact Functor.isoWhiskerLeft PA (eY ≪≫ EY.rightDerivedFunctorIsoMapDerivedCategory.symm) ≪≫
    rightDerivedLowerStarCompCoextendScalarsIso (algebraMap A B) f ≪≫
    Functor.isoWhiskerRight (EX.rightDerivedFunctorIsoMapDerivedCategory ≪≫ eX.symm) PB

private lemma fixedFrobeniusCompactIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Finite ι] (b : Module.Basis ι A B) (ell : B →ₗ[A] A)
    (hell : Function.Bijective fun s : B => ell ∘ₗ LinearMap.mulLeft A s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        ProEtale.pbcFixedScalarExtension Y.smallEtaleTopology (algebraMap A B) ≅
      ProEtale.pbcFixedScalarExtension X.smallEtaleTopology (algebraMap A B) ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} B) f) := by
  let : Fintype ι := Fintype.ofFinite ι
  let c := HasCompactification.compactification f
  let JA := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let JB := (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
  let PA := (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor
  let PB := (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
  let SX := ProEtale.pbcFixedScalarExtension X.smallEtaleTopology (algebraMap A B)
  let SZ := ProEtale.pbcFixedScalarExtension c.Z.smallEtaleTopology (algebraMap A B)
  let SY := ProEtale.pbcFixedScalarExtension Y.smallEtaleTopology (algebraMap A B)
  exact ⟨Functor.associator JA PA SY ≪≫
    Functor.isoWhiskerLeft JA (fixedFrobeniusDirectIso b ell hell c.g) ≪≫
    (Functor.associator JA SZ PB).symm ≪≫
    Functor.isoWhiskerRight (fixedOpenScalarIso (algebraMap A B) c.i) PB ≪≫
    Functor.associator SX JB PB⟩


end Etale

namespace ProEtale
private noncomputable abbrev coefficientCoextend
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology X) (ModuleCat.coextendScalars.{u + 1} φ)

private lemma coefficientCoextendAdditive
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u}) : (coefficientCoextend φ X).Additive where
  map_add {_ _ _ _} := by
    ext : 3
    rfl

@[irreducible] private noncomputable def proFrobeniusDirectIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) (ell : B →ₗ[A] A)
    (hell : Function.Bijective fun s : B => ell ∘ₗ LinearMap.mulLeft A s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology Y) (algebraMap A B) ≅
      pbcFixedScalarExtension (Scheme.ProEt.topology X) (algebraMap A B) ⋙
        (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor := by
  let EX := coefficientCoextend (algebraMap A B) X
  let EY := coefficientCoextend (algebraMap A B) Y
  have : EX.Additive := coefficientCoextendAdditive _ _
  have : EY.Additive := coefficientCoextendAdditive _ _
  let aX : EX ⊣ Sheaf.restrictScalars (Scheme.ProEt.topology X) (algebraMap A B) :=
    Sheaf.sheafComposeRestrictScalarsAdj _ _
      (ModuleCat.coextendRestrictScalarsAdj b ell hell)
  let aY : EY ⊣ Sheaf.restrictScalars (Scheme.ProEt.topology Y) (algebraMap A B) :=
    Sheaf.sheafComposeRestrictScalarsAdj _ _
      (ModuleCat.coextendRestrictScalarsAdj b ell hell)
  have := aX.isLeftAdjoint
  have := aY.isLeftAdjoint
  have := (Sheaf.restrictCoextendScalarsAdj
    (Scheme.ProEt.topology X) (algebraMap A B)).isRightAdjoint
  have := (Sheaf.restrictCoextendScalarsAdj
    (Scheme.ProEt.topology Y) (algebraMap A B)).isRightAdjoint
  have : EX.PreservesKInjectiveComplexes :=
    (Sheaf.restrictCoextendScalarsAdj
      (Scheme.ProEt.topology X) (algebraMap A B)).preservesKInjectiveComplexes
  have : EY.PreservesKInjectiveComplexes :=
    (Sheaf.restrictCoextendScalarsAdj
      (Scheme.ProEt.topology Y) (algebraMap A B)).preservesKInjectiveComplexes
  let PA := lowerStar (ModuleCat.{u + 1} A) f
  let PB := lowerStar (ModuleCat.{u + 1} B) f
  have : PA.PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  let e : PA ⋙ EY ≅ EX ⋙ PB := Iso.refl _
  let d : PA.rightDerivedFunctor ⋙ EY.rightDerivedFunctor ≅
      EX.rightDerivedFunctor ⋙ PB.rightDerivedFunctor :=
    Functor.rightDerivedFunctorCompIso' _ _ e ≪≫
      (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).symm
  let eX : pbcFixedScalarExtension (Scheme.ProEt.topology X) (algebraMap A B) ≅
      EX.mapDerivedCategory :=
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (algebraMap A
        B))).leftAdjointUniq aX.mapDerivedCategoryAdjunction
  let eY : pbcFixedScalarExtension (Scheme.ProEt.topology Y) (algebraMap A B) ≅
      EY.mapDerivedCategory :=
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) (algebraMap A
        B))).leftAdjointUniq aY.mapDerivedCategoryAdjunction
  exact Functor.isoWhiskerLeft PA.rightDerivedFunctor
      (eY ≪≫ EY.rightDerivedFunctorIsoMapDerivedCategory.symm) ≪≫
    d ≪≫ Functor.isoWhiskerRight
      (EX.rightDerivedFunctorIsoMapDerivedCategory ≪≫ eX.symm) PB.rightDerivedFunctor

@[irreducible] private noncomputable def proRestrictionUpperStarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ ⋙
        upperStar (ModuleCat.{u + 1} A) f ≅
      upperStar (ModuleCat.{u + 1} B) f ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology X) φ :=
  ((conjugateIsoEquiv
    ((Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) φ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ))).symm (Iso.refl _)).symm

@[irreducible] private noncomputable def proFixedOpenScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology Y) φ ≅
      pbcFixedScalarExtension (Scheme.ProEt.topology X) φ ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((conjugateIsoEquiv
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)))
    ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j))).symm
    (Functor.mapDerivedCategorySquareIso (proRestrictionUpperStarIso φ j))).symm

private lemma proFrobeniusCompactIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Finite ι] (b : Module.Basis ι A B) (ell : B →ₗ[A] A)
    (hell : Function.Bijective fun s : B => ell ∘ₗ LinearMap.mulLeft A s)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Nonempty (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology Y) (algebraMap A B) ≅
      pbcFixedScalarExtension (Scheme.ProEt.topology X) (algebraMap A B) ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c) := by
  let : Fintype ι := Fintype.ofFinite ι
  let JA := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let JB := (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
  let PA := (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor
  let PB := (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
  let SX := pbcFixedScalarExtension (Scheme.ProEt.topology X) (algebraMap A B)
  let SZ := pbcFixedScalarExtension (Scheme.ProEt.topology c.Z) (algebraMap A B)
  let SY := pbcFixedScalarExtension (Scheme.ProEt.topology Y) (algebraMap A B)
  exact ⟨Functor.associator JA PA SY ≪≫
    Functor.isoWhiskerLeft JA (proFrobeniusDirectIso b ell hell c.g) ≪≫
    (Functor.associator JA SZ PB).symm ≪≫
    Functor.isoWhiskerRight (proFixedOpenScalarIso (algebraMap A B) c.i) PB ≪≫
    Functor.associator SX JB PB⟩


end ProEtale


private lemma coefficientEtalePrincipalCompact
    {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : Etale.DerivedCategoryModule A X) :
    Nonempty ((CoefficientChange.etaleExtension (CoefficientChange.quotient A a n) Y).obj
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K) ≅
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f).obj
        ((CoefficientChange.etaleExtension (CoefficientChange.quotient A a n) X).obj K)) := by
  let φ := CoefficientChange.quotient A a n
  let c := HasCompactification.compactification f
  let JA := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let PB := (Etale.lowerStar
    (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) c.g).rightDerivedFunctor
  obtain ⟨e⟩ := CoefficientChange.operationComparisons.etaleDirect (A := A) (a := a) ha n c.g
    (JA.obj K)
  exact ⟨e ≪≫ PB.mapIso ((Etale.fixedOpenScalarIso φ c.i).app K)⟩

private lemma coefficientProPrincipalCompact
    {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    Nonempty ((CoefficientChange.proExtension (CoefficientChange.quotient A a n) Y).obj
      ((ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≅
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) c).obj
          ((CoefficientChange.proExtension (CoefficientChange.quotient A a n) X).obj K)) := by
  let φ := CoefficientChange.quotient A a n
  let JA := (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let PB := (ProEtale.lowerStar
    (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) c.g).rightDerivedFunctor
  obtain ⟨e⟩ := CoefficientChange.operationComparisons.proDirect (A := A) (a := a) ha n c.g
    (JA.obj K)
  exact ⟨e ≪≫ PB.mapIso ((ProEtale.proFixedOpenScalarIso φ c.i).app K)⟩


@[irreducible] private noncomputable def coefficientEtaleAdjunction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u}) :
    CoefficientChange.etaleExtension φ X ⊣ Etale.derivedRestrictScalars φ X :=
  Adjunction.ofIsRightAdjoint _

@[irreducible] private noncomputable def coefficientProAdjunction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u}) :
    CoefficientChange.proExtension φ X ⊣
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ :=
  Adjunction.ofIsRightAdjoint _

private lemma coefficientProPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} B)))
    (η : L ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).obj L')
    (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : L(ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj L ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj
        (L(ProEtale.upperStar (ModuleCat.{u + 1} B) f).obj L'),
      Sheaf.IsDerivedBaseChange θ := by
  let M : ProEtale.CoefficientTensorModel φ Y L := ⟨L', η, hη⟩
  exact ⟨(M.pullback f).unit, (M.pullback f).universal⟩

private lemma coefficientEtaleUnary
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}}
    (F : Etale.DerivedCategoryModule A X ⥤ Etale.DerivedCategoryModule A Y)
    (G : Etale.DerivedCategoryModule B X ⥤ Etale.DerivedCategoryModule B Y)
    (K : Etale.DerivedCategoryModule A X) (K' : Etale.DerivedCategoryModule B X)
    (η : K ⟶ (Etale.derivedRestrictScalars φ X).obj K') (hη : Etale.IsDerivedBaseChange η)
    (e : Nonempty ((CoefficientChange.etaleExtension φ Y).obj (F.obj K) ≅
      G.obj ((CoefficientChange.etaleExtension φ X).obj K))) :
    ∃ θ : F.obj K ⟶ (Etale.derivedRestrictScalars φ Y).obj (G.obj K'),
      Etale.IsDerivedBaseChange θ :=
  coefficientUnary X.smallEtaleTopology Y.smallEtaleTopology φ
    (coefficientEtaleAdjunction φ X) (coefficientEtaleAdjunction φ Y) F G K K' η hη e

private lemma coefficientProUnary
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}}
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (G : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} B)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K')
    (hη : Sheaf.IsDerivedBaseChange η)
    (e : Nonempty ((CoefficientChange.proExtension φ Y).obj (F.obj K) ≅
      G.obj ((CoefficientChange.proExtension φ X).obj K))) :
    ∃ θ : F.obj K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).obj (G.obj K'),
      Sheaf.IsDerivedBaseChange θ :=
  coefficientUnary (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) φ
    (coefficientProAdjunction φ X) (coefficientProAdjunction φ Y) F G K K' η hη e

private lemma coefficientEtaleProjection
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : Etale.DerivedCategoryModule A X) (L : Etale.DerivedCategoryModule A Y)
    (K' : Etale.DerivedCategoryModule B X)
    (η : K ⟶ (Etale.derivedRestrictScalars φ X).obj K')
    (L' : Etale.DerivedCategoryModule B Y)
    (η' : L ⟶ (Etale.derivedRestrictScalars φ Y).obj L')
    (hη : Etale.IsDerivedBaseChange η) (hη' : Etale.IsDerivedBaseChange η')
    (e : Nonempty (Arrow.mk ((CoefficientChange.etaleExtension φ Y).map
        (Etale.projectionMapApp A f K L)) ≅
      Arrow.mk (Etale.projectionMapApp B f
        ((CoefficientChange.etaleExtension φ X).obj K)
        ((CoefficientChange.etaleExtension φ Y).obj L)))) :
    ∃ (θ₁ : (Arrow.mk (Etale.projectionMapApp A f K L)).left ⟶
        (Etale.derivedRestrictScalars φ Y).obj (Arrow.mk (Etale.projectionMapApp B f K' L')).left)
      (θ₂ : (Arrow.mk (Etale.projectionMapApp A f K L)).right ⟶
        (Etale.derivedRestrictScalars φ Y).obj (Arrow.mk (Etale.projectionMapApp B f K' L')).right),
      Etale.IsDerivedBaseChange θ₁ ∧ Etale.IsDerivedBaseChange θ₂ ∧
        θ₁ ≫ (Etale.derivedRestrictScalars φ Y).map (Etale.projectionMapApp B f K' L') =
          Etale.projectionMapApp A f K L ≫ θ₂ := by
  obtain ⟨e⟩ := e
  obtain ⟨eK⟩ := coefficientIso X.smallEtaleTopology φ (coefficientEtaleAdjunction φ X) (η := η) hη
  obtain ⟨eL⟩ := coefficientIso Y.smallEtaleTopology φ (coefficientEtaleAdjunction φ Y)
    (η := η') hη'
  exact coefficientArrow Y.smallEtaleTopology φ (coefficientEtaleAdjunction φ Y) _ _
    ⟨e ≪≫ coefficientArrowBinary (Etale.projectionMap (ModuleCat.{u + 1} B) f) eK eL⟩

private lemma coefficientProExchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K')
    (hη : Sheaf.IsDerivedBaseChange η)
    (e : Nonempty (Arrow.mk ((CoefficientChange.proExtension φ Y').map
      ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app K)) ≅
      Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} B) sq c).app ((CoefficientChange.proExtension φ X).obj K)))) :
    ∃ (θ₁ : (Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K)).left ⟶
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y') φ).obj
          (Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} B) sq c).app K')).left)
      (θ₂ : (Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K)).right ⟶
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y') φ).obj
          (Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} B) sq c).app K')).right),
      Sheaf.IsDerivedBaseChange θ₁ ∧ Sheaf.IsDerivedBaseChange θ₂ ∧
        θ₁ ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y') φ).map
          ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} B) sq c).app K') =
          (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} A) sq c).app K ≫ θ₂ := by
  obtain ⟨e⟩ := e
  obtain ⟨eK⟩ := coefficientIso (Scheme.ProEt.topology X) φ
    (coefficientProAdjunction φ X) (η := η) hη
  exact coefficientArrow (Scheme.ProEt.topology Y') φ (coefficientProAdjunction φ Y') _ _
    ⟨e ≪≫ coefficientArrowUnary
      (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} B) sq c) eK⟩

private lemma coefficientEtaleTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (K L : Etale.DerivedCategoryModule A X) (K' L' : Etale.DerivedCategoryModule B X)
    (η : K ⟶ (Etale.derivedRestrictScalars φ X).obj K')
    (η' : L ⟶ (Etale.derivedRestrictScalars φ X).obj L')
    (hη : Etale.IsDerivedBaseChange η) (hη' : Etale.IsDerivedBaseChange η') :
    ∃ θ : ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj L ⟶
      (Etale.derivedRestrictScalars φ X).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} B) X).obj K').obj L'),
      Etale.IsDerivedBaseChange θ := by
  exact coefficientBinary X.smallEtaleTopology φ (coefficientEtaleAdjunction φ X)
    (Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (Etale.derivedTensor (ModuleCat.{u + 1} B) X) K L K' L' η η' hη hη'
    (Sheaf.genericScalarTensor X.smallEtaleTopology φ K L)

private lemma coefficientProTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K' L' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K')
    (η' : L ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L')
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj L ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj
        (((ProEtale.derivedTensor (ModuleCat.{u + 1} B) X).obj K').obj L'),
      Sheaf.IsDerivedBaseChange θ := by
  exact coefficientBinary (Scheme.ProEt.topology X) φ (coefficientProAdjunction φ X)
    (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (ProEtale.derivedTensor (ModuleCat.{u + 1} B) X) K L K' L' η η' hη hη'
    (Sheaf.genericScalarTensor (Scheme.ProEt.topology X) φ K L)

private lemma coefficientEtalePullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Etale.DerivedCategoryModule A Y) (L' : Etale.DerivedCategoryModule B Y)
    (η : L ⟶ (Etale.derivedRestrictScalars φ Y).obj L') (hη : Etale.IsDerivedBaseChange η) :
    ∃ θ : L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj L ⟶
      (Etale.derivedRestrictScalars φ X).obj
        (L(Etale.upperStar (ModuleCat.{u + 1} B) f).obj L'),
      Etale.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := Etale.scalarPullbackCanonical φ f
  exact coefficientEtaleUnary φ _ _ L L' η hη ⟨(e.app L).symm⟩

private lemma coefficientEtaleBase
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (P : ∀ X : Scheme.{u}, ObjectProperty (Etale.DerivedCategoryModule A X))
    (hc : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      (K : Etale.DerivedCategoryModule A X), P X K →
      Nonempty ((CoefficientChange.etaleExtension φ Y).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K) ≅
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).obj
          ((CoefficientChange.etaleExtension φ X).obj K)))
    (hp : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      (K : Etale.DerivedCategoryModule A X) (L : Etale.DerivedCategoryModule A Y),
      P X K → P Y L →
      Nonempty (Arrow.mk ((CoefficientChange.etaleExtension φ Y).map
        (Etale.projectionMapApp A f K L)) ≅
        Arrow.mk (Etale.projectionMapApp B f
          ((CoefficientChange.etaleExtension φ X).obj K)
          ((CoefficientChange.etaleExtension φ Y).obj L)))) :
    Etale.BaseChangeCompatibility φ P := by
  constructor
  · intro X Y f L _ L' η hη
    exact coefficientEtalePullback φ f L L' η hη
  · intro X K L _ _ K' L' η η' hη hη'
    exact coefficientEtaleTensor φ X K L K' L' η η' hη hη'
  · intro X Y f _ K hK K' η hη
    exact coefficientEtaleUnary φ _ _ K K' η hη (hc f K hK)
  · intro X Y f _ K L hK hL K' η L' η' hη hη'
    exact coefficientEtaleProjection φ f K L K' η L' η' hη hη' (hp f K L hK hL)

private lemma coefficientProBase
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (P : ∀ X : Scheme.{u}, ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))))
    (hc : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))), P X K →
      Nonempty ((CoefficientChange.proExtension φ Y).obj
        ((ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≅
        (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
          ((CoefficientChange.proExtension φ X).obj K)))
    (he : ∀ {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
      {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))), P X K →
      Nonempty (Arrow.mk ((CoefficientChange.proExtension φ Y').map
        ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K)) ≅
        Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} B) sq c).app ((CoefficientChange.proExtension φ X).obj K)))) :
    ProEtale.BaseChangeCompatibility φ P := by
  constructor
  · intro X Y f L _ L' η hη
    exact coefficientProPullback φ f L L' η hη
  · intro X K L _ _ K' L' η η' hη hη'
    exact coefficientProTensor φ X K L K' L' η η' hη hη'
  · intro X Y f c K hK K' η hη
    exact coefficientProUnary φ _ _ K K' η hη (hc c K hK)
  · intro X' X Y' Y g' f' f g sq c K hK K' η hη
    exact coefficientProExchange φ sq c K K' η hη (he sq c K hK)


@[irreducible] private noncomputable def coefficientEtaleProjectionArrow
    {B : Type (u + 1)} [CommRing B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    {K K' : Etale.DerivedCategoryModule B X}
    {L L' : Etale.DerivedCategoryModule B Y} (eK : K ≅ K') (eL : L ≅ L') :
    Arrow.mk (Etale.projectionMapApp B f K L) ≅
      Arrow.mk (Etale.projectionMapApp B f K' L') :=
  coefficientArrowBinary (Etale.projectionMap (ModuleCat.{u + 1} B) f) eK eL

@[irreducible] private noncomputable def coefficientProExchangeArrow
    {B : Type (u + 1)} [CommRing B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))}
    (eK : K ≅ K') :
    Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} B) sq c).app K) ≅
    Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} B) sq c).app K') :=
  coefficientArrowUnary
    (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} B) sq c) eK

private lemma coefficientEtaleProjectionMappedIso
    {B : Type (u + 1)} [CommRing B] {X Y : Scheme.{u}}
    {D : Type*} [Category D] (R : Etale.DerivedCategoryModule B Y ⥤ D)
    (f : X ⟶ Y) [HasCompactification f]
    {K K' : Etale.DerivedCategoryModule B X}
    {L L' : Etale.DerivedCategoryModule B Y} (eK : K ≅ K') (eL : L ≅ L') :
    Nonempty (Arrow.mk (R.map (Etale.projectionMapApp B f K L)) ≅
      Arrow.mk (R.map (Etale.projectionMapApp B f K' L'))) := by
  exact ⟨R.mapArrow.mapIso (coefficientEtaleProjectionArrow f eK eL)⟩

private lemma coefficientProExchangeMappedIso
    {B : Type (u + 1)} [CommRing B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    {D : Type*} [Category D]
    (R : DerivedCategory (Sheaf (Scheme.ProEt.topology Y') (ModuleCat.{u + 1} B)) ⥤ D)
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))}
    (eK : K ≅ K') :
    Nonempty (Arrow.mk (R.map
      ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} B) sq c).app K)) ≅
    Arrow.mk (R.map
      ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} B) sq c).app K'))) := by
  exact ⟨R.mapArrow.mapIso (coefficientProExchangeArrow sq c eK)⟩

private lemma coefficientEtaleCounitMappedIso
    {B : Type (u + 1)} [CommRing B] {X Y : Scheme.{u}}
    {D : Type*} [Category D] (R : Etale.DerivedCategoryModule B Y ⥤ D)
    (f : X ⟶ Y) [HasCompactification f]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).IsLeftAdjoint]
    {L L' : Etale.DerivedCategoryModule B Y} (eL : L ≅ L') :
    Nonempty (Arrow.mk (R.map ((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)).counit.app L)) ≅
    Arrow.mk (R.map ((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)).counit.app L'))) := by
  exact ⟨R.mapArrow.mapIso (coefficientArrowUnary
    (Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)).counit eL)⟩

private lemma coefficientEtaleUnitMappedIso
    {B : Type (u + 1)} [CommRing B] {X Y : Scheme.{u}}
    {D : Type*} [Category D] (R : Etale.DerivedCategoryModule B X ⥤ D)
    (f : X ⟶ Y) [HasCompactification f]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).IsLeftAdjoint]
    {K K' : Etale.DerivedCategoryModule B X} (eK : K ≅ K') :
    Nonempty (Arrow.mk (R.map ((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)).unit.app K)) ≅
    Arrow.mk (R.map ((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)).unit.app K'))) := by
  exact ⟨R.mapArrow.mapIso (coefficientArrowUnary
    (Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)).unit eK)⟩

-- Compare the generic wrappers once, before substituting large quotient instances.
private lemma coefficientProjection_eq
    {B : Type (u + 1)} [CommRing B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : Etale.DerivedCategoryModule B X) (L : Etale.DerivedCategoryModule B Y) :
    CoefficientChange.projection B f K L = Etale.projectionMapApp B f K L := by
  rfl

-- The chosen scalar adjunctions have been constructed above; keep their functors folded.
attribute [local irreducible] ProEtale.pbcFixedScalarExtension Etale.projectionMap
  ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap

-- Auxiliary field proofs avoid repeating their large elaborated instance arguments.

private lemma coefficientPart_reduction :
    ∀ {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (_hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ),
    Etale.ReductionCompatibility.{u} Λ (Ideal.span {ϖ}) n := by
  let O := CoefficientChange.operationComparisons.{u}
  let T := CoefficientChange.transformationComparisons.{u}
  intro A _ a ha n
  let φ := CoefficientChange.quotient A a n
  refine {
    exists_isDerivedBaseChange := ?_
    leftDerivedUpperStar := ?_
    derivedTensor := ?_
    rightDerivedLowerStar := ?_
    rightDerivedLowerShriek := ?_
    projectionMap := ?_
    derivedHom := ?_
    rightDerivedUpperShriek := ?_
    upperShriekCounit := ?_
    upperShriekUnit := ?_ }
  · as_aux_lemma =>
      intro X K
      exact ⟨(CoefficientChange.etaleExtension φ X).obj K,
        (coefficientEtaleAdjunction φ X).unit.app K,
        coefficientUnit X.smallEtaleTopology φ (coefficientEtaleAdjunction φ X) K⟩
  · as_aux_lemma =>
      intro X Y f L Ln η hη
      exact coefficientEtalePullback φ f L Ln η hη
  · as_aux_lemma =>
      intro X K L Kn Ln η η' hη hη'
      exact coefficientEtaleTensor φ X K L Kn Ln η η' hη hη'
  · as_aux_lemma =>
      intro X Y f K Kn η hη
      exact coefficientEtaleUnary φ _ _ K Kn η hη (O.etaleDirect (A := A) (a := a) ha n f K)
  · as_aux_lemma =>
      intro X Y f _ K Kn η hη
      exact coefficientEtaleUnary φ _ _ K Kn η hη (coefficientEtalePrincipalCompact ha n f K)
  · as_aux_lemma =>
      intro X Y f _ K L Kn η Ln η' hη hη'
      have he := T.principalProjection (A := A) (a := a) ha n f K L
      simp only [coefficientProjection_eq] at he
      obtain ⟨e⟩ := he
      obtain ⟨eK⟩ := coefficientIso X.smallEtaleTopology φ (coefficientEtaleAdjunction φ X)
        (η := η) hη
      obtain ⟨eL⟩ := coefficientIso Y.smallEtaleTopology φ (coefficientEtaleAdjunction φ Y)
        (η := η') hη'
      obtain ⟨e'⟩ := coefficientEtaleProjectionMappedIso
        (Etale.derivedRestrictScalars φ Y) f eK eL
      exact ⟨e ≪≫ e'⟩
  · as_aux_lemma =>
      intro X K L Kn Ln η η' hη hη'
      exact coefficientHom X.smallEtaleTopology φ (coefficientEtaleAdjunction φ X)
        (Etale.derivedHom (ModuleCat.{u + 1} A) X)
        (Etale.derivedHom (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X)
        K L Kn Ln η η' hη hη' (O.etaleHom (A := A) (a := a) ha n X K L)
  · as_aux_lemma =>
      intro X Y f _ _ _ L Ln η hη
      exact coefficientEtaleUnary φ _ _ L Ln η hη (O.etaleExceptional (A := A) (a := a) ha n f L)
  · as_aux_lemma =>
      intro X Y f _ _ _ L Ln η hη
      obtain ⟨e⟩ := T.principalCounit (A := A) (a := a) ha n f L
      obtain ⟨eL⟩ := coefficientIso Y.smallEtaleTopology φ (coefficientEtaleAdjunction φ Y)
        (η := η) hη
      obtain ⟨e'⟩ := coefficientEtaleCounitMappedIso
        (Etale.derivedRestrictScalars φ Y) f eL
      exact ⟨e ≪≫ e'⟩
  · as_aux_lemma =>
      intro X Y f _ _ _ K Kn η hη
      obtain ⟨e⟩ := T.principalUnit (A := A) (a := a) ha n f K
      obtain ⟨eK⟩ := coefficientIso X.smallEtaleTopology φ (coefficientEtaleAdjunction φ X)
        (η := η) hη
      obtain ⟨e'⟩ := coefficientEtaleUnitMappedIso
        (Etale.derivedRestrictScalars φ X) f eK
      exact ⟨e ≪≫ e'⟩

private lemma coefficientPart_proEtaleReduction :
    ∀ {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (_hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ),
    ProEtale.ReductionCompatibility.{u} Λ (Ideal.span {ϖ}) n := by
  let O := CoefficientChange.operationComparisons.{u}
  let T := CoefficientChange.transformationComparisons.{u}
  intro A _ a ha n
  let φ := CoefficientChange.quotient A a n
  refine {
    exists_isDerivedBaseChange := ?_
    leftDerivedUpperStar := ?_
    rightDerivedLowerShriekOfCompactification := ?_
    exchange := ?_
    derivedTensor := ?_
    rightDerivedLowerStar := ?_
    derivedHom := ?_
    rightDerivedUpperShriek := ?_ }
  · as_aux_lemma =>
      intro X K
      exact ⟨(CoefficientChange.proExtension φ X).obj K,
        (coefficientProAdjunction φ X).unit.app K,
        coefficientUnit (Scheme.ProEt.topology X) φ (coefficientProAdjunction φ X) K⟩
  · as_aux_lemma =>
      intro X Y f L Ln η hη
      exact coefficientProPullback φ f L Ln η hη
  · as_aux_lemma =>
      intro X Y f c K Kn η hη
      exact coefficientProUnary φ _ _ K Kn η hη (coefficientProPrincipalCompact ha n c K)
  · as_aux_lemma =>
      intro X' X Y' Y g' f' f g sq c K Kn η hη
      obtain ⟨e⟩ := T.principalExchange (A := A) (a := a) ha n sq c K
      obtain ⟨eK⟩ := coefficientIso (Scheme.ProEt.topology X) φ
        (coefficientProAdjunction φ X) (η := η) hη
      obtain ⟨e'⟩ := coefficientProExchangeMappedIso sq c
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y') φ) eK
      exact ⟨e ≪≫ e'⟩
  · as_aux_lemma =>
      intro X K L Kn Ln η η' hη hη'
      exact coefficientProTensor φ X K L Kn Ln η η' hη hη'
  · as_aux_lemma =>
      intro X Y f K Kn η hη
      exact coefficientProUnary φ _ _ K Kn η hη (O.proDirect (A := A) (a := a) ha n f K)
  · as_aux_lemma =>
      intro X K L Kn Ln η η' hη hη'
      exact coefficientHom (Scheme.ProEt.topology X) φ (coefficientProAdjunction φ X)
        (ProEtale.derivedHom (ModuleCat.{u + 1} A) X)
        (ProEtale.derivedHom (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X)
        K L Kn Ln η η' hη hη' (O.proHom (A := A) (a := a) ha n X K L)
  · as_aux_lemma =>
      intro X Y f _ _ _ L Ln η hη
      exact coefficientProUnary φ _ _ L Ln η hη (O.proExceptional (A := A) (a := a) ha n f L)

private lemma coefficientPart_finiteReduction :
    ∀ {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (_hϖ : ϖ ∈ nonZeroDivisors Λ)
    {m n : ℕ} (h : m ≤ n),
    Etale.FiniteReductionCompatibility.{u} Λ (Ideal.span {ϖ}) h := by
  let O := CoefficientChange.operationComparisons.{u}
  let T := CoefficientChange.transformationComparisons.{u}
  intro A _ a ha m n h
  refine { toBaseChangeCompatibility := ?_, derivedHom := ?_ }
  · as_aux_lemma =>
      refine coefficientEtaleBase (Ideal.Quotient.factor (S := Ideal.span {a} ^ n)
        (T := Ideal.span {a} ^ m) (Ideal.pow_le_pow_right h))
        (fun X ↦ Etale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X) ?_ ?_
      · intro X Y f hc K hK
        exact O.etaleFiniteCompact (A := A) (a := a) (m := m) (n := n) ha h f K hK
      · intro X Y f hc K L hK hL
        simpa only [coefficientProjection_eq] using
          T.finiteProjection (A := A) (a := a) (m := m) (n := n) ha h f K L hK hL
  · as_aux_lemma =>
      intro X K L hK K' L' η η' hη hη'
      exact coefficientHom X.smallEtaleTopology (Ideal.Quotient.factor (S := Ideal.span {a} ^ n)
        (T := Ideal.span {a} ^ m)
          (Ideal.pow_le_pow_right h))
        (coefficientEtaleAdjunction (Ideal.Quotient.factor (S := Ideal.span {a} ^ n) (T :=
          Ideal.span {a} ^ m)
          (Ideal.pow_le_pow_right h)) X)
        (Etale.derivedHom (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X)
        (Etale.derivedHom (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ m)) X)
        K L K' L' η η' hη hη' (Etale.scalarHomSitePerfect
          (Ideal.Quotient.factor (S := Ideal.span {a} ^ n) (T := Ideal.span {a} ^ m)
          (Ideal.pow_le_pow_right h)) X K L hK)

private lemma coefficientPart_scalarExtension :
    ∀ (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E] [Field E']
    [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E'],
    Etale.ScalarExtensionCompatibility.{u} l E E' := by
  let T := CoefficientChange.transformationComparisons.{u}
  intro l _ E E' _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine {
    toBaseChangeCompatibility := ?_
    rightDerivedLowerStar := ?_
    rationalProjectionMap := ?_ }
  · as_aux_lemma =>
      refine coefficientEtaleBase (PadicAlgCl.integersShrinkMap l E E')
        (fun _ _ ↦ True) ?_ ?_
      · intro X Y f _ K _
        let := (PadicAlgCl.integersShrinkMap l E E').toAlgebra
        obtain ⟨d, b, ell, hell⟩ :=
          PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap l E E'
        obtain ⟨e⟩ := Etale.fixedFrobeniusCompactIso b ell hell f
        exact ⟨e.app K⟩
      · intro X Y f _ K L _ _
        simpa only [coefficientProjection_eq] using T.scalarProjection l E E' f K L
  · as_aux_lemma =>
      intro X Y f K K' η hη
      let := (PadicAlgCl.integersShrinkMap l E E').toAlgebra
      obtain ⟨d, b, ell, hell⟩ := PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap l E E'
      exact Etale.frobeniusDirectImage b ell hell f K K' η hη
  · as_aux_lemma =>
      intro X Y f _ K L K' η L' η' hη hη'
      let φ := PadicAlgCl.integersShrinkMap l E E'
      have he := T.rationalProjection l E E' f K L
      simp only [coefficientProjection_eq] at he
      obtain ⟨e⟩ := he
      obtain ⟨eK⟩ := coefficientIso X.smallEtaleTopology φ (coefficientEtaleAdjunction φ X)
        (η := η) hη
      obtain ⟨eL⟩ := coefficientIso Y.smallEtaleTopology φ (coefficientEtaleAdjunction φ Y)
        (η := η') hη'
      let Q := DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E' ⋙
        DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E'
      obtain ⟨e'⟩ := coefficientEtaleProjectionMappedIso Q f eK eL
      exact ⟨e ≪≫ e'⟩

private lemma coefficientPart_proEtaleFiniteReduction :
    ∀ {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ}
    (_hϖ : ϖ ∈ nonZeroDivisors Λ) {m n : ℕ} (h : m ≤ n),
    ProEtale.FiniteReductionCompatibility.{u} Λ (Ideal.span {ϖ}) h := by
  let O := CoefficientChange.operationComparisons.{u}
  let T := CoefficientChange.transformationComparisons.{u}
  intro A _ a ha m n h
  refine coefficientProBase (Ideal.Quotient.factor (S := Ideal.span {a} ^ n)
    (T := Ideal.span {a} ^ m) (Ideal.pow_le_pow_right h))
    (fun X ↦ ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X) ?_ ?_
  · as_aux_lemma =>
      intro X Y f c K hK
      exact O.proFiniteCompact (A := A) (a := a) (m := m) (n := n) ha h c K hK
  · as_aux_lemma =>
      intro X' X Y' Y g' f' f g sq c K hK
      exact T.finiteExchange (A := A) (a := a) (m := m) (n := n) ha h sq c K hK

private lemma coefficientPart_proEtaleScalarExtension :
    ∀ (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E] [Field E']
    [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E'],
    ProEtale.ScalarExtensionCompatibility.{u} l E E' := by
  let T := CoefficientChange.transformationComparisons.{u}
  intro l _ E E' _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine { toBaseChangeCompatibility := ?_, rightDerivedLowerStar := ?_ }
  · as_aux_lemma =>
      refine coefficientProBase (PadicAlgCl.integersShrinkMap l E E')
        (fun _ _ ↦ True) ?_ ?_
      · intro X Y f c K _
        let := (PadicAlgCl.integersShrinkMap l E E').toAlgebra
        obtain ⟨d, b, ell, hell⟩ :=
          PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap l E E'
        obtain ⟨e⟩ := ProEtale.proFrobeniusCompactIso b ell hell c
        exact ⟨e.app K⟩
      · intro X' X Y' Y g' f' f g sq c K _
        exact T.scalarExchange l E E' sq c K
  · as_aux_lemma =>
      intro X Y f K K' η hη
      let := (PadicAlgCl.integersShrinkMap l E E').toAlgebra
      obtain ⟨d, b, ell, hell⟩ :=
        PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap l E E'
      exact coefficientProUnary _ _ _ K K' η hη
        ⟨(ProEtale.proFrobeniusDirectIso b ell hell f).app K⟩

end CoefficientProofs

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction.

For the derived-complete coefficient categories, reduction `𝒪_E → A_{E,n}` commutes with derived
pullback, tensor, ordinary direct image and compact-support direct image; finite reduction
`A_{E,n} → A_{E,m}` commutes with pullback, tensor and compact-support direct image on the
finite-Tor domains; internal Hom commutes with reduction `𝒪_E → A_{E,n}` for arbitrary first
variables, and between finite quotients for site-perfect first variables; the same operations
and comparisons commute with rationalization and common-stage scalar extension; and all the
comparisons preserve the associativity maps, units and counits used to construct the projection
and exchange transformations (`AlgebraicGeometry.CoefficientChangeCompatibility`).

Here `𝒪_E` is generalised to a commutative ring `Λ` with a nonzerodivisor `ϖ` (reduction modulo
`(ϖ)ⁿ` is then the cone of `ϖⁿ`, so it commutes with every `Λ`-linear triangulated operation on
the unbounded derived categories; the derived-complete categories are full subcategories of
these, and the comparisons are stated there), and both the étale and the pro-étale model of
the coefficient categories are covered. For the exceptional inverse image, the node only
invokes the coefficient comparisons that the admissibility hypothesis
`def-weil-exceptional-adjoint-admissibility` requires; for `𝒪_E → A_{E,n}` these hold
unconditionally on the unbounded categories and are stated (`Rf^!` and the unit and counit of
`Rf_! ⊣ Rf^!`), while for the finite reductions and scalar extensions they remain part of that
hypothesis. Rationalization is stated in the étale model, where the rational categories of
`def-sfb-rationalization-quotient` are formalised. -/
theorem coefficientChangeCompatibility : CoefficientChangeCompatibility.{u} :=
  sorry

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} {X Y : Scheme.{u}}

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
compatibility of the reduction `Λ → Λ ⧸ (ϖ)ⁿ` (for `Λ = 𝒪_E`, the reduction `𝒪_E → A_{E,n}`) with
the projection transformation.

For a nonzerodivisor `ϖ` of `Λ`, `f : X ⟶ Y` admitting a compactification, `K ∈ D(X_ét, Λ)` and
`L ∈ D(Y_ét, Λ)`, there are reductions `K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ` and `L_n = L ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`
(derived base changes, `AlgebraicGeometry.Etale.IsDerivedBaseChange`) such that the reduction
`ρ(PF_{f, K, L})` of the projection map, its image under `- ⊗ᴸ (Λ ⧸ (ϖ)ⁿ)_Y`, is isomorphic as an
arrow to the restriction of scalars of the projection map `PF_{f, K_n, L_n}` over `Λ ⧸ (ϖ)ⁿ`.
It is the reduction square that Step 1 of `sk-thm-sf-pf-adic` cites from
`sk-prop-sf-pf-reduction`, a consequence of
`AlgebraicGeometry.coefficientChangeCompatibility`. -/
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

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
compatibility of the reduction `Λ → Λ/Iⁿ` (for `Λ = 𝒪_E` and `I = 𝔪_E`, the reduction
`𝒪_E → A_{E,n}`) with the compact-support exchange transformation.

For an ideal `I` of `Λ` generated by a nonzerodivisor, a cartesian square `g' ≫ f = f' ≫ g`, a
compactification `c` of `f` and `K ∈ D(X_proét, Λ)` with a reduction `K_n = K ⊗ᴸ_Λ Λ/Iⁿ` (a
derived base change `η : K ⟶ Res K_n`, `CategoryTheory.Sheaf.IsDerivedBaseChange`), the
reduction modulo `Iⁿ` of the compact-support exchange map `Ex_!(c) : Lg^* Rf_!(c) K ⟶
Rf'_!(c') Lg'^* K` over `Λ` is isomorphic, as an arrow, to the restriction of scalars of the
exchange map `Ex_!(c)` over `Λ/Iⁿ` at `K_n`. It is a consequence of
`AlgebraicGeometry.coefficientChangeCompatibility`. -/
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
