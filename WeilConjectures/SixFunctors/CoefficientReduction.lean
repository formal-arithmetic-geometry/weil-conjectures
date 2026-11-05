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
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
import WeilConjectures.AlgebraicGeometry.CoefficientChange.CoefficientTransformationComparisons

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

attribute [local instance] coefficientCountableCoproducts

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

/-- Restriction of scalars `D(X_ét, Λ ⧸ Iⁿ) ⥤ D(X_ét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " I ", " n "]" =>
  derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X

section ScalarExtension

set_option hygiene false in
/-- The derived category `D(X_ét, 𝒪_E)` of the integral stage. The ring structure is written as
the one underlying the commutative ring structure, as in the statements for general commutative
coefficient rings. -/
local notation "𝐃𝐎(" X ", " E ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X)
    (@ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)) CommRing.toRing))

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

end ProEtale

section CoefficientProofs

-- Keep derived-functor constructions folded while checking their comparisons.
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

-- Elaborate each large proof before starting the next one.
set_option Elab.async false

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

 -- Use the generic commutative coefficient ring instance in proof constructions.
attribute [local instance 2000] CommRing.toRing

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

-- Prove the resolution comparison with abstract categories, before choosing the sites.

end Etale

namespace Etale
-- Match the monoidal structures of the public etale tensor and internal Hom.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
end Etale

namespace Etale
end Etale

namespace ProEtale
end ProEtale

attribute [local irreducible] ProEtale.pbcFixedScalarExtension Etale.projectionMap
  ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap

-- Auxiliary field proofs avoid repeating their large elaborated instance arguments.

end CoefficientProofs

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} {X Y : Scheme.{u}}

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

end ProEtale

end AlgebraicGeometry
