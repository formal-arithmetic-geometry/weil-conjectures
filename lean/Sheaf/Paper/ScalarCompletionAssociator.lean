/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization

/-! # Normalized associators for strict completed scalar extension

Source: blueprint main-20261015, `lem-fix-operation-reduction`, paragraph 3;
Stacks Tag 099B (blueprint: lem-fix-scalar-completion-associator).
The structure bundles the assertions of this single statement. Every scalar functor,
quotient cocone and K-flat comparison is the published construction. Its uniqueness
clause expresses independence of representatives and cofinal exponent choices:
any construction with the specified quotient normalization gives the same map.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

/-- The normalized scalar associators, on all derived-complete inputs and arbitrary schemes.
The ordinary associator is fixed by balanced multiplication on flat-term K-flat models;
the completed one is fixed by the actual zero-shifted-component quotient maps `chi`.
The unit is inverse to completeness after ordinary multiplication. The final equations
are the pentagon and the two unit equations, including identity field extensions.
Source: blueprint `lem-fix-operation-reduction`, paragraph 3; Stacks Tag 099B
(blueprint: lem-fix-scalar-completion-associator). -/
structure ScalarCompletionAssociatorData (l : ℕ) [Fact l.Prime]
    (W : AlgebraicGeometry.Scheme.{t}) where
  /-- Finite free scalar extension carries complete inputs to complete inputs. -/
  preserves : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (K : DerivedCategory (integralTowerModules l E W)),
    IsDerivedCompleteUnrestricted l E W K →
      IsDerivedCompleteUnrestricted l L W
        ((integralScalarExtensionOfUniverses l E L ι W).obj K)
  /-- The ordinary balanced derived tensor associator. -/
  ordinary : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M),
    completedDerivedScalarExtension l E L ι W ⋙ completedDerivedScalarExtension l L M κ W ≅
      completedDerivedScalarExtension l E M (κ.comp ι) W
  /-- Its exact computation on every flat-term K-flat representative. -/
  ordinary_model : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory),
    ∃ a : (completedOrdinaryScalarComplex l L M κ W).obj
        ((completedOrdinaryScalarComplex l E L ι W).obj P.obj) ≅
      (completedOrdinaryScalarComplex l E M (κ.comp ι) W).obj P.obj,
      (∀ (i : ℤ) (U : W.ProEtᵒᵖ)
        (b : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
        (c : (completedIntegralCommRingSheafUnrestricted l M W).obj.obj U)
        (x : (P.obj.X i).val.obj U),
        (a.hom.f i).val.app U
            (completedScalarTensorSection l L M κ W _ U c
              (completedScalarTensorSection l E L ι W _ U b x)) =
          completedScalarTensorSection l E M (κ.comp ι) W _ U
            (c * (completedCoefficientMap l L M κ W).hom.app U b) x) ∧
      (completedDerivedScalarExtension l L M κ W).map
          (completedScalarCounit l E L ι W P.obj) ≫
        completedScalarCounit l L M κ W
          ((completedOrdinaryScalarComplex l E L ι W).obj P.obj) ≫
        DerivedCategory.Q.map a.hom =
      (ordinary E L M ι κ).hom.app (DerivedCategory.Q.obj P.obj) ≫
        completedScalarCounit l E M (κ.comp ι) W P.obj
  /-- Ordinary scalar identity, before completion. -/
  ordinaryUnit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
    completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) W ≅
      𝟭 (DerivedCategory (integralTowerModules l E W))
  /-- The identity is precisely the published multiplication on K-flat models. -/
  ordinaryUnit_model : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (P : (integralOperationsGoodComplex l E W).FullSubcategory),
    (ordinaryUnit E).hom.app (DerivedCategory.Q.obj P.obj) =
      completedScalarCounit l E E (AlgHom.id ℚ_[l] E) W P.obj ≫
        DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E W).hom.app P.obj)
  /-- Natural isomorphisms on the full subcategory of complete objects. -/
  associator : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M),
    ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W) ⋙
        integralScalarExtensionOfUniverses l E L ι W ⋙
        integralScalarExtensionOfUniverses l L M κ W ≅
      ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W) ⋙
        integralScalarExtensionOfUniverses l E M (κ.comp ι) W
  /-- The quotient-cocone normalization, with the order of composition in Lean. -/
  normalization : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M)
    (K : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E W)),
    (completedScalarComparison l L M κ W).app
        ((completedDerivedScalarExtension l E L ι W).obj K.obj) ≫
      (integralScalarExtensionOfUniverses l L M κ W).map
        ((completedScalarComparison l E L ι W).app K.obj) ≫
      (associator E L M ι κ).hom.app K =
    (ordinary E L M ι κ).hom.app K.obj ≫
      (completedScalarComparison l E M (κ.comp ι) W).app K.obj
  /-- Uniqueness under this normalization: in particular no representative or cofinal
  exponent choice can change the comparison. -/
  independent : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M)
    (a : ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W) ⋙
        integralScalarExtensionOfUniverses l E L ι W ⋙
        integralScalarExtensionOfUniverses l L M κ W ≅
      ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W) ⋙
        integralScalarExtensionOfUniverses l E M (κ.comp ι) W),
    (∀ K : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E W),
      (completedScalarComparison l L M κ W).app
          ((completedDerivedScalarExtension l E L ι W).obj K.obj) ≫
        (integralScalarExtensionOfUniverses l L M κ W).map
          ((completedScalarComparison l E L ι W).app K.obj) ≫ a.hom.app K =
      (ordinary E L M ι κ).hom.app K.obj ≫
        (completedScalarComparison l E M (κ.comp ι) W).app K.obj) →
      a = associator E L M ι κ
  /-- The inverse completeness unit under ordinary multiplication. -/
  unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
    ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W) ⋙
        integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) W ≅
      ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W)
  /-- Its normalization uses exactly the published quotient completion map. -/
  unit_normalization : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E W)),
    (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) W).app K.obj ≫
      (unit E).hom.app K = (ordinaryUnit E).hom.app K.obj
  /-- The pentagon, as equality in the ambient derived category of the final field. -/
  pentagon : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (N : Type u) [Field N] [Algebra ℚ_[l] N] [FiniteDimensional ℚ_[l] N]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M) (ν : M →ₐ[ℚ_[l]] N)
    (K : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E W)),
    (integralScalarExtensionOfUniverses l M N ν W).map
        ((associator E L M ι κ).hom.app K) ≫
      (associator E M N (κ.comp ι) ν).hom.app K =
    (associator L M N κ ν).hom.app
        ⟨(integralScalarExtensionOfUniverses l E L ι W).obj K.obj,
          preserves E L ι K.obj K.property⟩ ≫
      (associator E L N ι (ν.comp κ)).hom.app K
  /-- The source-field identity extension acts by its completeness identification. -/
  left_unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (K : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E W)),
    (associator E E L (AlgHom.id ℚ_[l] E) ι).hom.app K =
      (integralScalarExtensionOfUniverses l E L ι W).map ((unit E).hom.app K)
  /-- The target-field identity extension acts by its completeness identification. -/
  right_unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (K : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E W)),
    (associator E L L ι (AlgHom.id ℚ_[l] L)).hom.app K =
      (unit L).hom.app
        ⟨(integralScalarExtensionOfUniverses l E L ι W).obj K.obj,
          preserves E L ι K.obj K.property⟩

/-- Strict-tower completed scalar extension has the canonically normalized coherent
associators, without boundedness, constructibility or geometric finiteness hypotheses.
Source: blueprint `lem-fix-operation-reduction`, paragraph 3; Stacks Tag 099B
(blueprint: lem-fix-scalar-completion-associator).

Proof:
1. The finite-free comparison supplies the canonical completed ring maps. Their
   finite projections identify their composites. Absolute-value uniqueness and the
   DVR property give t_E = u*t_L^e and t_L = z*t_M^f. Constant-completion flatness
   and exact sheafification identify the regular quotients with the finite coefficient
   sheaves. Countable pro-etale products are exact, so completion exchange applies.
2. Resolve by a flat-term K-flat complex. Balanced multiplication sends
   c tensor (b tensor x) to c*kappa(b) tensor x and has inverse c tensor x mapped
   to c tensor (1 tensor x). It commutes with quotient transitions and actual units.
   Quotient-scalar descent and well-definedness identify I_{G/F} with D_G C_{G/F}
   and chi with the quotient unit. Successive-derived-quotient normalization gives
   the ordinary balanced associator, its descent and its coherence.
3. Finite-free completion exchange gives epsilon: C_b D_L = D_M C_b, with
   epsilon C_b(eta_L) = eta_M. Tensor/product interchange, quotient reassociation
   and cofinal restriction give this equation on both actual Roos coordinates.
4. For complete K put J = I_{M/E}K and d = D_M(alpha) epsilon. The finite-free
   comparison makes J complete. Define a = inverse(eta_J) D_M(d). All factors
   are natural isomorphisms. This is the comparison from the specified cocones.
5. Naturality gives a eta = d. The exchange unit equation gives
   d C_b(chi) = chi alpha. Combining these is exactly normalization above.
6. All precomposing chi maps are invertible on complete inputs, so normalization
   determines a uniquely. Descent removes representative choices. Cofinal Roos
   restriction uses selection and weighted finite blocks, preserves augmentations
   and the zero shifted coordinate, and is invertible. Tensor commutes with its
   finite sums and products. Thus every cofinal construction has the same
   normalization and uniqueness gives independence.
7. Precompose the pentagon by the invertible threefold chi. Naturality and the
   normalization reduce both routes to the ordinary tensor pentagon. Cancel chi.
   For repeated fields the identity normalization identifies chi with the actual
   completeness unit under multiplication. The same calculation reduces the two
   unit equations to the ordinary multiplication identities.
-/
theorem scalarCompletionAssociator (l : ℕ) [Fact l.Prime]
    (W : AlgebraicGeometry.Scheme.{t}) :
    Nonempty (ScalarCompletionAssociatorData.{t, u} l W) := by
  sorry

end WeilConjectures
