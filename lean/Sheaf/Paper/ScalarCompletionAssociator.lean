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
import Sheaf.Paper.CompletedLineTensorCoherence

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
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedScalarChainComparison
  completedScalarComparison completedScalarIdentityMultiplication completedScalarIdentityUnit

private noncomputable def comparisonAlong
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : A ⥤ B) {G H : B ⥤ D} (χ : G ⟶ H)
    (h : ∀ X : A, IsIso (χ.app (F.obj X))) : F ⋙ G ≅ F ⋙ H :=
  NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (χ.app (F.obj X)) (h X))
    (fun f ↦ χ.naturality (F.map f))

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
  classical
  let ordinary := fun (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (M : Type u) [Field M] [Algebra ℚ_[l] M]
      [FiniteDimensional ℚ_[l] M] (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M) ↦
    (CompletedLineTensor.associatorData l E W L ι M κ).derived
  let assoc := fun (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (M : Type u) [Field M] [Algebra ℚ_[l] M]
      [FiniteDimensional ℚ_[l] M] (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M) ↦
    let incl := ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W)
    let one := comparisonAlong incl (completedScalarComparison l E L ι W)
      (fun K ↦ ((finiteFreeCompletedScalarComparison l E L ι W).2.1 K.obj K.property).1)
    let two := comparisonAlong (incl ⋙ integralScalarExtensionOfUniverses l E L ι W)
      (completedScalarComparison l L M κ W)
      (fun K ↦ ((finiteFreeCompletedScalarComparison l L M κ W).2.1 _
        (CompletedLineTensor.extension_complete l E W L ι K.obj K.property)).1)
    let three := comparisonAlong incl (completedScalarComparison l E M (κ.comp ι) W)
      (fun K ↦ ((finiteFreeCompletedScalarComparison l E M (κ.comp ι) W).2.1
        K.obj K.property).1)
    NatIso.ofComponents
      (F := incl ⋙ integralScalarExtensionOfUniverses l E L ι W ⋙
        integralScalarExtensionOfUniverses l L M κ W)
      (G := incl ⋙ integralScalarExtensionOfUniverses l E M (κ.comp ι) W)
      (fun K ↦ CompletedLineTensor.associator l E W L ι M κ K.obj K.property)
      (fun f ↦ (two.symm ≪≫
        isoWhiskerRight one.symm (completedDerivedScalarExtension l L M κ W) ≪≫
        isoWhiskerLeft incl (ordinary E L M ι κ) ≪≫ three).hom.naturality f)
  let unit := fun (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] ↦
    NatIso.ofComponents
      (F := ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W) ⋙
        integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) W)
      (G := ObjectProperty.ι (IsDerivedCompleteUnrestricted l E W))
      (fun K : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E W) ↦
        CompletedLineTensor.unit l E W K.obj K.property)
      (by
        intro K H f
        exact (CompletedLineTensor.unit_normalization l E W).2
          K.obj H.obj K.property H.property f.hom)
  have norm (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
      (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
      (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M)
      (K : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E W)) :
      (completedScalarComparison l L M κ W).app
          ((completedDerivedScalarExtension l E L ι W).obj K.obj) ≫
        (integralScalarExtensionOfUniverses l L M κ W).map
          ((completedScalarComparison l E L ι W).app K.obj) ≫
        (assoc E L M ι κ).hom.app K =
      (ordinary E L M ι κ).hom.app K.obj ≫
        (completedScalarComparison l E M (κ.comp ι) W).app K.obj := by
    change (completedScalarComparison l L M κ W).app _ ≫
      (integralScalarExtensionOfUniverses l L M κ W).map
        ((completedScalarComparison l E L ι W).app K.obj) ≫
      (CompletedLineTensor.associator l E W L ι M κ K.obj K.property).hom = _
    rw [← Category.assoc, ← (completedScalarComparison l L M κ W).naturality]
    dsimp only [CompletedLineTensor.associator]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    simp only [CompletedLineTensor.chi, asIso_hom, asIso_inv]
    have := ((finiteFreeCompletedScalarComparison l E L ι W).2.1 K.obj K.property).1
    have := ((finiteFreeCompletedScalarComparison l L M κ W).2.1 _
      (CompletedLineTensor.extension_complete l E W L ι K.obj K.property)).1
    simp only [IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
      IsIso.hom_inv_id]
    exact (congrArg
      (fun f ↦ f ≫ (ordinary E L M ι κ).hom.app K.obj ≫
        (completedScalarComparison l E M (κ.comp ι) W).app K.obj)
      ((completedDerivedScalarExtension l L M κ W).map_id
        ((completedDerivedScalarExtension l E L ι W).obj K.obj))).trans
      (Category.id_comp _)
  refine ⟨{
    preserves := fun E _ _ _ L _ _ _ ι K hK ↦
      CompletedLineTensor.extension_complete l E W L ι K hK
    ordinary := ordinary
    ordinary_model := ?_
    ordinaryUnit := fun E _ _ _ ↦ CompletedLineTensor.ordinaryUnit l E W
    ordinaryUnit_model := ?_
    associator := assoc
    normalization := norm
    independent := ?_
    unit := unit
    unit_normalization := ?_
    pentagon := ?_
    left_unit := ?_
    right_unit := ?_
  }⟩
  · intro E _ _ _ L _ _ _ M _ _ _ ι κ P
    have h := (CompletedLineTensor.associatorData_existsUnique l E W L ι M κ)
      |>.exists.choose_spec
    refine ⟨(CompletedLineTensor.scalarAssociatorComplex l E W L ι M κ
      (CompletedLineTensor.associatorData l E W L ι M κ).sheaf).app P.obj, ?_, ?_⟩
    · intro i U b c x
      exact h.1 (P.obj.X i) U b c x
    · exact h.2 P
  · intro E _ _ _ P
    exact (CompletedLineTensor.ordinaryUnit_existsUnique l E W).exists.choose_spec P
  · intro E _ _ _ L _ _ _ M _ _ _ ι κ a ha
    apply Iso.ext
    apply NatTrans.ext
    funext K
    have h1 := (finiteFreeCompletedScalarComparison l E L ι W).2.1 K.obj K.property
    have := h1.1
    have := ((finiteFreeCompletedScalarComparison l L M κ W).2.1 _ h1.2).1
    apply (cancel_epi ((integralScalarExtensionOfUniverses l L M κ W).map
      ((completedScalarComparison l E L ι W).app K.obj))).1
    apply (cancel_epi ((completedScalarComparison l L M κ W).app
      ((completedDerivedScalarExtension l E L ι W).obj K.obj))).1
    exact (ha K).trans (norm E L M ι κ K).symm
  · intro E _ _ _ K
    have := ((finiteFreeCompletedScalarComparison l E E (AlgHom.id ℚ_[l] E) W).2.1
      K.obj K.property).1
    change (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) W).app K.obj ≫
      (CompletedLineTensor.unit l E W K.obj K.property).hom = _
    dsimp only [CompletedLineTensor.unit]
    simp only [Iso.trans_hom, Iso.symm_hom]
    change (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) W).app K.obj ≫
      CategoryTheory.inv
        ((completedScalarComparison l E E (AlgHom.id ℚ_[l] E) W).app K.obj) ≫ _ = _
    simp only [IsIso.hom_inv_id_assoc]
    rfl
  · intro E _ _ _ L _ _ _ M _ _ _ N _ _ _ ι κ ν K
    exact (CompletedLineTensor.scalar_coherence l E W L ι M κ).2.2 N ν K.obj K.property
  · intro E _ _ _ L _ _ _ ι K
    exact (CompletedLineTensor.scalar_coherence l E W L ι L (AlgHom.id ℚ_[l] L)).1
      K.obj K.property
  · intro E _ _ _ L _ _ _ ι K
    exact (CompletedLineTensor.scalar_coherence l E W L ι L (AlgHom.id ℚ_[l] L)).2.1
      K.obj K.property

end WeilConjectures
