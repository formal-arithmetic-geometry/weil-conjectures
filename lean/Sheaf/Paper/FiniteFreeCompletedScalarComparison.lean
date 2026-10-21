/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.DerivedComplete
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.Paper.WeilCompletedTensorReflector
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Finite free completed scalar comparison

Source: Bhatt--Scholze, Lemma 6.8.2(1), Definition 3.4.10 and Lemma 3.4.12
(blueprint: lem-weil-finite-free-completed-scalar-comparison).

## Main definitions

- `completedCoefficientMap`: the completed coefficient inclusion fixed by its residues.
- `completedOrdinaryScalarExtension` and `completedDerivedScalarExtension`: ordinary
  and derived change of rings along that inclusion, retaining the universal counit.
- `completedScalarChainComparison` and `completedScalarComparison`: the specified
  strict-cone map and its normalized descent to the derived category.
- `completedScalarIdentityMultiplication` and `completedScalarIdentityUnit`: the
  multiplication isomorphism and independently specified completeness unit.

## Main statements

- `finiteFreeCompletedScalarComparison`: finite freeness, invertibility of the
  comparison on complete inputs, completeness of ordinary extension, and identity normalization.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

/-- The unique completed coefficient map with the prescribed finite reductions.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: the quotient inclusion maps commute with transitions. Their composites with
source limit projections are a cone. The target limit property gives the map;
joint monicity of its projections gives uniqueness. Forgetting commutativity is
faithful, so the same construction gives the commutative-ring sheaf map. -/
theorem completedCoefficientMap_existsUnique :
    ∃! φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
        completedIntegralCommRingSheafUnrestricted l L Y,
      ∀ n : ℕ,
        φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
          completedIntegralCommRingProjectionUnrestricted l E Y n ≫
            integralScalarQuotientSheafMap l E L ι Y n := by
  let forgetComm := sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let α : integralCoefficientSheafSystem l E Y ⟶
      integralCoefficientSheafSystem l L Y :=
    NatTrans.ofOpSequence
      (fun n ↦ forgetComm.map (integralScalarQuotientSheafMap l E L ι Y n))
      (by
        intro n
        simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
        change integralCoefficientSheafTransition l E Y n ≫ _ =
          _ ≫ integralCoefficientSheafTransition l L Y n
        unfold integralCoefficientSheafTransition integralScalarQuotientSheafMap
        change forgetComm.map _ ≫ forgetComm.map _ =
          forgetComm.map _ ≫ forgetComm.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 2
        ext x
        exact RingHom.congr_fun (integralScalarQuotientMap_transition l E L ι n).symm x.down)
  let c : Cone (integralCoefficientSheafSystem l L Y) :=
    { pt := completedIntegralCoefficientSheafUnrestricted l E Y
      π := (limit.cone (integralCoefficientSheafSystem l E Y)).π ≫ α }
  let φr := limit.lift (integralCoefficientSheafSystem l L Y) c
  let φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y :=
    forgetComm.preimage
      (X := completedIntegralCommRingSheafUnrestricted l E Y)
      (Y := completedIntegralCommRingSheafUnrestricted l L Y) φr
  have hproj (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (n : ℕ) :
      forgetComm.map (completedIntegralCommRingProjectionUnrestricted l F Y n) =
        limit.π (integralCoefficientSheafSystem l F Y) (op n) := by
    ext U x
    rfl
  have hφ (n : ℕ) :
      φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
        completedIntegralCommRingProjectionUnrestricted l E Y n ≫
          integralScalarQuotientSheafMap l E L ι Y n := by
    apply forgetComm.map_injective
    rw [Functor.map_comp, Functor.map_comp, hproj, hproj]
    change forgetComm.map φ ≫ _ = _
    dsimp only [φ]
    rw [Functor.map_preimage]
    exact limit.lift_π c (op n)
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply forgetComm.map_injective
  apply limit.hom_ext
  intro n
  have h := congrArg forgetComm.map ((hψ n.unop).trans (hφ n.unop).symm)
  simpa only [Functor.map_comp, hproj] using h

/-- The canonical completed coefficient map, uniquely fixed by its residues.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedCoefficientMap :
    completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y :=
  (completedCoefficientMap_existsUnique l E L ι Y).exists.choose

set_option linter.defProp false in
/-- The existing universal derived-change-of-rings witness, with standard localizations.
Source: Stacks Tag 06YY (blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarChangeData :=
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheafUnrestricted l E Y)
    (O' := completedIntegralCommRingSheafUnrestricted l L Y)
    (completedCoefficientMap l E L ι Y)

/-- Ordinary sheafified extension along the canonical completed coefficient map.
Source: Stacks Tag 06YY (blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedOrdinaryScalarExtension :
    integralTowerModules l E Y ⥤ integralTowerModules l L Y :=
  (completedScalarChangeData l E L ι Y).choose

/-- Additivity of ordinary extension from the canonical tensor witness.
Source: Stacks Tag 06YY (blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable instance completedOrdinaryScalarExtension_additive :
    (completedOrdinaryScalarExtension l E L ι Y).Additive :=
  (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose

/-- Termwise ordinary extension, before any completion.
Source: Stacks Tag 06YY (blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedOrdinaryScalarComplex :=
  (completedOrdinaryScalarExtension l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Ordinary derived scalar extension with its universal K-flat computation.
Source: Stacks Tag 06YY (blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedDerivedScalarExtension :
    DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l L Y) :=
  (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

/-- The universal counit on a complex, invertible when that complex is K-flat.
Source: Stacks Tag 06YY (blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarCounit
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (completedDerivedScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((completedOrdinaryScalarComplex l E L ι Y).obj P) :=
  (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose_spec.2.2
    |>.choose_spec.choose.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)

/-- Sheafified s tensor x in the ordinary extension, with the witness's canonical transport.
Source: Stacks Tag 06YY (blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarTensorSection
    (M : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U) (x : M.val.obj U) :
    ((completedOrdinaryScalarExtension l E L ι Y).obj M).val.obj U :=
  (eqToHom ((completedScalarChangeData l E L ι Y).choose_spec.choose M).symm).val.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (completedCoefficientMap l E L ι Y) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((completedCoefficientMap l E L ι Y).hom.app U).hom] x))

/-- The strict transition endomorphism of the coefficient-extension tower.
Source: Stacks Tag 08TC (blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarRoosEndomorphism
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
    (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P))

/-- The uniquely specified chain comparison to the strict product cone.
Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: tensor the target quotient maps with P. The completed coefficient map's residue
equations make these maps balanced and S-linear; they commute with transitions and
are natural in P. Their product is killed strictly by 1-s. Apply mappingCocone.lift
with zero degree -1 cochain. The two projections determine the map uniquely in every
degree. This also proves naturality without any choice of a triangle filler. -/
theorem completedScalarChainComparison_existsUnique :
    ∃! b : completedOrdinaryScalarComplex l E L ι Y ⟶
        integralScalarComplexFunctor l E L ι Y,
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
        (n : ℕ) (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((b.app P).f i ≫
          (CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
          (Pi.π
            (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i).val.app U)
            (completedScalarTensorSection l E L ι Y (P.X i) U s x) =
          integralScalarTensorSection l E L ι Y n (P.X i) U
            ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
        (b.app P).f i ≫
          (CochainComplex.mappingCocone.snd
            (completedScalarRoosEndomorphism l E L ι Y P)).v i (i - 1) (by omega) = 0) := by
  sorry

/-- The canonical chain comparison, with both cone components fixed by the theorem.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarChainComparison :
    completedOrdinaryScalarComplex l E L ι Y ⟶ integralScalarComplexFunctor l E L ι Y :=
  (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose

/-- Descent of the specific chain comparison, not an arbitrary map to a derived limit.
Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: the derived-change-of-rings counit is invertible on good representatives.
Compose it with the localized chain comparison and the inverse of the normalized
strict-extension comparison. Naturality holds on chain maps by the two universal
comparisons and the chain comparison. Good representatives localize to D(R); hence
these maps descend uniquely. This proves independence of every chosen resolution. -/
theorem completedScalarComparison_existsUnique :
    ∃! χ : completedDerivedScalarExtension l E L ι Y ⟶
        integralScalarExtensionOfUniverses l E L ι Y,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P =
          completedScalarCounit l E L ι Y P.obj ≫
            DerivedCategory.Q.map ((completedScalarChainComparison l E L ι Y).app P.obj) := by
  sorry

/-- The canonical completion map χ, natural on the entire derived category.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarComparison :
    completedDerivedScalarExtension l E L ι Y ⟶ integralScalarExtensionOfUniverses l E L ι Y :=
  (completedScalarComparison_existsUnique l E L ι Y).exists.choose

/-- The relative field degree for the given inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarRelativeDegree : ℕ :=
  letI := ι.toAlgebra
  Module.finrank E L

/-- Multiplication identifies ordinary scalar extension along the identity with P.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: the residue equations identify the completed identity map with the identity.
The balanced maps s tensor x ↦ s*x and x ↦ 1 tensor x are inverse, linear, commute
with restrictions and differentials, and are natural in P. Sheafification preserves
the inverse equations. Pure tensors generate locally, proving uniqueness. -/
theorem completedScalarIdentityMultiplication_existsUnique :
    ∃! μ : completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) Y ≅
        𝟭 (CochainComplex (integralTowerModules l E Y) ℤ),
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U)
        (x : (P.X i).val.obj U),
        ((μ.hom.app P).f i).val.app U
          (completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) Y (P.X i) U s x) =
            s • x := by
  sorry

/-- The actual multiplication isomorphism, fixed on every pure tensor.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarIdentityMultiplication :
    completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) Y ≅
      𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) :=
  (completedScalarIdentityMultiplication_existsUnique l E Y).exists.choose

/-- The completeness unit directly from the reductions of P and zero shifted component.
Source: Bhatt--Scholze, Definition 3.5.2 and Proposition 3.5.1
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: the canonical tensor units send x to 1 tensor x at every level. The transitions
send this to the next unit, hence the product map is killed by 1-s. The mapping cocone
lift with zero cochain supplies the chain map, natural in P. The two cone projections
and local generation by the tensor units determine it uniquely. -/
theorem completedScalarIdentityUnit_existsUnique :
    ∃! η : 𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) ⟶
        integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E) Y,
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U),
        (((η.app P).f i ≫
          (CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E E (AlgHom.id ℚ_[l] E) Y P)).f i ≫
          (Pi.π
            (fun n ↦ ((integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) Y).obj P).obj
              (op n)) n).f i).val.app U) x =
          integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) Y n (P.X i) U 1 x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
        (η.app P).f i ≫
          (CochainComplex.mappingCocone.snd
            (completedScalarRoosEndomorphism l E E (AlgHom.id ℚ_[l] E) Y P)).v
              i (i - 1) (by omega) = 0) := by
  sorry

/-- The specified completeness unit before localization, constructed independently of χ.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarIdentityUnit :
    𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) ⟶
      integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E) Y :=
  (completedScalarIdentityUnit_existsUnique l E Y).exists.choose

/-- Finite freeness, invertibility of the specified comparison on derived-complete
inputs, and derived completeness of ordinary extension.
Source: Bhatt--Scholze, Lemma 6.8.2(1), Definition 3.4.10, Lemma 3.4.12 and
Proposition 3.5.1 (blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: uniqueness of extending absolute values gives O_E = E intersect O_L and
 t = u v^e for a unit u and e positive. Completeness of E identifies O_E with its
 t-adic limit. Finite quotients and the finite-over-complete-ring criterion give
 O_L finite over O_E; torsion-freeness and the DVR theorem give a basis of size [L:E].
The basis and its coordinate inverse commute with quotients and constant
sheafification. Taking inverse limits over the cofinal exponents en gives R^d = S,
with exactly the displayed R-action. Stacks 093M identifies completed quotients
with the finite constant coefficient sheaves and proves regularity of t and v.
Resolve K by a flat-term K-flat complex P. Its ordinary extension Q is K-flat.
The regular Koszul-to-quotient comparison identifies the specified quotient unit
with the Koszul reflector unit. The Roos completeness assumption first implies
local t-completeness of K, so this specific unit is invertible. The basis identifies
Q, its quotients, products, cone and unit over R with d finite copies of those of P.
Restriction detects acyclicity, so Q is locally t-complete over S. The augmented
Cech complexes [S -> S[1/t]] and [S -> S[1/v]] are canonically identical since
 t = u v^e. Their reflectors give local v-completeness, and the Koszul unit criterion
makes the specific v-quotient unit invertible. Associativity sends
(p tensor s) tensor z to p tensor residue(s)z; its inverse sends p tensor z to
(p tensor 1) tensor z. These commute with all transitions and units, identifying
the quotient unit with exactly the chain comparison above, including its zero
shifted component. The normalized descent gives the asserted χ and completeness.
For the identity inclusion, multiplication identifies the chain comparison with
the directly constructed reduction unit: both have quotient components x ↦ 1 tensor x
and zero shifted component. Their two-projection uniqueness gives the final equality.
All maps commute with chain maps; localization extends this to arbitrary derived
morphisms. The basis checks invertibility only and never chooses χ. -/
theorem finiteFreeCompletedScalarComparison :
    Nonempty
      (((SheafOfModules.restrictScalars
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (completedCoefficientMap l E L ι Y))).obj
              (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L Y))) ≅
        ∏ᶜ fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ∧
    (∀ K : DerivedCategory (integralTowerModules l E Y),
      IsDerivedCompleteUnrestricted l E Y K →
        IsIso ((completedScalarComparison l E L ι Y).app K) ∧
          IsDerivedCompleteUnrestricted l L Y
            ((completedDerivedScalarExtension l E L ι Y).obj K)) ∧
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) Y).app
          (DerivedCategory.Q.obj P.obj) ≫
          (integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E) Y).hom.app P =
        completedScalarCounit l E E (AlgHom.id ℚ_[l] E) Y P.obj ≫
          DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E Y).hom.app P.obj) ≫
          DerivedCategory.Q.map ((completedScalarIdentityUnit l E Y).app P.obj) := by
  sorry

end WeilConjectures
