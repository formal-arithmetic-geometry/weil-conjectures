/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Sheaf.Paper.QuotientScalarComparisonDescent
import all Sheaf.Paper.IntegralOperationsWellDefined
import all Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Algebra.Homology.SignedMappingCoconeShift

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
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory

attribute [local irreducible] HasDerivedCategory.standard

universe t u a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
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

attribute [local irreducible] limit

private theorem completedCoefficientMap_id :
    completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) Y = 𝟙 _ := by
  apply (completedCoefficientMap_existsUnique l E E (AlgHom.id ℚ_[l] E) Y).unique
  · exact (completedCoefficientMap_existsUnique l E E (AlgHom.id ℚ_[l] E) Y).exists.choose_spec
  · intro n
    have hring : integralScalarQuotientMap l E E (AlgHom.id ℚ_[l] E) n =
        RingHom.id _ := by
      ext x
      rfl
    have hq : integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) Y n = 𝟙 _ := by
      unfold integralScalarQuotientSheafMap
      rw [hring]
      convert (constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology Y)
        CommRingCat.{max u (t + 1)}).map_id
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        using 1 <;> rfl
    simp only [hq, Category.id_comp, Category.comp_id]

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

attribute [local irreducible] completedScalarChangeData integralScalarReductionWitness

private theorem completedScalarResidue (n : ℕ) :
    completedCoefficientMap l E L ι Y ≫
      completedIntegralCommRingProjectionUnrestricted l L Y n =
        integralScalarRho l E L ι Y n :=
  (completedCoefficientMap_existsUnique l E L ι Y).exists.choose_spec n

private noncomputable def completedScalarModuleLevel (n : ℕ) :=
  integralScalarReduction l E L ι Y n ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))

private noncomputable def completedScalarModuleArrow
    (M : integralTowerModules l E Y) (n : ℕ) :
    (completedOrdinaryScalarExtension l E L ι Y).obj M ⟶
      (completedScalarModuleLevel l E L ι Y n).obj M :=
  eqToHom ((completedScalarChangeData l E L ι Y).choose_spec.choose M) ≫
    SheafOfModules.ScalarComparisonProof.sheafMap (completedCoefficientMap l E L ι Y)
      (integralScalarRho l E L ι Y n)
      (completedIntegralCommRingProjectionUnrestricted l L Y n)
      (completedScalarResidue l E L ι Y n) M ≫
    (SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))).map
      ((integralScalarReductionIso l E L ι Y n).inv.app M)

private theorem completedScalarModuleArrow_tensor
    (M : integralTowerModules l E Y) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : M.val.obj U) :
    (completedScalarModuleArrow l E L ι Y M n).val.app U
      (completedScalarTensorSection l E L ι Y M U s x) =
        integralScalarTensorSection l E L ι Y n M U
          ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x := by
  let e := eqToIso ((completedScalarChangeData l E L ι Y).choose_spec.choose M)
  let q := completedIntegralCommRingProjectionUnrestricted l L Y n
  let r := SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map q)
  let z := (integralScalarReductionIso l E L ι Y n).inv.app M
  have hc : e.inv ≫ completedScalarModuleArrow l E L ι Y M n =
      SheafOfModules.ScalarComparisonProof.sheafMap (completedCoefficientMap l E L ι Y)
        (integralScalarRho l E L ι Y n) q (completedScalarResidue l E L ι Y n) M ≫
          r.map z := by
    simp only [completedScalarModuleArrow, e, eqToIso.inv, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, q, r, z]
  change ((e.inv ≫ completedScalarModuleArrow l E L ι Y M n).val.app U) _ = _
  rw [hc]
  change z.val.app U
    ((SheafOfModules.ScalarComparisonProof.sheafMap (completedCoefficientMap l E L ι Y)
      (integralScalarRho l E L ι Y n) q (completedScalarResidue l E L ι Y n) M).val.app U
        (SheafOfModules.ScalarComparisonProof.tensorSection
          (completedCoefficientMap l E L ι Y) M U s x)) = _
  exact congrArg (z.val.app U)
    (SheafOfModules.ScalarComparisonProof.sheafMap_tmul _ _ _ _ M U s x)

private theorem completedScalar_tensor_ext
    (M : integralTowerModules l E Y) (N : integralTowerModules l L Y)
    (f g : (completedOrdinaryScalarExtension l E L ι Y).obj M ⟶ N)
    (h : ∀ U s x, f.val.app U (completedScalarTensorSection l E L ι Y M U s x) =
      g.val.app U (completedScalarTensorSection l E L ι Y M U s x)) : f = g := by
  apply (cancel_epi
    (eqToIso ((completedScalarChangeData l E L ι Y).choose_spec.choose M)).inv).1
  apply SheafOfModules.tensor_generator_ext (completedCoefficientMap l E L ι Y)
  intro U x s
  exact h U s x

private theorem witnessTensor_naturality
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hobj : ∀ M, G.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), G.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm)
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (G.map f).val.app U ((eqToHom (hobj M).symm).val.app U
      (SheafOfModules.ScalarComparisonProof.tensorSection φ M U s x)) =
    (eqToHom (hobj N).symm).val.app U
      (SheafOfModules.ScalarComparisonProof.tensorSection φ N U s (f.val.app U x)) := by
  rw [hmap]
  change ((eqToHom (hobj M).symm ≫ eqToHom (hobj M) ≫
    SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm).val.app U) _ = _
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact congrArg ((eqToHom (hobj N).symm).val.app U)
    (SheafOfModules.ScalarComparisonProof.map_tensorSection φ M f U s x)

private theorem completedScalarTensorSection_naturality
    {M N : integralTowerModules l E Y} (f : M ⟶ N) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : M.val.obj U) :
    ((completedOrdinaryScalarExtension l E L ι Y).map f).val.app U
      (completedScalarTensorSection l E L ι Y M U s x) =
        completedScalarTensorSection l E L ι Y N U s (f.val.app U x) := by
  exact witnessTensor_naturality (completedCoefficientMap l E L ι Y)
    (completedOrdinaryScalarExtension l E L ι Y)
    (completedScalarChangeData l E L ι Y).choose_spec.choose
    (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose f U s x

private theorem integralScalarTensorSection_naturality
    {M N : integralTowerModules l E Y} (f : M ⟶ N) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    ((integralScalarReduction l E L ι Y n).map f).val.app U
      (integralScalarTensorSection l E L ι Y n M U s x) =
        integralScalarTensorSection l E L ι Y n N U s (f.val.app U x) := by
  exact integralScalarReduction_map_tmul l E L ι Y n f U s x

private theorem completedScalarModuleArrow_naturality
    {M N : integralTowerModules l E Y} (f : M ⟶ N) (n : ℕ) :
    (completedOrdinaryScalarExtension l E L ι Y).map f ≫
        completedScalarModuleArrow l E L ι Y N n =
      completedScalarModuleArrow l E L ι Y M n ≫
        (completedScalarModuleLevel l E L ι Y n).map f := by
  apply completedScalar_tensor_ext l E L ι Y
  intro U s x
  change (completedScalarModuleArrow l E L ι Y N n).val.app U
    (((completedOrdinaryScalarExtension l E L ι Y).map f).val.app U _) =
      ((integralScalarReduction l E L ι Y n).map f).val.app U
        ((completedScalarModuleArrow l E L ι Y M n).val.app U _)
  rw [completedScalarTensorSection_naturality, completedScalarModuleArrow_tensor,
    completedScalarModuleArrow_tensor, integralScalarTensorSection_naturality]

private noncomputable def completedScalarLevelArrow (n : ℕ) :
    completedOrdinaryScalarComplex l E L ι Y ⟶ integralScalarLevel l E L ι Y n where
  app P :=
    { f := fun i ↦ completedScalarModuleArrow l E L ι Y (P.X i) n
      comm' := fun i j _ ↦ (completedScalarModuleArrow_naturality l E L ι Y (P.d i j) n).symm }
  naturality := by
    intro P Q f
    ext i : 1
    exact completedScalarModuleArrow_naturality l E L ι Y (f.f i) n

private theorem completedScalarLevelArrow_transition
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (completedScalarLevelArrow l E L ι Y (n + 1)).app P ≫
        (integralScalarTransition l E L ι Y n).app P =
      (completedScalarLevelArrow l E L ι Y n).app P := by
  ext i : 1
  apply completedScalar_tensor_ext l E L ι Y
  intro U s x
  change (((integralScalarTransition l E L ι Y n).app P).f i).val.app U
    ((completedScalarModuleArrow l E L ι Y (P.X i) (n + 1)).val.app U _) =
      (completedScalarModuleArrow l E L ι Y (P.X i) n).val.app U _
  rw [completedScalarModuleArrow_tensor, completedScalarModuleArrow_tensor]
  have ht := (integralScalarTransition_existsUnique l E L ι Y n).exists.choose_spec
    P i U ((completedIntegralCommRingProjectionUnrestricted l L Y (n + 1)).hom.app U s) x
  erw [ht]
  congr 1
  change ((limit.π (integralCoefficientSheafSystem l L Y) (op (n + 1))).hom.app U ≫
    (integralCoefficientSheafTransition l L Y n).hom.app U) s =
      (limit.π (integralCoefficientSheafSystem l L Y) (op n)).hom.app U s
  have hp := limit.w (integralCoefficientSheafSystem l L Y)
    (homOfLE (Nat.le_succ n)).op
  simp only [integralCoefficientSheafSystem,
    Functor.ofOpSequence_map_homOfLE_succ] at hp
  have hp' := congrArg (fun f ↦ f.hom.app U) hp
  exact ConcreteCategory.congr_hom hp' s

attribute [local semireducible] limit

private theorem complexProduct_hom_ext
    {D : Type*} [Category* D] [Preadditive D] [HasCountableProducts D]
    (X : ℕ → CochainComplex D ℤ) (i : ℤ) {M : D}
    (f g : M ⟶ (∏ᶜ X).X i)
    (h : ∀ n, f ≫ (Pi.π X n).f i = g ≫ (Pi.π X n).f i) : f = g := by
  apply (isLimitOfPreserves (HomologicalComplex.eval D (.up ℤ) i)
    (limit.isLimit (Discrete.functor X))).hom_ext
  intro n
  exact h n.as

attribute [local irreducible] limit

private theorem cocone_degree_ext
    {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D]
    {P K L₀ : CochainComplex D ℤ} (φ : K ⟶ L₀)
    (f g : P ⟶ CochainComplex.mappingCocone φ) (i : ℤ)
    (hf : f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i)
    (hs : f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) :
    f.f i = g.f i := by
  have hi := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ _ := congrArg (f.f i ≫ ·) hi.symm
    _ = g.f i ≫ _ := by rw [comp_add, comp_add, reassoc_of% hf, reassoc_of% hs]
    _ = g.f i := by rw [hi, Category.comp_id]

private theorem zeroCoconeLift_f
    {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D]
    {P K L₀ : CochainComplex D ℤ} (φ : K ⟶ L₀) (α : P ⟶ K)
    (h : α ≫ φ = 0) (i : ℤ) :
    (CochainComplex.mappingCocone.lift φ α 0 (by simp [h])).f i =
      α.f i ≫ (CochainComplex.mappingCocone.inl φ).v i i (by omega) := by
  let β := CochainComplex.mappingCocone.lift φ α 0 (by simp [h])
  rw [← Category.comp_id (β.f i),
    ← CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)]
  simp only [comp_add, ← Category.assoc, β,
    CochainComplex.mappingCocone.lift_f_fst_f,
    CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v, zero_comp, add_zero]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem towerZeroLift_exists
    {D Z : Type*} [Category* D] [Abelian D] [HasCountableProducts D] [Category* Z]
    (F : Z ⥤ CochainComplex D ℤ) (G : Z ⥤ ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (a : ∀ n : ℕ, F ⟶ G ⋙ (evaluation ℕᵒᵖ (CochainComplex D ℤ)).obj (op n))
    (ha : ∀ P n, (a (n + 1)).app P ≫ (G.obj P).map
      (homOfLE (Nat.le_succ n)).op = (a n).app P) :
    ∃ b : F ⟶ G ⋙ integralOperationsRoosFunctor,
      (∀ P : Z, b.app P ≫ (CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ (G.obj P).obj (op n))
        (integralOperationsTowerStep (G.obj P)))) =
          Pi.lift (fun n ↦ (a n).app P)) ∧
      ∀ (P : Z) (i : ℤ), (b.app P).f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n ↦ (G.obj P).obj (op n))
        (integralOperationsTowerStep (G.obj P)))).v
          i (i - 1) (by omega) = 0 := by
  let α (P : Z) : F.obj P ⟶ ∏ᶜ fun n ↦ (G.obj P).obj (op n) :=
    Pi.lift (fun n ↦ (a n).app P)
  let φ P := towerTransitionEndomorphism (K := fun n ↦ (G.obj P).obj (op n))
        (integralOperationsTowerStep (G.obj P))
  have hα P : α P ≫ φ P = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [α, φ, towerTransitionEndomorphism, towerProductShift, comp_sub,
      Category.comp_id, Category.assoc, Pi.lift_π, sub_comp, zero_comp]
    rw [← Category.assoc, Pi.lift_π]
    exact sub_eq_zero.mpr (ha P n).symm
  let β P := CochainComplex.mappingCocone.lift (φ P) (α P) 0 (by simp [hα])
  have hβ P i : (β P).f i =
      (α P).f i ≫ (CochainComplex.mappingCocone.inl (φ P)).v i i (by omega) :=
    zeroCoconeLift_f _ _ (hα P) i
  let b : F ⟶ G ⋙ integralOperationsRoosFunctor :=
    { app := β
      naturality := by
        intro P Q f
        have hn : F.map f ≫ α Q = α P ≫
            Limits.Pi.map (fun n ↦ (G.map f).app (op n)) := by
          apply Pi.hom_ext
          intro n
          simp only [α, Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc]
          exact (a n).naturality f
        ext i : 1
        change (F.map f).f i ≫ (β Q).f i =
          (β P).f i ≫ (integralOperationsRoosMap (G.map f)).f i
        rw [hβ, hβ]
        rw [← Category.assoc, ← HomologicalComplex.comp_f, hn,
          HomologicalComplex.comp_f, Category.assoc]
        exact (congrArg ((α P).f i ≫ ·)
          (SignedCoconeShift.coconeMap_inl (φ P) (φ Q)
            (Arrow.homMk (Limits.Pi.map (fun n ↦ (G.map f).app (op n)))
              (Limits.Pi.map (fun n ↦ (G.map f).app (op n)))
                (integralOperationsRoos_square (G.map f)).symm) i).symm).trans
          (Category.assoc _ _ _).symm }
  refine ⟨b, ?_, ?_⟩
  · intro P
    exact CochainComplex.mappingCocone.lift_fst (φ P) (α P) 0 (by simp [hα])
  · intro P i
    exact CochainComplex.mappingCocone.lift_f_snd_v (φ P) (α P) 0
      (by simp [hα]) i (i - 1) (by omega)

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
  let G := integralScalarTowerFunctor l E L ι Y
  let a (n : ℕ) : completedOrdinaryScalarComplex l E L ι Y ⟶
      G ⋙ (evaluation ℕᵒᵖ (CochainComplex (integralTowerModules l L Y) ℤ)).obj (op n) :=
    completedScalarLevelArrow l E L ι Y n
  have ha P n : (a (n + 1)).app P ≫ (G.obj P).map
      (homOfLE (Nat.le_succ n)).op = (a n).app P := by
    simpa only [G, integralScalarTowerFunctor, Functor.flip_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ] using
        completedScalarLevelArrow_transition l E L ι Y P n
  obtain ⟨b, hf, hs⟩ := towerZeroLift_exists
    (completedOrdinaryScalarComplex l E L ι Y) G a ha
  have hb :
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
    constructor
    · intro P i n U s x
      have hh := congrArg (fun f ↦ f.f i) (hf P)
      change (b.app P).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι Y P)).f i = _ at hh
      rw [← Category.assoc, hh]
      have hp := congrArg (fun f ↦ (f.f i).val.app U)
        (Pi.lift_π (fun n ↦ (a n).app P) n)
      exact (ConcreteCategory.congr_hom hp _).trans
        (completedScalarModuleArrow_tensor l E L ι Y (P.X i) n U s x)
    · exact hs
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply NatTrans.ext
  funext P
  ext i : 1
  let φ := completedScalarRoosEndomorphism l E L ι Y P
  have hf : (b'.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      (b.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i := by
    apply complexProduct_hom_ext
    intro n
    apply completedScalar_tensor_ext l E L ι Y
    intro U s x
    exact (hb'.1 P i n U s x).trans (hb.1 P i n U s x).symm
  have hs := (hb'.2 P i).trans (hb.2 P i).symm
  exact cocone_degree_ext φ (b'.app P) (b.app P) i hf hs

/-- The canonical chain comparison, with both cone components fixed by the theorem.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarChainComparison :
    completedOrdinaryScalarComplex l E L ι Y ⟶ integralScalarComplexFunctor l E L ι Y :=
  (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem scalarMultiplication_existsUnique
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (φ : R ⟶ R)
    (G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    [G.Additive]
    (hobj : ∀ M, G.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), G.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm)
    (hid : φ = 𝟙 R) :
    ∃! μ : G.mapHomologicalComplex (.up ℤ) ≅ 𝟭 _,
      ∀ P i (U : Cᵒᵖ) (s : R.obj.obj U) (x : (P.X i).val.obj U),
        ((μ.hom.app P).f i).val.app U
          ((eqToHom (hobj (P.X i)).symm).val.app U
            (SheafOfModules.ScalarComparisonProof.tensorSection φ (P.X i) U s x)) = s • x := by
  subst φ
  let e M : G.obj M ≅ M := eqToIso (hobj M) ≪≫ SheafOfModules.scalarIdIso M
  have he {M N} (f : M ⟶ N) : G.map f ≫ (e N).hom = (e M).hom ≫ f := by
    simp only [e, Iso.trans_hom, eqToIso.hom, hmap, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact congrArg (eqToHom (hobj M) ≫ ·) (SheafOfModules.scalarIdIso_naturality f)
  let μ : G.mapHomologicalComplex (.up ℤ) ≅ 𝟭 _ :=
    NatIso.ofComponents
      (fun P ↦ HomologicalComplex.Hom.isoOfComponents (fun i ↦ e (P.X i))
        (fun i j _ ↦ (he (P.d i j)).symm))
      (by intro P Q f; ext i : 1; exact he (f.f i))
  have hμ P i (U : Cᵒᵖ) (s : R.obj.obj U) (x : (P.X i).val.obj U) :
      ((μ.hom.app P).f i).val.app U
        ((eqToHom (hobj (P.X i)).symm).val.app U
          (SheafOfModules.ScalarComparisonProof.tensorSection (𝟙 R) (P.X i) U s x)) = s • x := by
    change (((eqToIso (hobj (P.X i))).inv ≫ (e (P.X i)).hom).val.app U) _ = _
    simp only [e, Iso.trans_hom, Iso.inv_hom_id_assoc]
    exact SheafOfModules.scalarIdIso_tmul _ _ _ _
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  apply Iso.ext
  apply NatTrans.ext
  funext P
  ext i : 1
  apply (cancel_epi (eqToIso (hobj (P.X i))).inv).1
  apply SheafOfModules.tensor_generator_ext (𝟙 R)
  intro U x s
  exact (hν P i U s x).trans (hμ P i U s x).symm

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
  exact scalarMultiplication_existsUnique
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) Y)
    (completedOrdinaryScalarExtension l E E (AlgHom.id ℚ_[l] E) Y)
    ((completedScalarChangeData l E E (AlgHom.id ℚ_[l] E) Y).choose_spec.choose)
    ((completedScalarChangeData l E E (AlgHom.id ℚ_[l] E) Y).choose_spec.choose_spec.choose)
    (completedCoefficientMap_id l E Y)

/-- The actual multiplication isomorphism, fixed on every pure tensor.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
noncomputable def completedScalarIdentityMultiplication :
    completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) Y ≅
      𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) :=
  (completedScalarIdentityMultiplication_existsUnique l E Y).exists.choose

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 600000 in
-- Concrete sheaf transports and evaluated cone identities require additional elaboration.
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
  let μ := completedScalarIdentityMultiplication l E Y
  let β := completedScalarChainComparison l E E (AlgHom.id ℚ_[l] E) Y
  let η : 𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) ⟶
      integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E) Y := μ.inv ≫ β
  have hinv (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
      (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
      ((μ.inv.app P).f i).val.app U x =
        completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) Y (P.X i) U 1 x := by
    have h := (completedScalarIdentityMultiplication_existsUnique l E Y).exists.choose_spec
      P i U 1 x
    rw [one_smul] at h
    have hh := congrArg (fun x ↦ ((μ.inv.app P).f i).val.app U x) h
    have he := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ (f.f i).val.app U) (μ.app P).hom_inv_id)
      (completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) Y (P.X i) U 1 x)
    exact hh.symm.trans he
  have hβ := (completedScalarChainComparison_existsUnique l E E (AlgHom.id ℚ_[l] E)
    Y).exists.choose_spec
  have hη :
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
    constructor
    · intro P i n U x
      simp only [η, NatTrans.comp_app, HomologicalComplex.comp_f, Category.assoc,
        SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
      trans (((β.app P).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E E (AlgHom.id ℚ_[l] E) Y P)).f i ≫
        (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) Y).obj P).obj
          (op n)) n).f i).val.app U)
            (completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) Y (P.X i) U 1 x)
      · exact congrArg
          (fun z ↦ (((β.app P).f i ≫
            (CochainComplex.mappingCocone.fst
              (completedScalarRoosEndomorphism l E E (AlgHom.id ℚ_[l] E) Y P)).f i ≫
            (Pi.π (fun n ↦
              ((integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) Y).obj P).obj
                (op n)) n).f i).val.app U) z) (hinv P i U x)
      · have hh := hβ.1 P i n U 1 x
        have h1 :=
          (((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom).map_one
        have hz := congrArg
          (fun s ↦ integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) Y n (P.X i) U s x)
            h1
        exact hh.trans hz
    · intro P i
      dsimp only [η, NatTrans.comp_app, HomologicalComplex.comp_f]
      exact (Category.assoc _ _ _).trans
        ((congrArg ((μ.inv.app P).f i ≫ ·) (hβ.2 P i)).trans comp_zero)
  refine ⟨η, hη, ?_⟩
  intro η' hη'
  apply NatTrans.ext
  funext P
  ext i : 1
  let φ := completedScalarRoosEndomorphism l E E (AlgHom.id ℚ_[l] E) Y P
  have hf : (η'.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      (η.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i := by
    apply complexProduct_hom_ext
    intro n
    ext U x
    exact (hη'.1 P i n U x).trans (hη.1 P i n U x).symm
  have hs : (η'.app P).f i ≫ (CochainComplex.mappingCocone.snd φ).v
      i (i - 1) (by omega) =
      (η.app P).f i ≫ (CochainComplex.mappingCocone.snd φ).v
        i (i - 1) (by omega) :=
    (hη'.2 P i).trans (hη.2 P i).symm
  exact cocone_degree_ext φ (η'.app P) (η.app P) i hf hs

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
