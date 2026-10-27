/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Topology.Constructible
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities

import all Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import all Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import all Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.Paper.PullbackFiniteConstantLocalModel
import Mathlib.Algebra.Field.Equiv
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Field-scalar stratified heart closure and locally closed support

Source: main-20261015, sk-lem-coefficient-heart.proof.md (1) and
sk-thm-sf-pf-field-tensor.proof.md (1), the locally closed extension assertion.
(blueprint: lem-sfb-field-lisse-stratified-heart-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar upperStarFromPoint
  CondensedRing.upperStarComp CondensedRing.upperStarLowerStarAdjunction

private theorem support_ringMonObj (A : Ab.{u + 1}) [MonObj A] [IsCommMonObj A] :
    @AddCommGrpCat.ringMonObj A (InternalAbelianSheafModule.commRing A).toRing =
      (inferInstance : MonObj A) := by
  apply MonObj.ext
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  exact TensorProduct.ext' fun _ _ ↦ rfl

private theorem support_scalarMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (scalarSections.{u}).monObjObj Λ = AddCommGrpCat.ringMonObj
      ((InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) Λ).obj.obj
        (Opposite.op (Profinite.of PUnit.{u + 1}))) := by
  rw [scalarSections_monoidal_eq]
  let A := (Monoidal.CommMonFunctorCategoryEquivalence.functor.obj
    ((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapCommMon.obj
      (CommMon.mk Λ))).obj (Opposite.op (Profinite.of PUnit.{u + 1}))
  change _ = @AddCommGrpCat.ringMonObj A.X
    (InternalAbelianSheafModule.commRing A.X).toRing
  rw [support_ringMonObj]
  rfl

private theorem support_finitelyPresentedIsFree
    (K : Type (u + 1)) [Field K] (A : Ab.{u + 1}) [MonObj A]
    (φ : AddCommGrpCat.of K ⟶ A) [IsMonHom φ] [IsIso φ]
    (P : Mod Ab.{u + 1} A) (hP : Mod.IsFinitelyPresented A P) : Mod.IsFree A P := by
  classical
  let Q := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : Q.IsEquivalence := by dsimp only [Q]; infer_instance
  have : Q.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [Q]
    infer_instance
  let r : (Mod.comap φ).obj (Mod.regular (A)) ≅
      Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  let b : Q.obj (Mod.regular (A)) ≃ₗ[K] K :=
    ((internalToModule K).mapIso r).toLinearEquiv.trans (internalRegularCoordinates K)
  let c (n : ℕ) := finiteFreeEvaluationCoords (Mod.regular (A)) Q b n
  obtain ⟨n, m, f, ⟨ef⟩⟩ := hP
  let eQ : Q.obj P ≅ cokernel (Q.map f) := Q.mapIso ef ≪≫ PreservesCokernel.iso Q f
  have : Module.Finite K (Q.obj (Mod.finiteFree (A) n)) :=
    Module.Finite.of_injective (c n).toLinearMap (c n).injective
  have : Module.Finite K (cokernel (Q.map f) : ModuleCat K) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient (Q.map f)).toLinearEquiv.symm
  have : Module.Finite K (Q.obj P) := Module.Finite.equiv eQ.toLinearEquiv.symm
  let B := Module.finBasis K (Q.obj P)
  refine ⟨Module.finrank K (Q.obj P), ⟨Q.preimageIso ?_⟩⟩
  exact (B.equivFun.trans (c _).symm).toModuleIso

private theorem support_scalarFree
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hfield : IsField ((InternalAbelianSheafModule.sectionRingSheaf
      (coherentTopology Profinite.{u}) Λ.X).obj.obj (Opposite.op (⊤_ Profinite.{u}))))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ.X))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ.X) P) :
    Mod.IsFree (scalarRingObj Λ.X) P := by
  classical
  let R := InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) Λ.X
  let K := R.obj.obj (Opposite.op (Profinite.of PUnit.{u + 1}))
  let e := R.obj.mapIso (Profinite.isTerminalPUnit.uniqueUpToIso terminalIsTerminal).op
  have hK : IsField K := e.commRingCatIsoToRingEquiv.toMulEquiv.isField_congr.mp hfield
  let : Field K := hK.toField
  let φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ.X := 𝟙 _
  have : IsIso φ := IsIso.id _
  have : IsMonHom φ := by
    change @IsMonHom _ _ _ _ _ _ ((scalarSections.{u}).monObjObj Λ.X) _
    rw [support_scalarMonObj]
    exact inferInstanceAs (IsMonHom (𝟙 (AddCommGrpCat.of K)))
  exact support_finitelyPresentedIsFree K _ φ P hP

private theorem support_modelsLisse
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hfield : IsField ((InternalAbelianSheafModule.sectionRingSheaf
      (coherentTopology Profinite.{u}) Λ.X).obj.obj (Opposite.op (⊤_ Profinite.{u}))))
    {T : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
    (hM : HasFiniteConstantLocalModel Λ.X T M) : IsLisseCoefficientModule Λ.X M :=
  models_free_cover Λ.X M (support_scalarFree Λ hfield) hM

private theorem support_modelAlongFactorization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y D : Scheme.{u}}
    (f : Y ⟶ X) (p : D ⟶ Y) (a : D ⟶ X) (ha : a = p ≫ f)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ Y ((CondensedRing.upperStar Λ f).obj M)) :
    HasFiniteConstantLocalModel Λ D ((CondensedRing.upperStar Λ a).obj M) := by
  exact finiteModel_iso Λ D
    (((CondensedRing.upperStarComp Λ p f).app M).symm ≪≫
      eqToIso (congrArg (fun q ↦ (CondensedRing.upperStar Λ q).obj M) ha.symm))
    (pullback_finiteConstantLocalModel Λ p _ hM)

private theorem support_strataCommon
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (S T : Scheme.Stratification X)
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hS : ∀ a, HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj A))
    (hT : ∀ a, HasFiniteConstantLocalModel Λ (T.domain a)
      ((CondensedRing.upperStar Λ (T.immersion a)).obj B)) :
    ∃ R : Scheme.Stratification X, ∀ a : Fin R.n,
      HasFiniteConstantLocalModel Λ (R.domain a)
        ((CondensedRing.upperStar Λ (R.immersion a)).obj A) ∧
      HasFiniteConstantLocalModel Λ (R.domain a)
        ((CondensedRing.upperStar Λ (R.immersion a)).obj B) := by
  classical
  let R := S.inter T
  refine ⟨R, ?_⟩
  intro a
  let b := (finProdFinEquiv.symm a).1
  let c := (finProdFinEquiv.symm a).2
  let p : R.domain a ⟶ S.domain b := pullback.fst (S.immersion b) (T.immersion c)
  let q : R.domain a ⟶ T.domain c := pullback.snd (S.immersion b) (T.immersion c)
  have hp : R.immersion a = p ≫ S.immersion b := rfl
  have hq : R.immersion a = q ≫ T.immersion c := pullback.condition
  exact ⟨support_modelAlongFactorization Λ _ p _ hp A (hS b),
    support_modelAlongFactorization Λ _ q _ hq B (hT c)⟩

private theorem support_commonModels
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hA : IsConstantModelConstructible Λ X A) (hB : IsConstantModelConstructible Λ X B) :
    ∃ R : Scheme.Stratification X, ∀ a : Fin R.n,
      HasFiniteConstantLocalModel Λ (R.domain a)
        ((CondensedRing.upperStar Λ (R.immersion a)).obj A) ∧
      HasFiniteConstantLocalModel Λ (R.domain a)
        ((CondensedRing.upperStar Λ (R.immersion a)).obj B) := by
  classical
  have hq : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hA' : IsFiniteConstantStratified Λ X A :=
    (if_pos hq : IsConstantModelConstructible Λ X A = _).mp hA
  have hB' : IsFiniteConstantStratified Λ X B :=
    (if_pos hq : IsConstantModelConstructible Λ X B = _).mp hB
  obtain ⟨S, hS⟩ := hA'
  obtain ⟨T, hT⟩ := hB'
  exact support_strataCommon Λ S T A B hS hT


/-- Field-scalar constant-model constructibility is closed under the stated ambient
operations, provided lisse modules have the three closure properties on all locally
closed subschemes. Extension of a lisse module along an open immersion followed by a
closed immersion is constructible, with the specified three restrictions. Both
extensions are exact, and their termwise degree-zero complex is the degree-zero complex
of the extended module in the ordinary unbounded derived category.

Source: main-20261015, sk-lem-coefficient-heart.proof.md (1) and
sk-thm-sf-pf-field-tensor.proof.md (1), locally closed extension assertion
(blueprint: lem-sfb-field-lisse-stratified-heart-support).

Proof:
1. Identify sections at the chosen terminal profinite set with sections at PUnit.
The evaluated scalar ring object is the ring object of that section ring. Transport a
finitely presented internal scalar module to ordinary modules over this field. Its
finite free presentation makes it finite dimensional, so its finite basis transports
back to an internal finite free presentation. The existing scalar-extension comparison
then makes finite constant local models lisse. Conversely lisse modules have such models.
2. Intersect the two adapted scheme stratifications using their actual fibre products.
Pull back the two finite constant models along the projections and use the composition
comparison to identify them with the restrictions to this common stratification.
3. Exact restriction preserves limiting kernel forks, colimiting cokernel coforks, and
short exact sequences. On the common stratification apply the assumed lisse closure,
then turn lisse modules back into finite constant models. The zero and isomorphism
assertions are the existing generic constant-model assertions.
4. The closed immersion makes Z Noetherian; the open immersions in question are
quasi-compact. Condensed open-closed recollement gives exactness of the closed direct
image and its counit isomorphism. The open extension is exact. The generic proved
open-extension and closed-pushforward stratification constructions, applied successively
to the lisse model, prove constructibility of the locally closed extension.
5. Combine pullback composition, the closed counit, and the inverse open unit for the
restriction to S. The same closed counit and the open-module restriction identities give
zero on any closed complement in Z. On any open complement in X, the direct image is
zero because its sections are evaluated on the empty fibre product.
6. Apply the natural comparison between a single complex and its termwise functor image
first for the open extension and then for the closed direct image. Map these two
isomorphisms through the derived localization to obtain the degree-zero comparison. -/
theorem field_lisse_stratified_heart_support
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hfield : IsField ((CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf
      (coherentTopology Profinite.{u}) Λ.X).obj.obj (Opposite.op (⊤_ Profinite.{u}))))
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (hclosed : ∀ (T : Scheme.{u}) (a : T ⟶ X), IsImmersion a →
      ObjectProperty.IsClosedUnderKernels (IsLisseCoefficientModule Λ.X (X := T)) ∧
      ObjectProperty.IsClosedUnderCokernels (IsLisseCoefficientModule Λ.X (X := T)) ∧
      ObjectProperty.IsClosedUnderExtensions (IsLisseCoefficientModule Λ.X (X := T))) :
    IsConstantModelConstructible Λ.X X
      (0 : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) ∧
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ.X X) ∧
    ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ.X X) ∧
    ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ.X X) ∧
    ObjectProperty.IsClosedUnderExtensions (IsConstantModelConstructible Λ.X X) ∧
    ∀ (S Z : Scheme.{u}) (j : S ⟶ Z) [IsOpenImmersion j]
      (i : Z ⟶ X) [IsClosedImmersion i], Topology.IsConstructible (Set.range (j ≫ i)) →
      PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ.X j) ∧
      PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ.X j) ∧
      PreservesFiniteLimits (CondensedRing.lowerStar Λ.X i) ∧
      PreservesFiniteColimits (CondensedRing.lowerStar Λ.X i) ∧
      ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S),
        IsLisseCoefficientModule Λ.X L →
        IsConstantModelConstructible Λ.X X
          ((CondensedRing.lowerStar Λ.X i).obj
            ((CondensedRing.openImmersionLowerShriek Λ.X j).obj L)) ∧
        Nonempty ((CondensedRing.upperStar Λ.X (j ≫ i)).obj
          ((CondensedRing.lowerStar Λ.X i).obj
            ((CondensedRing.openImmersionLowerShriek Λ.X j).obj L)) ≅ L) ∧
        (∀ (K : Scheme.{u}) (k : K ⟶ Z) [IsClosedImmersion k],
          Set.range k = (Set.range j)ᶜ →
          IsZero ((CondensedRing.upperStar Λ.X (k ≫ i)).obj
            ((CondensedRing.lowerStar Λ.X i).obj
              ((CondensedRing.openImmersionLowerShriek Λ.X j).obj L)))) ∧
        (∀ (U : Scheme.{u}) (v : U ⟶ X) [IsOpenImmersion v],
          Set.range v = (Set.range i)ᶜ →
          IsZero ((CondensedRing.upperStar Λ.X v).obj
            ((CondensedRing.lowerStar Λ.X i).obj
              ((CondensedRing.openImmersionLowerShriek Λ.X j).obj L)))) ∧
        Nonempty (DerivedCategory.Q.obj
          (((CondensedRing.lowerStar Λ.X i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((CondensedRing.openImmersionLowerShriek Λ.X j).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
                ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L))) ≅
          (DerivedCategory.singleFunctor _ 0).obj
            ((CondensedRing.lowerStar Λ.X i).obj
              ((CondensedRing.openImmersionLowerShriek Λ.X j).obj L))) := by
  classical
  have : IsNoetherian X := ⟨⟩
  have hzero := constantModelConstructible_of_isZero Λ.X X _ (isZero_zero _)
  have hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstantModelConstructible Λ.X X) :=
    (constantModelConstructibleFiniteTor_wellDefined Λ.X X).1
  have hkernels : ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ.X X) := by
    refine ⟨?_⟩
    rintro _ ⟨f, k, hk, hAB⟩
    obtain ⟨R, hR⟩ := support_commonModels Λ.X _ _ hAB.1 hAB.2
    rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
    refine ⟨R, fun a ↦ ?_⟩
    have := R.isImmersion a
    have := (hclosed (R.domain a) (R.immersion a) inferInstance).1
    exact lisse_finiteModel Λ.X _ _
      (ObjectProperty.prop_of_isLimit_kernelFork (IsLisseCoefficientModule Λ.X (X := R.domain a))
        (k.mapIsLimit hk (CondensedRing.upperStar Λ.X (R.immersion a)))
        (support_modelsLisse Λ hfield _ (hR a).1)
        (support_modelsLisse Λ hfield _ (hR a).2))
  have hcokernels :
      ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ.X X) := by
    refine ⟨?_⟩
    rintro _ ⟨f, k, hk, hAB⟩
    obtain ⟨R, hR⟩ := support_commonModels Λ.X _ _ hAB.1 hAB.2
    rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
    refine ⟨R, fun a ↦ ?_⟩
    have := R.isImmersion a
    have := (hclosed (R.domain a) (R.immersion a) inferInstance).2.1
    exact lisse_finiteModel Λ.X _ _
      (ObjectProperty.prop_of_isColimit_cokernelCofork
        (IsLisseCoefficientModule Λ.X (X := R.domain a))
        (k.mapIsColimit hk (CondensedRing.upperStar Λ.X (R.immersion a)))
        (support_modelsLisse Λ hfield _ (hR a).1)
        (support_modelsLisse Λ hfield _ (hR a).2))
  have hextensions :
      ObjectProperty.IsClosedUnderExtensions (IsConstantModelConstructible Λ.X X) := by
    refine ⟨?_⟩
    intro S hS h₁ h₃
    obtain ⟨R, hR⟩ := support_commonModels Λ.X _ _ h₁ h₃
    rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
    refine ⟨R, fun a ↦ ?_⟩
    have := R.isImmersion a
    have := (hclosed (R.domain a) (R.immersion a) inferInstance).2.2
    exact lisse_finiteModel Λ.X _ _
      (ObjectProperty.prop_X₂_of_shortExact (IsLisseCoefficientModule Λ.X (X := R.domain a))
        (hS.map_of_exact (CondensedRing.upperStar Λ.X (R.immersion a)))
        (support_modelsLisse Λ hfield _ (hR a).1)
        (support_modelsLisse Λ hfield _ (hR a).2))
  refine ⟨hzero, hiso, hkernels, hcokernels, hextensions, ?_⟩
  intro S Z j _ i _ _
  have : TopologicalSpace.NoetherianSpace Z := i.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : IsNoetherian Z := ⟨⟩
  let U := Scheme.openComplementOfIsClosedImmersion i
  have hv : Set.range U.ι = (Set.range i)ᶜ := by
    simp [U, Scheme.openComplementOfIsClosedImmersion]
  have hi : Set.range i = (Set.range U.ι)ᶜ := by rw [hv, compl_compl]
  obtain ⟨hexact, _, _, _, _, _, _, _, _, _, _, _, ⟨ei⟩, _⟩ :=
    CondensedRing.condensed_open_closed_recollement Λ.X i U.ι hv
  have := hexact
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro L hL
  have hG := stratified_closedPush Λ.X i _
    (stratified_openExtension Λ.X j L
      (stratified_of_finiteModel Λ.X S L (lisse_finiteModel Λ.X S L hL)))
  have : IsIso (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ.X j).unit :=
    CondensedRing.openUnitIsIso Λ.X j
  have eL : (CondensedRing.upperStar Λ.X (j ≫ i)).obj
      ((CondensedRing.lowerStar Λ.X i).obj
        ((CondensedRing.openImmersionLowerShriek Λ.X j).obj L)) ≅ L :=
    (CondensedRing.upperStarComp Λ.X j i).app _ ≪≫
      (CondensedRing.upperStar Λ.X j).mapIso (ei.app _) ≪≫
      (asIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app L)).symm
  refine ⟨?_, ⟨eL⟩, ?_, ?_, ?_⟩
  · rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
    exact hG
  · intro K k _ hkj
    obtain ⟨_, ⟨e⟩⟩ := CondensedRing.open_module_restriction_identities Λ.X j k hkj
    exact ((isZero_zero _).of_iso (e.app L)).of_iso
      ((CondensedRing.upperStarComp Λ.X k i).app _ ≪≫
        (CondensedRing.upperStar Λ.X k).mapIso (ei.app _))
  · intro V v _ hvi
    exact CondensedRing.openRestrictionPushforwardZero Λ.X i v hvi _
  · exact ⟨DerivedCategory.Q.mapIso
      ((CondensedRing.lowerStar Λ.X i).mapHomologicalComplex (.up ℤ) |>.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (CondensedRing.openImmersionLowerShriek Λ.X j) (.up ℤ) 0).app L)) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (CondensedRing.lowerStar Λ.X i) (.up ℤ) 0).app _)⟩

end AlgebraicGeometry.ProEtale
