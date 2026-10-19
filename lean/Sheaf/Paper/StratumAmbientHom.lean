/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.EtaleGenericStratumMate

import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
import all Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Parametrized
import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Internal Hom from extension along a stratum

Source: Weil blueprint, six functors, sk-prop-sf-rf-shriek-preservation,
node order 2069 (blueprint: lem-weil-stratum-ambient-hom).

Both formulas are natural isomorphisms on the product of the opposite source derived
category and the target derived category. All derived categories are ordinary and unbounded.
The etale category uses the recorded fixed-scalar presentation. The pro-etale category
uses the recorded intrinsic constant-ring presentation and its canonical coefficient map.
-/

@[expose] public section

set_option autoImplicit false

universe u d e v w a b a' b' a'' b''

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme WeilConjectures
private theorem existsNonempty {α : Sort*} {P : α → Prop} (h : ∃ x, P x) :
    Nonempty α := by
  obtain ⟨x, _⟩ := h
  exact ⟨x⟩


private theorem directImage_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] :
    sfConstantModuleDirectImage f A = proEtaleConstantModuleDirectImage f A := by
  have h : proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (sfConstantCoefficientIso f A) =
      proEtaleCoefficientDirectImageMap f A := by
    change ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
        (proEtaleCoefficientDirectImageMap f A)) = _
    exact Equiv.apply_symm_apply _ _
  unfold sfConstantModuleDirectImage proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage
  rw [h]
private noncomputable def pullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] :
    sfConstantModulePullback f A ≅ sfIntrinsicPullback A f :=
  (sfConstantModuleAdjunction f A).leftAdjointUniq
    ((sfIntrinsicConstantModuleAdjunction f A).ofNatIsoRight
      (eqToIso (directImage_eq f A)).symm)
/- The sheaf open adjunction is transported through the actual coefficient equivalences.
This uses only the fixed-coefficient open adjunction, without any exchange theorem. -/
private noncomputable def openSheafAdjunction
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    sfIntrinsicExtensionByZero j A ⊣ sfConstantModulePullback j A :=
  (((sfIntrinsicModuleEquivalence U A).symm.toAdjunction.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).comp
    (sfIntrinsicModuleEquivalence X A).toAdjunction).ofNatIsoRight (pullbackIso j A).symm

private noncomputable def openAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⊣
      (sfConstantModulePullback j A).mapDerivedCategory := by
  let a := openSheafAdjunction A j
  letI : CatCommSq ((sfIntrinsicExtensionByZero j A).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q
      (sfIntrinsicExtensionByZero j A).mapDerivedCategory :=
    ⟨(sfIntrinsicExtensionByZero j A).mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq ((sfConstantModulePullback j A).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q
      (sfConstantModulePullback j A).mapDerivedCategory :=
    ⟨(sfConstantModulePullback j A).mapDerivedCategoryFactors.symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) _ _
/- Exact restrictions that detect zero objects detect isomorphisms through kernels and
cokernels. The derived statement follows by commuting each restriction with homology. -/
private theorem jointIsoOfZero
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : C ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hz : ∀ M, IsZero (F.obj M) → IsZero (G.obj M) → IsZero M)
    {M N : C} (f : M ⟶ N) (hf : IsIso (F.map f)) (hg : IsIso (G.map f)) :
    IsIso f := by
  have : Mono f := Preadditive.mono_of_isZero_kernel f
    (hz _ ((isZero_kernel_of_mono (F.map f)).of_iso (asIso (kernelComparison f F)))
      ((isZero_kernel_of_mono (G.map f)).of_iso (asIso (kernelComparison f G))))
  have : Epi f := Preadditive.epi_of_isZero_cokernel f
    (hz _ ((isZero_cokernel_of_epi (F.map f)).of_iso ((asIso (cokernelComparison f F)).symm))
      ((isZero_cokernel_of_epi (G.map f)).of_iso ((asIso (cokernelComparison f G)).symm)))
  exact isIso_of_mono_of_epi f

private theorem jointDerivedIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : C ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hz : ∀ M, IsZero (F.obj M) → IsZero (G.obj M) → IsZero M)
    {M N : DerivedCategory C} (f : M ⟶ N)
    (hf : IsIso (F.mapDerivedCategory.map f))
    (hg : IsIso (G.mapDerivedCategory.map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  apply jointIsoOfZero F G hz
  · exact (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by dsimp; infer_instance)
  · exact (NatIso.isIso_map_iff (G.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by dsimp; infer_instance)

private theorem derivedZeroOfHomology
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C)
    (hz : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj K)) :
    IsZero K := by
  let : Zero (DerivedCategory C) := HasZeroObject.zero' _
  have : IsIso (0 : 0 ⟶ K) := (DerivedCategory.isIso_iff C _).2 fun n ↦
    ((DerivedCategory.homologyFunctor C n).map_isZero (isZero_zero _)).isIso (hz n) _
  exact (isZero_zero _).of_iso (asIso (0 : 0 ⟶ K)).symm

private theorem derivedCompositeZero
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hz : ∀ M, IsZero (G.obj (F.obj M))) (K : DerivedCategory C) :
    IsZero (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) := by
  apply derivedZeroOfHomology
  intro n
  exact (hz ((DerivedCategory.homologyFunctor C n).obj K)).of_iso
    (((G.mapDerivedCategoryHomologyFunctorIso n).app (F.mapDerivedCategory.obj K)).symm ≪≫
      G.mapIso ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm)

private theorem closedCounit
    (A : Type u) [CommRing A] [Finite A]
    {Z U X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hc : Set.range j = (Set.range i)ᶜ) :
    IsIso (sfConstantModuleAdjunction i A).counit := by
  let R := proEtaleConstantRing X A
  let Ri := proEtaleConstantRing Z A
  let ci := sfConstantCoefficientIso i A
  let V := ProEt.mk j
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := inferInstanceAs (QuasiCompact j)
  obtain ⟨q, hq, ai, aj, hh, _⟩ := proEtale_ringed_open_closed i V hc R
  have : IsIso ai.counit := by
    have := hh
    exact NatIso.isIso_of_isIso_app _
  have : (proEtaleRingedDirectImage i R).Full := ai.fullyFaithfulROfIsIsoCounit.full
  have : (proEtaleRingedDirectImage i R).Faithful := ai.fullyFaithfulROfIsIsoCounit.faithful
  let ei := proEtaleScalarEquivalence Z ((sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso ci)
  let d := coefficientDirectImageIso i R Ri ci
  have : (sfConstantModuleDirectImage i A).Full := Functor.Full.of_iso d
  have : (sfConstantModuleDirectImage i A).Faithful := Functor.Faithful.of_iso d
  exact (sfConstantModuleAdjunction i A).counit_isIso_of_R_fully_faithful

private theorem closedOpenZero
    (A : Type u) [CommRing A] [Finite A]
    {Z U X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hc : Set.range j = (Set.range i)ᶜ)
    (P : proEtaleRingModules Z (proEtaleConstantRing Z A)) :
    IsZero ((sfConstantModulePullback j A).obj
      ((sfConstantModuleDirectImage i A).obj P)) := by
  exact (proEtaleRingModule_closed_essImage_iff_and_unit_isIso i j hc
    (proEtaleConstantRing X A) (proEtaleConstantRing Z A) (proEtaleConstantRing U A)
    (sfConstantCoefficientIso i A) (sfConstantCoefficientIso j A) _).1.1
      ⟨P, ⟨Iso.refl _⟩⟩

private theorem tensorZeroRight
    {D : Type*} [Category* D] [HasZeroMorphisms D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (b : @SymmetricCategory D _ S.monoidal)
    (Q P : D) (hP : IsZero P) : IsZero (S.tensor.obj (Q, P)) := by
  let := S.monoidal
  let := b
  have : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight Q) :=
    (S.adjunction Q).leftAdjoint_preservesColimits
  have hz : IsZero ((MonoidalCategory.tensorRight Q).obj P) :=
    (hP.isInitial.isInitialObj (MonoidalCategory.tensorRight Q) P).isZero
  exact hz.of_iso (β_ Q P)

private noncomputable def intrinsicTensorModel
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u}
        (ProEt.topology X) (proEtaleConstantRing X A)))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (ProEt.topology X) (proEtaleConstantRing X A) S) :
    ProEtaleTensorModel X (proEtaleConstantRing X A) := by
  let i := ObjectProperty.ιOfLE
    (P := proEtaleFlatRepresentatives X (proEtaleConstantRing X A))
    (P' := CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := proEtaleConstantRing X A))
    (fun _ hP ↦ hP.1)
  exact { tensor := S.tensor
          representative := Functor.isoWhiskerLeft (i.prod i) T.comparison }

private theorem tensorPullback
    (A : Type u) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (SX : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u}
        (ProEt.topology X) (proEtaleConstantRing X A)))
    (SY : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u}
        (ProEt.topology Y) (proEtaleConstantRing Y A)))
    (TX : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (ProEt.topology X) (proEtaleConstantRing X A) SX)
    (TY : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (ProEt.topology Y) (proEtaleConstantRing Y A) SY) :
    Nonempty (SX.tensor ⋙ (sfConstantModulePullback f A).mapDerivedCategory ≅
      ((sfConstantModulePullback f A).mapDerivedCategory.prod
        (sfConstantModulePullback f A).mapDerivedCategory) ⋙ SY.tensor) := by
  exact ⟨proEtaleCanonicalTensorComparison f
    (proEtaleConstantRing X A) (proEtaleConstantRing Y A)
    (sfConstantCoefficientIso f A)
    (intrinsicTensorModel X A SX TX) (intrinsicTensorModel Y A SY TY)⟩

private theorem openUnit
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openSheafAdjunction A j).unit := by
  have : (sfIntrinsicExtensionByZero j A).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j A).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  exact (openSheafAdjunction A j).unit_isIso_of_L_fully_faithful

/- The two projection maps are the explicit mates of the tensor-pullback comparison.
After restriction, their mate identities reduce invertibility to the closed counit or
open unit; the other restriction sees zero objects on both sides. -/
namespace ClosedProjectionFormal
private noncomputable def projection
    {D : Type d} [Category.{v} D] {E : Type e} [Category.{w} E]
    (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (L : D ⥤ E) (R : E ⥤ D) (a : L ⊣ R)
    (μ : TD ⋙ L ≅ (L.prod L) ⋙ TE) :
    ((𝟭 D).prod R) ⋙ TD ⟶ (L.prod (𝟭 E)) ⋙ TE ⋙ R where
  app Z := a.unit.app (TD.obj (Z.1, R.obj Z.2)) ≫
    R.map (μ.hom.app (Z.1, R.obj Z.2) ≫
      TE.map (Prod.mkHom (𝟙 (L.obj Z.1)) (a.counit.app Z.2)))
  naturality {Z Z'} f := by
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map]
    rw [← Category.assoc, ← a.unit_naturality (TD.map
      (Prod.mkHom f.1 (R.map f.2))), Category.assoc]
    simp only [Category.assoc, ← R.map_comp]
    congr 1
    have hm := μ.hom.naturality (Prod.mkHom f.1 (R.map f.2))
    dsimp only [Functor.comp_map, Functor.prod_map] at hm
    rw [← Category.assoc, hm]
    rw [Category.assoc, ← TE.map_comp, ← TE.map_comp]
    congr 3
    ext
    · simp
    · simp

private noncomputable def projectionIso
    {D : Type d} [Category.{v} D] {E : Type e} [Category.{w} E]
    {V : Type*} [Category* V] [HasZeroMorphisms V]
    (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (L : D ⥤ E) (R : E ⥤ D) (a : L ⊣ R)
    (μ : TD ⋙ L ≅ (L.prod L) ⋙ TE)
    (J : D ⥤ V)
    (hc : ∀ P, IsIso (a.counit.app P))
    (hj : ∀ {P Q : D} (f : P ⟶ Q), IsIso (L.map f) → IsIso (J.map f) → IsIso f)
    (hs : ∀ Q P, IsZero (J.obj (TD.obj (Q, R.obj P))))
    (ht : ∀ Q P, IsZero (J.obj (R.obj (TE.obj (L.obj Q, P))))) :
    (L.prod (𝟭 E)) ⋙ TE ⋙ R ≅ ((𝟭 D).prod R) ⋙ TD := by
  let π := projection TD TE L R a μ
  have hc' : IsIso a.counit := by
    let := hc
    exact NatIso.isIso_of_isIso_app _
  have hi (Z : D × E) : IsIso (L.map (π.app Z)) := by
    have h : L.map (π.app Z) ≫ a.counit.app (TE.obj (L.obj Z.1, Z.2)) =
        μ.hom.app (Z.1, R.obj Z.2) ≫
          TE.map (Prod.mkHom (𝟙 (L.obj Z.1)) (a.counit.app Z.2)) := by
      exact (a.homEquiv _ _).symm_apply_apply _
    have : IsIso (a.counit.app Z.2) := hc _
    have : IsIso (TE.map (Prod.mkHom (𝟙 (L.obj Z.1)) (a.counit.app Z.2))) :=
      by
      let : IsIso (Prod.mkHom (𝟙 (L.obj Z.1)) (a.counit.app Z.2)) :=
        (Iso.prod (Iso.refl (L.obj Z.1)) (asIso (a.counit.app Z.2))).isIso_hom
      infer_instance
    have : IsIso (L.map (π.app Z) ≫
        a.counit.app (TE.obj (L.obj Z.1, Z.2))) := by rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _ (a.counit.app (TE.obj (L.obj Z.1, Z.2)))
  have hiso (Z : D × E) : IsIso (π.app Z) :=
    hj (π.app Z) (hi Z) ((hs Z.1 Z.2).isIso (ht Z.1 Z.2) (J.map (π.app Z)))
  let := hiso
  have : IsIso π := NatIso.isIso_of_isIso_app π
  exact (asIso π).symm
end ClosedProjectionFormal

namespace OpenProjectionFormal
open CategoryTheory.Functor
private noncomputable def projection
    {D : Type d} [Category.{v} D] {E : Type e} [Category.{w} E]
    (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (L : D ⥤ E) (F : E ⥤ D) (a : F ⊣ L)
    (μ : TD ⋙ L ≅ (L.prod L) ⋙ TE) :
    (L.prod (𝟭 E)) ⋙ TE ⋙ F ⟶ ((𝟭 D).prod F) ⋙ TD := by
  let t : (L.prod (𝟭 E)) ⋙ TE ⟶ ((𝟭 D).prod F) ⋙ TD ⋙ L :=
    whiskerRight (NatTrans.prod (𝟙 L) a.unit) TE ≫
      whiskerLeft ((𝟭 D).prod F) μ.inv
  exact whiskerRight t F ≫ whiskerLeft (((𝟭 D).prod F) ⋙ TD) a.counit

private noncomputable def projectionIso
    {D : Type d} [Category.{v} D] {E : Type e} [Category.{w} E]
    {V : Type*} [Category* V] [HasZeroMorphisms V]
    (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (L : D ⥤ E) (F : E ⥤ D) (a : F ⊣ L)
    (μ : TD ⋙ L ≅ (L.prod L) ⋙ TE)
    (J : D ⥤ V)
    (hc : ∀ P, IsIso (a.unit.app P))
    (hj : ∀ {P Q : D} (f : P ⟶ Q), IsIso (L.map f) → IsIso (J.map f) → IsIso f)
    (hs : ∀ Q P, IsZero (J.obj (TD.obj (Q, F.obj P))))
    (ht : ∀ Q P, IsZero (J.obj (F.obj (TE.obj (L.obj Q, P))))) :
    (L.prod (𝟭 E)) ⋙ TE ⋙ F ≅ ((𝟭 D).prod F) ⋙ TD := by
  let π := projection TD TE L F a μ
  have hc' : IsIso a.unit := by
    have := hc
    exact NatIso.isIso_of_isIso_app _
  have hi (Z : D × E) : IsIso (L.map (π.app Z)) := by
    have h : a.unit.app (TE.obj (L.obj Z.1, Z.2)) ≫ L.map (π.app Z) =
        TE.map (Prod.mkHom (𝟙 (L.obj Z.1)) (a.unit.app Z.2)) ≫
          μ.inv.app (Z.1, F.obj Z.2) := by
      exact (a.homEquiv _ _).apply_symm_apply _
    have : IsIso (Prod.mkHom (𝟙 (L.obj Z.1)) (a.unit.app Z.2)) :=
      (Iso.prod (Iso.refl (L.obj Z.1)) (asIso (a.unit.app Z.2))).isIso_hom
    have : IsIso (a.unit.app (TE.obj (L.obj Z.1, Z.2)) ≫ L.map (π.app Z)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (a.unit.app (TE.obj (L.obj Z.1, Z.2))) _
  have hiso (Z : D × E) : IsIso (π.app Z) :=
    hj (π.app Z) (hi Z) ((ht Z.1 Z.2).isIso (hs Z.1 Z.2) (J.map (π.app Z)))
  have : IsIso π := NatIso.isIso_of_isIso_app π
  exact asIso π
end OpenProjectionFormal

/- Disjointness in the opposite order follows formally from the two adjunctions.
Tensor preserves zero objects because tensoring is a left adjoint. -/
private theorem supportProjectionPair
    {D E C : Type*} [Category* D] [Category* E] [Category* C]
    [HasZeroMorphisms D] [HasZeroMorphisms E] [HasZeroMorphisms C]
    {HD : Dᵒᵖ × D ⥤ D} {HE : Eᵒᵖ × E ⥤ E} {HC : Cᵒᵖ × C ⥤ C}
    (SD : CoefficientClosedStructure HD) (SE : CoefficientClosedStructure HE)
    (SC : CoefficientClosedStructure HC)
    (bE : @SymmetricCategory E _ SE.monoidal)
    (bC : @SymmetricCategory C _ SC.monoidal)
    (L : D ⥤ E) (R : E ⥤ D) (F : C ⥤ D) (J : D ⥤ C)
    (ai : L ⊣ R) (aj : F ⊣ J)
    (μi : SD.tensor ⋙ L ≅ (L.prod L) ⋙ SE.tensor)
    (μj : SD.tensor ⋙ J ≅ (J.prod J) ⋙ SC.tensor)
    (hc : ∀ P, IsIso (ai.counit.app P)) (hu : ∀ P, IsIso (aj.unit.app P))
    (hj : ∀ {P Q : D} (f : P ⟶ Q), IsIso (L.map f) → IsIso (J.map f) → IsIso f)
    (hz : ∀ P, IsZero (J.obj (R.obj P))) :
    Nonempty ((L.prod (𝟭 E)) ⋙ SE.tensor ⋙ R ≅ ((𝟭 D).prod R) ⋙ SD.tensor) ∧
    Nonempty ((J.prod (𝟭 C)) ⋙ SC.tensor ⋙ F ≅ ((𝟭 D).prod F) ⋙ SD.tensor) := by
  have hLF (P : C) : IsZero (L.obj (F.obj P)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (ai.homEquiv _ _).injective
    apply (aj.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  constructor
  · exact ⟨ClosedProjectionFormal.projectionIso SD.tensor SE.tensor L R ai μi J hc hj
      (fun Q P ↦ (tensorZeroRight SC bC _ _ (hz P)).of_iso (μj.app (Q, R.obj P)))
      (fun Q P ↦ hz _)⟩
  · exact ⟨OpenProjectionFormal.projectionIso SD.tensor SC.tensor J F aj μj L hu
      (fun f hJ hL ↦ hj f hL hJ)
      (fun Q P ↦ (tensorZeroRight SE bE _ _ (hLF P)).of_iso (μi.app (Q, F.obj P)))
      (fun Q P ↦ hLF _)⟩

private abbrev IntrinsicClosed (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  CoefficientClosedStructure (derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology X) (proEtaleConstantRing X A))

private abbrev IntrinsicTensor (X : Scheme.{u}) (A : Type u) [CommRing A]
    (S : IntrinsicClosed X A) :=
  CoefficientTensorModels.{u, u + 1, u, u + 2}
    (ProEt.topology X) (proEtaleConstantRing X A) S

private noncomputable def deriveExactAdjunction
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory := by
  letI : CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) _ _

/- Apply the abstract support calculation to exact sheaf functors and their derived
functors. Full faithfulness derives by localizing the sheaf unit/counit isomorphisms. -/
private theorem intrinsicSupportProjectionPair
    (A : Type u) [CommRing A] [Finite A]
    {Z U X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hc : Set.range j = (Set.range i)ᶜ)
    (SX : IntrinsicClosed X A) (SZ : IntrinsicClosed Z A) (SU : IntrinsicClosed U A)
    (TX : IntrinsicTensor X A SX) (TZ : IntrinsicTensor Z A SZ)
    (TU : IntrinsicTensor U A SU)
    (bZ : @SymmetricCategory (proEtaleDerivedCategory Z A) _ SZ.monoidal)
    (bU : @SymmetricCategory (proEtaleDerivedCategory U A) _ SU.monoidal) :
    Nonempty (((sfConstantModulePullback i A).mapDerivedCategory.prod (𝟭 _)) ⋙
      SZ.tensor ⋙ (sfConstantModuleDirectImage i A).rightDerivedFunctor ≅
      ((𝟭 _).prod (sfConstantModuleDirectImage i A).rightDerivedFunctor) ⋙ SX.tensor) ∧
    Nonempty (((sfConstantModulePullback j A).mapDerivedCategory.prod (𝟭 _)) ⋙
      SU.tensor ⋙ (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      ((𝟭 _).prod (sfIntrinsicExtensionByZero j A).mapDerivedCategory) ⋙ SX.tensor) := by
  have : PreservesFiniteColimits (sfConstantModuleDirectImage i A) :=
    (sfIntrinsicClosedAmbientAdjunction A i j (compl_eq_iff_isCompl.mp hc.symm)).1
  have : PreservesLimitsOfSize.{0, 0} (sfConstantModuleDirectImage i A) :=
    (sfConstantModuleAdjunction i A).rightAdjoint_preservesLimits
  have := closedCounit A i j hc
  have := openUnit A j
  let ai := deriveExactAdjunction (sfConstantModuleAdjunction i A)
  let aj := deriveExactAdjunction (openSheafAdjunction A j)
  let fi := ai.fullyFaithfulROfCompIsoId
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (sfConstantModuleAdjunction i A).counit) ≪≫
        Functor.mapDerivedCategoryIdIso _)
  have := fi.full
  have := fi.faithful
  have : IsIso ai.counit := ai.counit_isIso_of_R_fully_faithful
  let fj := aj.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (openSheafAdjunction A j).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _)
  have := fj.full
  have := fj.faithful
  have : IsIso aj.unit := aj.unit_isIso_of_L_fully_faithful
  obtain ⟨μi⟩ := tensorPullback A i SX SZ TX TZ
  obtain ⟨μj⟩ := tensorPullback A j SX SU TX TU
  have hJoint {P Q : proEtaleDerivedCategory X A} (f : P ⟶ Q)
      (hi : IsIso ((sfConstantModulePullback i A).mapDerivedCategory.map f))
      (hj : IsIso ((sfConstantModulePullback j A).mapDerivedCategory.map f)) : IsIso f :=
    jointDerivedIso (sfConstantModulePullback i A)
    (sfConstantModulePullback j A) (fun P hi hj ↦
      proEtaleRingModule_isZero_of_open_closed i j hc
        (proEtaleConstantRing X A) (proEtaleConstantRing Z A) (proEtaleConstantRing U A)
        (sfConstantCoefficientIso i A) (sfConstantCoefficientIso j A) P hj hi) f hi hj
  have hp := supportProjectionPair SX SZ SU bZ bU _ _ _ _ ai aj μi μj
    (fun P ↦ inferInstance) (fun P ↦ inferInstance) hJoint
    (derivedCompositeZero _ _ (closedOpenZero A i j hc))
  obtain ⟨c⟩ := hp.1
  let e := (sfConstantModuleDirectImage i A).rightDerivedFunctorIsoMapDerivedCategory
  exact ⟨⟨Functor.isoWhiskerLeft
      (((sfConstantModulePullback i A).mapDerivedCategory.prod (𝟭 _)) ⋙ SZ.tensor) e ≪≫
    c ≪≫ Functor.isoWhiskerRight (NatIso.prod (Iso.refl _) e.symm) SX.tensor⟩, hp.2⟩

private theorem intrinsicClosedProjection
    (A : Type u) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} [IsNoetherian X]
    (i : Y ⟶ X) [IsClosedImmersion i]
    (SX : IntrinsicClosed X A) (SY : IntrinsicClosed Y A)
    (TX : IntrinsicTensor X A SX) (TY : IntrinsicTensor Y A SY)
    (bY : @SymmetricCategory (proEtaleDerivedCategory Y A) _ SY.monoidal) :
    Nonempty (((sfConstantModulePullback i A).mapDerivedCategory.prod (𝟭 _)) ⋙
      SY.tensor ⋙ (sfConstantModuleDirectImage i A).rightDerivedFunctor ≅
      ((𝟭 _).prod (sfConstantModuleDirectImage i A).rightDerivedFunctor) ⋙ SX.tensor) := by
  let V : X.Opens := ⟨(Set.range i)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hc : Set.range V.ι = (Set.range i)ᶜ := Scheme.Opens.range_ι V
  obtain ⟨SV, TV, bV, _⟩ := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology V) (proEtaleConstantRing V A)
  exact (intrinsicSupportProjectionPair A i V.ι hc SX SY SV TX TY TV bY bV).1

private theorem intrinsicOpenProjection
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j]
    (SX : IntrinsicClosed X A) (SU : IntrinsicClosed U A)
    (TX : IntrinsicTensor X A SX) (TU : IntrinsicTensor U A SU)
    (bU : @SymmetricCategory (proEtaleDerivedCategory U A) _ SU.monoidal) :
    Nonempty (((sfConstantModulePullback j A).mapDerivedCategory.prod (𝟭 _)) ⋙
      SU.tensor ⋙ (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      ((𝟭 _).prod (sfIntrinsicExtensionByZero j A).mapDerivedCategory) ⋙ SX.tensor) := by
  let Z : TopologicalSpace.Closeds X :=
    ⟨(Set.range j)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hc : Set.range j = (Set.range I.subschemeι)ᶜ := by
    simp only [Scheme.IdealSheafData.range_subschemeι, I,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Z]
    exact (compl_compl (Set.range j)).symm
  obtain ⟨SZ, TZ, bZ, _⟩ := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology I.subscheme) (proEtaleConstantRing I.subscheme A)
  exact (intrinsicSupportProjectionPair A I.subschemeι j hc SX SZ SU TX TZ TU bZ bU).2

open CategoryTheory.MonoidalCategory
private def closedParametrized {D : Type a} [Category.{b} D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H) :
    letI := S.monoidal
    (curriedTensor D).flip ⊣₂ Functor.curry.obj H := by
  letI := S.monoidal
  refine ParametrizedAdjunction.mk' S.adjunction ?_
  intro P P' f X Y g
  change (S.adjunction P).homEquiv X Y (X ◁ f ≫ g) =
    (S.adjunction P').homEquiv X Y g ≫ H.map (Prod.mkHom f.op (𝟙 Y))
  apply ((S.adjunction P).homEquiv X Y).symm.injective
  rw [Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]
  rw [S.evaluation_naturality P' P Y f]
  rw [← Category.assoc]
  have hn := ((curriedTensor D).map ((S.adjunction P').homEquiv X Y g)).naturality f
  change X ◁ f ≫ ((S.adjunction P').homEquiv X Y g) ▷ P' =
    ((S.adjunction P').homEquiv X Y g) ▷ P ≫ H.obj (op P', Y) ◁ f at hn
  change X ◁ f ≫ g =
    (((S.adjunction P').homEquiv X Y g) ▷ P ≫ H.obj (op P', Y) ◁ f) ≫ _
  rw [← hn, Category.assoc]
  congr 1
  exact ((S.adjunction P').homEquiv X Y).symm_apply_apply g |>.symm
/- Parametrized conjugate isomorphisms implement the blueprint Yoneda calculation
with naturality in both internal-Hom variables already built in. -/
private theorem ambientHomOfProjection
    {D : Type a} [Category.{b} D] {E : Type a'} [Category.{b'} E]
    {HD : Dᵒᵖ × D ⥤ D} {HE : Eᵒᵖ × E ⥤ E}
    (SD : CoefficientClosedStructure HD) (SE : CoefficientClosedStructure HE)
    (L : D ⥤ E) (R F : E ⥤ D) (G : D ⥤ E)
    (a : L ⊣ R) (b : F ⊣ G)
    (p : (L.prod (𝟭 E)) ⋙ SE.tensor ⋙ F ≅
      ((𝟭 D).prod F) ⋙ SD.tensor) :
    Nonempty ((F.op.prod (𝟭 D)) ⋙ HD ≅
      ((𝟭 Eᵒᵖ).prod G) ⋙ HE ⋙ R) := by
  let := SD.monoidal
  let := SE.monoidal
  let ad := (closedParametrized SD).precomp F
  let ae := (closedParametrized SE).comp a b
  let e : (curriedTensor E).flip ⋙ (Functor.whiskeringLeft _ _ _).obj L ⋙
      (Functor.whiskeringRight _ _ _).obj F ≅ F ⋙ (curriedTensor D).flip :=
    NatIso.ofComponents
    (fun (P : E) ↦ NatIso.ofComponents (fun (Q : D) ↦ p.app (Q, P))
      (fun {Q Q'} f ↦ by
        simpa [CoefficientClosedStructure.tensor, MonoidalCategory.tensorHom_def] using
          p.hom.naturality (Prod.mkHom f (𝟙 P)))) (fun {P P'} f ↦ by
          ext Q
          simpa [CoefficientClosedStructure.tensor, MonoidalCategory.tensorHom_def] using
            p.hom.naturality (Prod.mkHom (𝟙 Q) f))
  let t := Functor.uncurry.mapIso (ad.conjugateIso ae e)
  refine ⟨NatIso.ofComponents (fun Z ↦ t.app Z) ?_⟩
  intro Z Z' f
  have h := t.hom.naturality f
  change (HD.map (Prod.mkHom (F.op.map f.1) (𝟙 _)) ≫
      HD.map (Prod.mkHom (𝟙 _) f.2)) ≫ t.hom.app Z' =
    t.hom.app Z ≫ (R.map (HE.map (Prod.mkHom f.1 (𝟙 _))) ≫
      R.map (HE.map (Prod.mkHom (𝟙 _) (G.map f.2)))) at h
  simpa only [Functor.comp_map, Functor.prod_map, Functor.id_map,
    ← HD.map_comp, ← HE.map_comp, ← R.map_comp, prod_comp,
    Category.id_comp, Category.comp_id, Iso.app_hom] using h


private noncomputable def starAdjunction {S X : Scheme.{u}} (s : S ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    (sfConstantModulePullback s A).mapDerivedCategory ⊣
      (sfConstantModuleDirectImage s A).rightDerivedFunctor :=
  (sfConstantModuleAdjunction s A).mapDerivedCategoryRightDerivedAdjunction

private def compositeProjection
    {D : Type a} [Category.{b} D] {E : Type a'} [Category.{b'} E]
    {C : Type a''} [Category.{b''} C]
    (TD : D × D ⥤ D) (TE : E × E ⥤ E) (TC : C × C ⥤ C)
    (L : D ⥤ E) (M : E ⥤ C) (I : C ⥤ E) (J : E ⥤ D)
    (c : (M.prod (𝟭 C)) ⋙ TC ⋙ I ≅ ((𝟭 E).prod I) ⋙ TE)
    (o : (L.prod (𝟭 E)) ⋙ TE ⋙ J ≅ ((𝟭 D).prod J) ⋙ TD) :
    ((L ⋙ M).prod (𝟭 C)) ⋙ TC ⋙ (I ⋙ J) ≅
      ((𝟭 D).prod (I ⋙ J)) ⋙ TD :=
  NatIso.ofComponents (fun Z ↦ J.mapIso (c.app (L.obj Z.1, Z.2)) ≪≫
    o.app (Z.1, I.obj Z.2)) (by
      intro Z Z' f
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map,
        Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
      rw [← Category.assoc, ← J.map_comp]
      have hc := c.hom.naturality (Prod.mkHom (L.map f.1) f.2)
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hc
      rw [hc]
      rw [J.map_comp, Category.assoc]
      have ho := o.hom.naturality (Prod.mkHom f.1 (I.map f.2))
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at ho
      rw [ho]
      simp only [Category.assoc])

private theorem assembly (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsNoetherian X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (SX : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u}
        (ProEt.topology X) (proEtaleConstantRing X A)))
    (SS : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u}
        (ProEt.topology S) (proEtaleConstantRing S A)))
    (p : ((sfConstantModulePullback (i ≫ j) A).mapDerivedCategory.prod
        (𝟭 (proEtaleDerivedCategory S A))) ⋙ SS.tensor ⋙
          ((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
            (sfIntrinsicExtensionByZero j A).mapDerivedCategory) ≅
      ((𝟭 (proEtaleDerivedCategory X A)).prod
        ((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory)) ⋙ SX.tensor) :
    Nonempty
      ((((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory).op.prod
          (𝟭 (proEtaleDerivedCategory X A))) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology X) (proEtaleConstantRing X A) ≅
        ((𝟭 (proEtaleDerivedCategory S A)ᵒᵖ).prod
          ((sfConstantModulePullback j A).mapDerivedCategory ⋙
            (sfIntrinsicClosedUpperShriek i
              (Scheme.Opens.ι (X := U) (⟨(Set.range i)ᶜ,
                (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩ :
                  U.Opens)) A).rightDerivedFunctor)) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology S) (proEtaleConstantRing S A) ⋙
            (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor) := by
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : IsNoetherian U := ⟨⟩
  let V : U.Opens := ⟨(Set.range i)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hc : IsCompl (Set.range i) (Set.range V.ι) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  obtain ⟨_, ⟨ai⟩⟩ := sfIntrinsicClosedAmbientAdjunction A i V.ι hc
  exact ambientHomOfProjection SX SS _ _ _ _ (starAdjunction (i ≫ j) A)
    (ai.comp (openAdjunction j A)) p

private theorem assembled (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsNoetherian X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty
      ((((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory).op.prod
          (𝟭 (proEtaleDerivedCategory X A))) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology X) (proEtaleConstantRing X A) ≅
        ((𝟭 (proEtaleDerivedCategory S A)ᵒᵖ).prod
          ((sfConstantModulePullback j A).mapDerivedCategory ⋙
            (sfIntrinsicClosedUpperShriek i
              (Scheme.Opens.ι (X := U) (⟨(Set.range i)ᶜ,
                (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩ :
                  U.Opens)) A).rightDerivedFunctor)) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology S) (proEtaleConstantRing S A) ⋙
            (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor) := by
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : IsNoetherian U := ⟨⟩
  obtain ⟨SX, TX, _, _⟩ := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology X) (proEtaleConstantRing X A)
  obtain ⟨SU, TU, bU, _⟩ := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology U) (proEtaleConstantRing U A)
  obtain ⟨SS, TS, bS, _⟩ := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology S) (proEtaleConstantRing S A)
  obtain ⟨c⟩ := intrinsicClosedProjection A i SU SS TU TS bS
  obtain ⟨o⟩ := intrinsicOpenProjection A j SX SU TX TU bU
  let p := compositeProjection SX.tensor SU.tensor SS.tensor
    (sfConstantModulePullback j A).mapDerivedCategory
    (sfConstantModulePullback i A).mapDerivedCategory
    (sfConstantModuleDirectImage i A).rightDerivedFunctor
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory c o
  obtain ⟨e, _, _⟩ := proEtaleConstantRingModulePullbackComposition i j A
  let e' : (sfConstantModulePullback (i ≫ j) A).mapDerivedCategory ≅
      (sfConstantModulePullback j A).mapDerivedCategory ⋙
        (sfConstantModulePullback i A).mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso _ _
  let p' := Functor.isoWhiskerRight (NatIso.prod e' (Iso.refl _))
    (SS.tensor ⋙ ((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
      (sfIntrinsicExtensionByZero j A).mapDerivedCategory)) ≪≫ p
  exact assembly A i j SX SS p'


namespace AlgebraicGeometry

open Scheme

/-- The etale ambient stratum identity, natural contravariantly in P and covariantly in M.
Source: Weil blueprint, order 2069 (blueprint: lem-weil-stratum-ambient-hom).

Proof: derive the exact open extension/restriction adjunction and compose with the ambient
closed adjunction. The open projection formula follows by resolving the target tensor
factor by a K-flat complex with flat terms, applying the sheaf projection formula degreewise,
and commuting extension by zero with the total-complex sums. The closed projection formula
is checked by closed and complementary-open restriction: the former is an isomorphism by
the closed counit, and both sides vanish on the latter. These restrictions jointly detect
acyclic complexes. Compose the two projection formulas. Resolve internal Hom's second
argument by a K-injective and its first by a K-flat complex; Hom-complex currying and H^0
of derived global sections give tensor-Hom adjunction. For every test complex Q, tensor-Hom,
the projection formula, shriek adjunction, tensor-Hom on S, and ordinary pullback/direct-image
adjunction identify Hom(Q,RHom(Rs! P,M)) with Hom(Q,Rs* RHom(P,Rs^! M)). All bijections are
natural in Q,P,M. Evaluate this bijection and its inverse on identities to obtain mutually
inverse arrows. Naturality in P,M gives the bifunctor isomorphism. No finite-amplitude,
constructibility, or boundedness condition occurs.

Complete DAG proof plan:
1. Use the chosen closed-then-open factorization $s=ji$. In the pro-etale case, $U$ is Noetherian
by [lem-weil-pbc-noetherian-open-subscheme-noetherian]. Apply the same statement to the open
complement $V=U\setminus i(S)$ and to its intersections with affine opens of $U$: all are
quasi-compact. Thus $v:V\hookrightarrow U$ is a quasi-compact morphism. This verifies the
hypotheses of the pro-etale closed-localization and closed-support statements used below. No such
hypothesis is needed on the etale side. The Noetherian assumption restores the scheme context of
the enclosing unit; the imported standalone node did not state it. Dependencies:
lem-weil-pbc-noetherian-open-subscheme-noetherian.

2. The etale closed direct image $i_*$ is exact: at points of $i(S)$ its stalk is the
corresponding stalk on $S$ by [lemma-openclosed-stalk-lowerstar]; outside $i(S)$ it is zero, since
a neighbourhood disjoint from $i(S)$ has empty pullback. Exactness of geometric stalks and their
conservativity therefore check exactness of $i_*$ on every short exact sequence. The same
assertions hold for constant-coefficient modules by forgetting the module action. Its
inverse-image counit is an isomorphism by [lem-kun-04ca]. In the pro-etale case
[lem-weil-pbc-proetale-ringed-open-closed], applied on $U$ with the quasi-compact complement from
step 1, directly gives exactness, the closed counit isomorphism, and $v^{-1}i_*=0$. Consequently
$Ri_*=i_*$, computed termwise, in both cases. Moreover $i^{-1}$ and $v^{-1}$ detect zero sheaves:
in the etale case a sheaf zero on $V$ is supported on $i(S)$ and [lem-kun-04ca] identifies it with
$i_*G$, so its inverse image on $S$ is $G$; in the pro-etale case the short exact localization
sequence of [lem-weil-pbc-proetale-ringed-open-closed] proves this directly. Since both inverse
images are exact, they also jointly detect acyclic complexes, by applying this argument to each
cohomology sheaf. Dependencies: lemma-openclosed-stalk-lowerstar,
prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative, lem-kun-04ca,
lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-site-pullback-abelian-exact.

3. For any of the scheme maps in this argument, inverse image with constant coefficients is exact:
its underlying abelian functor is the exact site inverse image, and the inverse image of the
constant ring is the same constant ring. The module adjunction is
[lem-weil-pbc-ringed-topoi-module-adjunction]. It derives on the whole unbounded categories as
follows. Choose a K-injective resolution $N\to I$ on the source site using
[prop-pur-kinjective-resolutions-exist]. The direct image of $I$ is K-injective by
[lem-weil-pbc-right-adjoint-preserves-kinjective], since inverse image is exact. The
homotopy-category adjunction [lem-weil-pbc-termwise-adjunction-homotopy] and
[lem-weil-pbc-kinjective-hom-derived] then give
$$\operatorname{Hom}(t^{-1}Q,N)=\operatorname{Hom}_{K}(t^{-1}Q,I)=\operatorname{Hom}_{K}(Q,t_*I)=
\operatorname{Hom}(Q,Rt_*N).$$
Here any representative of $Q$ can be used. Thus $t^{-1}\dashv Rt_*$. The total derived functor
used here exists by [lem-weil-pbc-kinjective-total-derived]. The same K-injective calculation
derives $j_!\dashv j^{-1}$ from the etale sheaf adjunction and exactness
[lem-weil-pbc-extension-by-zero-adjunction, lem-weil-pbc-extension-by-zero-exact], or from the
pro-etale exact adjunction [lem-cbc-proetale-extension-zero]; for this calculation $j^{-1}I$ is
K-injective because $j_!$ is exact. All these bijections are natural. Composing this open
adjunction with the ambient closed adjunction of [lem-exc-closed-ambient] or
[lem-exc-proetale-closed-support] gives $Rs_!=j_!i_*\dashv Ri^!j^{-1}=Rs^!$. Dependencies:
lem-weil-pbc-site-pullback-abelian-exact, lem-weil-pbc-ringed-topoi-module-adjunction,
prop-pur-kinjective-resolutions-exist, lem-weil-pbc-right-adjoint-preserves-kinjective,
lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-kinjective-hom-derived,
lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-extension-by-zero-adjunction,
lem-weil-pbc-extension-by-zero-exact, lem-cbc-proetale-extension-zero, lem-exc-closed-ambient,
lem-exc-proetale-closed-support.

4. Inverse image on each of these constant-coefficient ringed sites has a canonical derived tensor
comparison $$t^{-1}(Q\otimes_A^LQ')\cong t^{-1}Q\otimes_A^Lt^{-1}Q'$$ by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. The same cited statement says that pullback
of a K-flat complex with flat terms is K-flat with flat terms. We will use both assertions for
$i$, $j$, and the complementary $v$. The constant-coefficient pullback is termwise inverse image
because it is exact; no finite Tor-amplitude condition on $Q,Q'$ occurs in this result. We will
also use the following direct consequence of K-flatness [def-pc-kflat-complex]: if one tensor
factor is K-flat, the other may be represented by an arbitrary complex. Indeed, replace that other
complex by a K-flat resolution; the cone of its resolution map is acyclic, and tensoring this cone
with the fixed K-flat factor is acyclic by the definition. Thus the induced map of total tensor
complexes is a quasi-isomorphism. This justifies the arbitrary first-factor representatives in
steps 5 and 8. Dependencies: lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
def-pc-kflat-complex.

5. First establish the open projection formula on both sites. An open immersion is an etale site
object by [lem-weil-pbc-open-immersion-etale], and inverse image there is restriction by
[lem-weil-pbc-etale-inverse-image-restriction]. For the pro-etale site use the localization
identification [lem-weil-proetale-weakly-etale-localization]. The ringed-slice formula
[lem-weil-pbc-ringed-slice-extension-tensor] therefore gives, for module sheaves, $j_!(F\otimes
j^{-1}G)\cong j_!F\otimes G$. Choose a K-flat resolution with flat terms $Q_0\to Q$ on $X$ using
[lem-pc-kflat-resolution]. By step 4, $j^{-1}Q_0$ is K-flat. Use any complex representing $P'$ on
$U$. In each total degree the sheaf formula identifies the summands of $j_!(P'\otimes j^{-1}Q_0)$
with those of $j_!P'\otimes Q_0$, and it commutes with both differentials by naturality. Extension
by zero commutes with their direct sums: the coproduct comparison follows directly from its
adjunction, since maps from either candidate to $N$ are families of maps from the summands to
$j^{-1}N$. Hence it identifies the total complexes. Exactness of $j_!$ from step 3 and the derived
tensor construction [lem-weil-pbc-site-derived-tensor-descent] give a natural isomorphism
$$j_!P'\otimes_A^L Q\cong j_!(P'\otimes_A^Lj^{-1}Q).$$ The pro-etale assertion is also exactly
[lem-cbc-extension-zero-projection-formula]. Dependencies: lem-weil-pbc-open-immersion-etale,
lem-weil-pbc-etale-inverse-image-restriction, lem-weil-proetale-weakly-etale-localization,
lem-weil-pbc-ringed-slice-extension-tensor, lem-pc-kflat-resolution,
lem-weil-pbc-site-derived-tensor-descent, lem-cbc-extension-zero-projection-formula.

6. Next establish the closed projection formula without using geometric stalks on the pro-etale
site. Form $$c:i_*P\otimes_A^LQ'\longrightarrow i_*(P\otimes_A^Li^{-1}Q')$$ as the adjoint under
$i^{-1}\dashv Ri_*=i_*$ of $$i^{-1}(i_*P\otimes_A^LQ')\cong
i^{-1}i_*P\otimes_A^Li^{-1}Q'\xrightarrow{\varepsilon_P\otimes1}P\otimes_A^Li^{-1}Q'.$$ The
comparison in step 4 and the closed counit isomorphism in step 2 identify $i^{-1}c$ with an
isomorphism. Both sides have zero restriction to $V$: for the source use $v^{-1}i_*P=0$ and the
tensor comparison, and for the target use $v^{-1}i_*=0$. The cone of $c$ therefore has zero
inverse images on $S$ and $V$, so it is acyclic by the joint detection on complexes proved in step
2. Thus $c$ is an isomorphism. This proves $i_*P\otimes_A^LQ'\cong i_*(P\otimes_A^Li^{-1}Q')$,
naturally in the two arbitrary complexes. The exactness and counit facts are precisely those of
[lem-kun-04ca] in the etale case and [lem-weil-pbc-proetale-ringed-open-closed] in the pro-etale
case; the tensor assertion is [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Dependencies:
lem-kun-04ca, lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

7. Compose the open and closed formulas of steps 5 and 6, with $P'=i_*P$ and $Q'=j^{-1}Q$, to
obtain $$Rs_!P\otimes_A^LQ=j_!i_*P\otimes_A^LQ\cong j_!(i_*P\otimes_A^Lj^{-1}Q)\cong
j_!i_*(P\otimes_A^Li^{-1}j^{-1}Q)=Rs_!(P\otimes_A^Ls^{-1}Q).$$ Here $s^{-1}=i^{-1}j^{-1}$: the
composite is left adjoint to the composite sheaf direct image $j_*i_*=s_*$, so identifies with
inverse image, including its unit and counit. On K-injectives, $Ri_*=i_*$ preserves K-injectives
by the exact inverse-image adjunction and [lem-weil-pbc-right-adjoint-preserves-kinjective]. Thus
$Rj_*Ri_*=Rs_*$ as well: on a K-injective $I$ the two constructions both give $j_*i_*I=s_*I$. All
comparisons in the displayed projection formula are natural. Dependencies:
lem-weil-pbc-right-adjoint-preserves-kinjective.

8. Derive the tensor-internal-Hom bijection on either ringed site, rather than taking it from a
definition of the operations. For arbitrary $K,L,N$, choose a K-flat representative $L_0$ of $L$
and a K-injective representative $I$ of $N$. The Hom complex $\mathcal Hom^\bullet(L_0,I)$ is
K-injective by [lem-pur-hom-kflat-into-kinjective]. For any representative $K_0$,
[lem-sc-derived-hom-tensor-total] gives $$\mathcal Hom^\bullet(K_0,\mathcal
Hom^\bullet(L_0,I))\cong\mathcal Hom^\bullet(\operatorname{Tot}(K_0\otimes L_0),I).$$ The two
sides represent $R\mathcal Hom(K,R\mathcal Hom(L,N))$ and $R\mathcal Hom(K\otimes_A^LL,N)$. Taking
$H^0$ of derived global sections and using [lem-pur-rhom-global-sections] on each side gives
$$\operatorname{Hom}(K,R\mathcal Hom(L,N))\cong\operatorname{Hom}(K\otimes_A^LL,N),$$ natural in
all three derived objects. Existence of $L_0$ and $I$ is [lem-pc-kflat-resolution,
prop-pur-kinjective-resolutions-exist]; the models and their descent are
[def-pur-derived-internal-hom, lem-weil-pbc-site-derived-tensor-descent]. Symmetry used to resolve
the second tensor variable is induced by the symmetric sheaf tensor
[lem-pc-sheaf-modules-tensor-closed]; swapping the degree-$p,q$ summands with sign $(-1)^{pq}$
commutes with the total differential and squares to the identity, hence gives the corresponding
derived symmetry. Dependencies: lem-pur-hom-kflat-into-kinjective,
lem-sc-derived-hom-tensor-total, lem-pur-rhom-global-sections, lem-pc-kflat-resolution,
prop-pur-kinjective-resolutions-exist, def-pur-derived-internal-hom,
lem-weil-pbc-site-derived-tensor-descent, lem-pc-sheaf-modules-tensor-closed.

9. For every $Q\in D_\tau(X,A)$, apply step 8, the projection formula of step 7 (with tensor
symmetry), the shriek adjunction of step 3, step 8 on $S$, and the star adjunction of step 3, in
that order: $$\begin{aligned} \operatorname{Hom}_X(Q,R\mathcal Hom_X(Rs_!P,M))
&\cong\operatorname{Hom}_X(Q\otimes_A^LRs_!P,M)\\
&\cong\operatorname{Hom}_X(Rs_!(s^{-1}Q\otimes_A^LP),M)\\
&\cong\operatorname{Hom}_S(s^{-1}Q\otimes_A^LP,Rs^!M)\\
&\cong\operatorname{Hom}_S(s^{-1}Q,R\mathcal Hom_S(P,Rs^!M))\\
&\cong\operatorname{Hom}_X(Q,Rs_*R\mathcal Hom_S(P,Rs^!M)). \end{aligned}$$ Every object here
belongs to its ordinary ambient derived category, by the constructions already checked; none of
the bijections requires a constructible or perfect input. Their composite is natural in $Q$,
contravariantly in $P$, and covariantly in $M$. No additional dependencies.

10. Write $B=R\mathcal Hom_X(Rs_!P,M)$, $C=Rs_*R\mathcal Hom_S(P,Rs^!M)$, and
$\theta_Q:\operatorname{Hom}(Q,B)\cong\operatorname{Hom}(Q,C)$ for step 9. Set
$\alpha=\theta_B(1_B):B\to C$ and $\beta=\theta_C^{-1}(1_C):C\to B$. Naturality in $Q$ gives
$\theta_Q(f)=\alpha f$ and $\theta_Q^{-1}(g)=\beta g$; evaluating their inverse composites at the
identities gives $\beta\alpha=1_B$ and $\alpha\beta=1_C$. Thus $\alpha$ is the desired
isomorphism. Naturality of $\theta$ in $P,M$ gives naturality of $\alpha$. This writes out the
required representable-functor argument directly, without applying the scheme-specific Yoneda node
to a derived category. No additional dependencies. -/
theorem Etale.nonempty_stratumAmbientHomIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty
      ((Etale.immersionLowerShriek A i j).op.prod
          (𝟭 (Etale.DerivedCategoryModule A X)) ⋙
          Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1} A) X) ≅
        (𝟭 (Etale.DerivedCategoryModule A S)ᵒᵖ).prod (Etale.immersionUpperShriek A i j) ⋙
          Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1} A) S) ⋙
            (Etale.lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).rightDerivedFunctor) := by
  exact existsNonempty (Etale.immersionInternalHomIso A i j)

/-- The pro-etale ambient stratum identity on a Noetherian target.
Source: Weil blueprint, order 2069 (blueprint: lem-weil-stratum-ambient-hom).

Proof: U and its open complement to i(S) are Noetherian, so the complement is quasi-compact.
Use the pro-etale ringed open-closed localization sequence to get exactness of closed
pushforward, its invertible inverse-image counit, disjoint-support vanishing, and joint
acyclicity detection by closed and complementary-open restrictions. The ambient closed
adjunction is computed by the right derived functor of i* ker(N → v* v* N), and composes
with the exact open extension/restriction adjunction. Pullback preserves K-flat complexes
and derived tensor. Apply the ringed-slice projection formula to a K-flat representative
of the target tensor factor; extension by zero commutes with direct sums, hence with its
total tensor complex. Check the closed projection formula on the two restrictions using
the counit and disjoint-support vanishing, then compose the open and closed formulas.
K-injective resolutions compute ordinary direct image and its composition. Hom-complex
currying with K-flat/K-injective representatives gives tensor-Hom adjunction on both sites.
For a test Q, tensor-Hom, the composed projection formula, shriek adjunction, tensor-Hom
on S, and ordinary direct-image adjunction give the natural bijection of representable
Hom functors. Evaluating this bijection and its inverse on identities gives the isomorphism,
and naturality in P and M makes it a bifunctor isomorphism. No constructible preservation,
boundedness, finite Tor amplitude, or biduality is used.

Complete DAG proof plan:
1. Use the chosen closed-then-open factorization $s=ji$. In the pro-etale case, $U$ is Noetherian
by [lem-weil-pbc-noetherian-open-subscheme-noetherian]. Apply the same statement to the open
complement $V=U\setminus i(S)$ and to its intersections with affine opens of $U$: all are
quasi-compact. Thus $v:V\hookrightarrow U$ is a quasi-compact morphism. This verifies the
hypotheses of the pro-etale closed-localization and closed-support statements used below. No such
hypothesis is needed on the etale side. The Noetherian assumption restores the scheme context of
the enclosing unit; the imported standalone node did not state it. Dependencies:
lem-weil-pbc-noetherian-open-subscheme-noetherian.

2. The etale closed direct image $i_*$ is exact: at points of $i(S)$ its stalk is the
corresponding stalk on $S$ by [lemma-openclosed-stalk-lowerstar]; outside $i(S)$ it is zero, since
a neighbourhood disjoint from $i(S)$ has empty pullback. Exactness of geometric stalks and their
conservativity therefore check exactness of $i_*$ on every short exact sequence. The same
assertions hold for constant-coefficient modules by forgetting the module action. Its
inverse-image counit is an isomorphism by [lem-kun-04ca]. In the pro-etale case
[lem-weil-pbc-proetale-ringed-open-closed], applied on $U$ with the quasi-compact complement from
step 1, directly gives exactness, the closed counit isomorphism, and $v^{-1}i_*=0$. Consequently
$Ri_*=i_*$, computed termwise, in both cases. Moreover $i^{-1}$ and $v^{-1}$ detect zero sheaves:
in the etale case a sheaf zero on $V$ is supported on $i(S)$ and [lem-kun-04ca] identifies it with
$i_*G$, so its inverse image on $S$ is $G$; in the pro-etale case the short exact localization
sequence of [lem-weil-pbc-proetale-ringed-open-closed] proves this directly. Since both inverse
images are exact, they also jointly detect acyclic complexes, by applying this argument to each
cohomology sheaf. Dependencies: lemma-openclosed-stalk-lowerstar,
prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative, lem-kun-04ca,
lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-site-pullback-abelian-exact.

3. For any of the scheme maps in this argument, inverse image with constant coefficients is exact:
its underlying abelian functor is the exact site inverse image, and the inverse image of the
constant ring is the same constant ring. The module adjunction is
[lem-weil-pbc-ringed-topoi-module-adjunction]. It derives on the whole unbounded categories as
follows. Choose a K-injective resolution $N\to I$ on the source site using
[prop-pur-kinjective-resolutions-exist]. The direct image of $I$ is K-injective by
[lem-weil-pbc-right-adjoint-preserves-kinjective], since inverse image is exact. The
homotopy-category adjunction [lem-weil-pbc-termwise-adjunction-homotopy] and
[lem-weil-pbc-kinjective-hom-derived] then give
$$\operatorname{Hom}(t^{-1}Q,N)=\operatorname{Hom}_{K}(t^{-1}Q,I)=\operatorname{Hom}_{K}(Q,t_*I)=
\operatorname{Hom}(Q,Rt_*N).$$
Here any representative of $Q$ can be used. Thus $t^{-1}\dashv Rt_*$. The total derived functor
used here exists by [lem-weil-pbc-kinjective-total-derived]. The same K-injective calculation
derives $j_!\dashv j^{-1}$ from the etale sheaf adjunction and exactness
[lem-weil-pbc-extension-by-zero-adjunction, lem-weil-pbc-extension-by-zero-exact], or from the
pro-etale exact adjunction [lem-cbc-proetale-extension-zero]; for this calculation $j^{-1}I$ is
K-injective because $j_!$ is exact. All these bijections are natural. Composing this open
adjunction with the ambient closed adjunction of [lem-exc-closed-ambient] or
[lem-exc-proetale-closed-support] gives $Rs_!=j_!i_*\dashv Ri^!j^{-1}=Rs^!$. Dependencies:
lem-weil-pbc-site-pullback-abelian-exact, lem-weil-pbc-ringed-topoi-module-adjunction,
prop-pur-kinjective-resolutions-exist, lem-weil-pbc-right-adjoint-preserves-kinjective,
lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-kinjective-hom-derived,
lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-extension-by-zero-adjunction,
lem-weil-pbc-extension-by-zero-exact, lem-cbc-proetale-extension-zero, lem-exc-closed-ambient,
lem-exc-proetale-closed-support.

4. Inverse image on each of these constant-coefficient ringed sites has a canonical derived tensor
comparison $$t^{-1}(Q\otimes_A^LQ')\cong t^{-1}Q\otimes_A^Lt^{-1}Q'$$ by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. The same cited statement says that pullback
of a K-flat complex with flat terms is K-flat with flat terms. We will use both assertions for
$i$, $j$, and the complementary $v$. The constant-coefficient pullback is termwise inverse image
because it is exact; no finite Tor-amplitude condition on $Q,Q'$ occurs in this result. We will
also use the following direct consequence of K-flatness [def-pc-kflat-complex]: if one tensor
factor is K-flat, the other may be represented by an arbitrary complex. Indeed, replace that other
complex by a K-flat resolution; the cone of its resolution map is acyclic, and tensoring this cone
with the fixed K-flat factor is acyclic by the definition. Thus the induced map of total tensor
complexes is a quasi-isomorphism. This justifies the arbitrary first-factor representatives in
steps 5 and 8. Dependencies: lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
def-pc-kflat-complex.

5. First establish the open projection formula on both sites. An open immersion is an etale site
object by [lem-weil-pbc-open-immersion-etale], and inverse image there is restriction by
[lem-weil-pbc-etale-inverse-image-restriction]. For the pro-etale site use the localization
identification [lem-weil-proetale-weakly-etale-localization]. The ringed-slice formula
[lem-weil-pbc-ringed-slice-extension-tensor] therefore gives, for module sheaves, $j_!(F\otimes
j^{-1}G)\cong j_!F\otimes G$. Choose a K-flat resolution with flat terms $Q_0\to Q$ on $X$ using
[lem-pc-kflat-resolution]. By step 4, $j^{-1}Q_0$ is K-flat. Use any complex representing $P'$ on
$U$. In each total degree the sheaf formula identifies the summands of $j_!(P'\otimes j^{-1}Q_0)$
with those of $j_!P'\otimes Q_0$, and it commutes with both differentials by naturality. Extension
by zero commutes with their direct sums: the coproduct comparison follows directly from its
adjunction, since maps from either candidate to $N$ are families of maps from the summands to
$j^{-1}N$. Hence it identifies the total complexes. Exactness of $j_!$ from step 3 and the derived
tensor construction [lem-weil-pbc-site-derived-tensor-descent] give a natural isomorphism
$$j_!P'\otimes_A^L Q\cong j_!(P'\otimes_A^Lj^{-1}Q).$$ The pro-etale assertion is also exactly
[lem-cbc-extension-zero-projection-formula]. Dependencies: lem-weil-pbc-open-immersion-etale,
lem-weil-pbc-etale-inverse-image-restriction, lem-weil-proetale-weakly-etale-localization,
lem-weil-pbc-ringed-slice-extension-tensor, lem-pc-kflat-resolution,
lem-weil-pbc-site-derived-tensor-descent, lem-cbc-extension-zero-projection-formula.

6. Next establish the closed projection formula without using geometric stalks on the pro-etale
site. Form $$c:i_*P\otimes_A^LQ'\longrightarrow i_*(P\otimes_A^Li^{-1}Q')$$ as the adjoint under
$i^{-1}\dashv Ri_*=i_*$ of $$i^{-1}(i_*P\otimes_A^LQ')\cong
i^{-1}i_*P\otimes_A^Li^{-1}Q'\xrightarrow{\varepsilon_P\otimes1}P\otimes_A^Li^{-1}Q'.$$ The
comparison in step 4 and the closed counit isomorphism in step 2 identify $i^{-1}c$ with an
isomorphism. Both sides have zero restriction to $V$: for the source use $v^{-1}i_*P=0$ and the
tensor comparison, and for the target use $v^{-1}i_*=0$. The cone of $c$ therefore has zero
inverse images on $S$ and $V$, so it is acyclic by the joint detection on complexes proved in step
2. Thus $c$ is an isomorphism. This proves $i_*P\otimes_A^LQ'\cong i_*(P\otimes_A^Li^{-1}Q')$,
naturally in the two arbitrary complexes. The exactness and counit facts are precisely those of
[lem-kun-04ca] in the etale case and [lem-weil-pbc-proetale-ringed-open-closed] in the pro-etale
case; the tensor assertion is [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Dependencies:
lem-kun-04ca, lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

7. Compose the open and closed formulas of steps 5 and 6, with $P'=i_*P$ and $Q'=j^{-1}Q$, to
obtain $$Rs_!P\otimes_A^LQ=j_!i_*P\otimes_A^LQ\cong j_!(i_*P\otimes_A^Lj^{-1}Q)\cong
j_!i_*(P\otimes_A^Li^{-1}j^{-1}Q)=Rs_!(P\otimes_A^Ls^{-1}Q).$$ Here $s^{-1}=i^{-1}j^{-1}$: the
composite is left adjoint to the composite sheaf direct image $j_*i_*=s_*$, so identifies with
inverse image, including its unit and counit. On K-injectives, $Ri_*=i_*$ preserves K-injectives
by the exact inverse-image adjunction and [lem-weil-pbc-right-adjoint-preserves-kinjective]. Thus
$Rj_*Ri_*=Rs_*$ as well: on a K-injective $I$ the two constructions both give $j_*i_*I=s_*I$. All
comparisons in the displayed projection formula are natural. Dependencies:
lem-weil-pbc-right-adjoint-preserves-kinjective.

8. Derive the tensor-internal-Hom bijection on either ringed site, rather than taking it from a
definition of the operations. For arbitrary $K,L,N$, choose a K-flat representative $L_0$ of $L$
and a K-injective representative $I$ of $N$. The Hom complex $\mathcal Hom^\bullet(L_0,I)$ is
K-injective by [lem-pur-hom-kflat-into-kinjective]. For any representative $K_0$,
[lem-sc-derived-hom-tensor-total] gives $$\mathcal Hom^\bullet(K_0,\mathcal
Hom^\bullet(L_0,I))\cong\mathcal Hom^\bullet(\operatorname{Tot}(K_0\otimes L_0),I).$$ The two
sides represent $R\mathcal Hom(K,R\mathcal Hom(L,N))$ and $R\mathcal Hom(K\otimes_A^LL,N)$. Taking
$H^0$ of derived global sections and using [lem-pur-rhom-global-sections] on each side gives
$$\operatorname{Hom}(K,R\mathcal Hom(L,N))\cong\operatorname{Hom}(K\otimes_A^LL,N),$$ natural in
all three derived objects. Existence of $L_0$ and $I$ is [lem-pc-kflat-resolution,
prop-pur-kinjective-resolutions-exist]; the models and their descent are
[def-pur-derived-internal-hom, lem-weil-pbc-site-derived-tensor-descent]. Symmetry used to resolve
the second tensor variable is induced by the symmetric sheaf tensor
[lem-pc-sheaf-modules-tensor-closed]; swapping the degree-$p,q$ summands with sign $(-1)^{pq}$
commutes with the total differential and squares to the identity, hence gives the corresponding
derived symmetry. Dependencies: lem-pur-hom-kflat-into-kinjective,
lem-sc-derived-hom-tensor-total, lem-pur-rhom-global-sections, lem-pc-kflat-resolution,
prop-pur-kinjective-resolutions-exist, def-pur-derived-internal-hom,
lem-weil-pbc-site-derived-tensor-descent, lem-pc-sheaf-modules-tensor-closed.

9. For every $Q\in D_\tau(X,A)$, apply step 8, the projection formula of step 7 (with tensor
symmetry), the shriek adjunction of step 3, step 8 on $S$, and the star adjunction of step 3, in
that order: $$\begin{aligned} \operatorname{Hom}_X(Q,R\mathcal Hom_X(Rs_!P,M))
&\cong\operatorname{Hom}_X(Q\otimes_A^LRs_!P,M)\\
&\cong\operatorname{Hom}_X(Rs_!(s^{-1}Q\otimes_A^LP),M)\\
&\cong\operatorname{Hom}_S(s^{-1}Q\otimes_A^LP,Rs^!M)\\
&\cong\operatorname{Hom}_S(s^{-1}Q,R\mathcal Hom_S(P,Rs^!M))\\
&\cong\operatorname{Hom}_X(Q,Rs_*R\mathcal Hom_S(P,Rs^!M)). \end{aligned}$$ Every object here
belongs to its ordinary ambient derived category, by the constructions already checked; none of
the bijections requires a constructible or perfect input. Their composite is natural in $Q$,
contravariantly in $P$, and covariantly in $M$. No additional dependencies.

10. Write $B=R\mathcal Hom_X(Rs_!P,M)$, $C=Rs_*R\mathcal Hom_S(P,Rs^!M)$, and
$\theta_Q:\operatorname{Hom}(Q,B)\cong\operatorname{Hom}(Q,C)$ for step 9. Set
$\alpha=\theta_B(1_B):B\to C$ and $\beta=\theta_C^{-1}(1_C):C\to B$. Naturality in $Q$ gives
$\theta_Q(f)=\alpha f$ and $\theta_Q^{-1}(g)=\beta g$; evaluating their inverse composites at the
identities gives $\beta\alpha=1_B$ and $\alpha\beta=1_C$. Thus $\alpha$ is the desired
isomorphism. Naturality of $\theta$ in $P,M$ gives naturality of $\alpha$. This writes out the
required representable-functor argument directly, without applying the scheme-specific Yoneda node
to a derived category. No additional dependencies. -/
theorem ProEtale.nonempty_stratumAmbientHomIso
    (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsNoetherian X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty
      ((((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory).op.prod
          (𝟭 (proEtaleDerivedCategory X A))) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology X) (proEtaleConstantRing X A) ≅
        ((𝟭 (proEtaleDerivedCategory S A)ᵒᵖ).prod
          ((sfConstantModulePullback j A).mapDerivedCategory ⋙
            (sfIntrinsicClosedUpperShriek i
              (Scheme.Opens.ι (X := U) (⟨(Set.range i)ᶜ,
                (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩ :
                  U.Opens)) A).rightDerivedFunctor)) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology S) (proEtaleConstantRing S A) ⋙
            (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor) := by
  exact assembled A i j

end AlgebraicGeometry
