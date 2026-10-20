/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import Sheaf.Algebra.Homology.IntegerFlatRepresentative
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.PrincipalIdealDomain
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc

/-! # Degreewise bounded flat approximation for constant projection functors

Source: Stacks Project, Etale Cohomology, Tag 0F0E, lemma-pull-out-constant.
(blueprint: lem-kun-constant-projection-flat-approximation)
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale


-- Match the braided structures used by the generic derived tensor comparison.
attribute [local instance 50000] constantProjectionSheafMonoidalPreadditive
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance 21000] sheafBraidedCategory


private instance integer_isDomain : IsDomain (ULift.{u + 1} ℤ) :=
  MulEquiv.isDomain ℤ (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toMulEquiv
private instance integer_isPrincipalIdealRing : IsPrincipalIdealRing (ULift.{u + 1} ℤ) :=
  IsPrincipalIdealRing.of_surjective
    (ULift.ringEquiv.symm.toRingHom : ℤ →+* ULift.{u + 1} ℤ)
    ULift.ringEquiv.symm.surjective

private theorem flat_of_mono_integer
    {R : Type (u + 1)} [CommRing R] [IsDomain R] [IsBezout R]
    {M N : ModuleCat.{u + 1} R} (f : M ⟶ N) [Mono f]
    (hN : Module.Flat R N) : Module.Flat R M := by
  have : Module.IsTorsionFree R N := inferInstance
  have : Module.IsTorsionFree R M := Function.Injective.moduleIsTorsionFree f
    ((ModuleCat.mono_iff_injective f).mp inferInstance) (fun r x ↦ f.hom.map_smul r x)
  exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)

private theorem integer_truncLE_flat
    {R : Type (u + 1)} [CommRing R] [IsDomain R] [IsBezout R]
    (P : CochainComplex (ModuleCat.{u + 1} R) ℤ)
    (hP : ∀ i : ℤ, Module.Flat R (P.X i)) (N i : ℤ) :
    ObjectProperty.flat ((P.truncLE N).X i) := by
  apply (ModuleCat.flat_iff_flat _).2
  exact flat_of_mono_integer ((P.ιTruncLE N).f i) (hP i)

private theorem integer_kFlat
    {R : Type (u + 1)} [CommRing R] [IsDomain R] [IsBezout R]
    (P : CochainComplex (ModuleCat.{u + 1} R) ℤ)
    (hP : ∀ i : ℤ, Module.Flat R (P.X i)) :
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} R) (.up ℤ)).kFlat P := by
  apply ObjectProperty.prop_of_isColimit _ P.isColimitFiltrationLECocone
  intro N
  exact CochainComplex.kFlat_of_isStrictlyLE_of_flat (P.truncLE N) N
    (integer_truncLE_flat P hP N)

private theorem constant_kFlat
    (X : Scheme.{u}) (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ℤ)
    (hP : ∀ i : ℤ, Module.Flat (ULift.{u + 1} ℤ) (P.X i)) :
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (.up ℤ)).kFlat
      (((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapHomologicalComplex (.up ℤ)).obj P) := by
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
  apply ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) P.isColimitFiltrationLECocone)
  intro N
  have : CochainComplex.IsStrictlyLE
      ((P.filtrationLE ⋙ F.mapHomologicalComplex (.up ℤ)).obj N) N := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero ((P.truncLE N).isZero_of_isStrictlyLE N i hi)
  apply CochainComplex.kFlat_of_isStrictlyLE_of_flat _ N
  intro i
  exact Functor.PreservesFlat.flat_obj (F := F) (integer_truncLE_flat P hP N i)

private theorem tensor_isGE_of_kFlat
    {C : Type (v + 1)} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{v} C]
    (E : DerivedCategory C) (a : ℤ) [E.IsGE a]
    (P : CochainComplex C ℤ) (b : ℤ) [P.IsStrictlyGE b]
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    {U : DerivedCategory C} (eU : U ≅ DerivedCategory.Q.obj P) :
    (((curriedTensor (DerivedCategory C)).obj E).obj U).IsGE (a + b) := by
  change (E ⊗ U).IsGE (a + b)
  obtain ⟨L, _, ⟨e⟩⟩ := E.exists_iso_Q_obj_of_isGE a
  have := CochainComplex.isStrictlyGE_tensorObj L P a b
  let e' : E ⊗ U ≅ DerivedCategory.Q.obj (L ⊗ P) :=
    tensorIso e eU ≪≫ DerivedCategory.QObjTensorQObjIsoOfKFlatRight L P hP
  exact DerivedCategory.TStructure.t.isGE_of_iso e'.symm _

private theorem constantSections_isGE
    {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    (X : Scheme.{u}) (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (a : ℤ) [E.IsGE a] :
    ((rightDerivedGlobalSections A X).obj E).IsGE a := by
  dsimp only [rightDerivedGlobalSections]
  let Γ := Sheaf.Γ X.smallEtaleTopology A
  let Eplus : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) := ⟨E, a, inferInstance⟩
  have hE : (DerivedCategory.Plus.ι.obj Eplus).IsGE a :=
    show E.IsGE a from inferInstance
  have : Eplus.IsGE a := (Eplus.isGE_ι_obj_iff a).1 hE
  refine (DerivedCategory.isGE_iff _ a).2 fun i hi ↦ ?_
  exact (Γ.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE Eplus a hi).of_iso
    ((DerivedCategory.homologyFunctor A i).mapIso
      (Γ.rightDerivedFunctorPlusCompatibility.app Eplus)).symm

private theorem ulift_integer_flat_representative
    (K : DerivedCategory.Plus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    ∃ (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ℤ) (b : ℤ),
      (∀ i : ℤ, i < b → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat (ULift.{u + 1} ℤ) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K.obj) := by
  let e : ModuleCat.{u + 1} (ULift.{u + 1} ℤ) ≌ ModuleCat.{u + 1} ℤ :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u + 1} ℤ)
  have : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} ℤ) :=
    IsGrothendieckAbelian.of_equivalence e
  let F := e.functor
  let G := e.inverse
  obtain ⟨P, b, hz, hflat, ⟨i⟩⟩ :=
    DerivedCategory.Plus.exists_boundedBelow_flat_representative.{u + 1, u + 1}
      (F.mapDerivedCategoryPlus.obj K)
  let P' := (G.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨P', b, fun j hj ↦ G.map_isZero (hz j hj), fun j ↦ ?_, ?_⟩
  · let : Module ℤ (P'.X j) := (P.X j).isModule
    have : Module.Flat ℤ (P'.X j) := hflat j
    have : Module.IsTorsionFree (ULift.{u + 1} ℤ) (P'.X j) :=
      Module.IsTorsionFree.comap (S := ℤ) ULift.down
        (fun r hr ↦ IsRegular.of_ne_zero
          (fun h ↦ (isRegular_iff_ne_zero.mp hr) (ULift.ext _ _ h)))
        (fun _ _ ↦ rfl)
    exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  · exact ⟨(G.mapDerivedCategoryFactors.app P).symm ≪≫ G.mapDerivedCategory.mapIso i ≪≫
      (Functor.mapDerivedCategoryCompNatIso e.unitIso.symm).app K.obj ≪≫
      (Functor.mapDerivedCategoryIdIso _).app K.obj⟩

private theorem boundedFlat_approximation
    {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    [HasDerivedCategory.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A]
    {D : Type (u + 2)} [Category.{u + 1} D] [Abelian D] [HasDerivedCategory.{u + 1} D]
    (F G : DerivedCategory A ⥤ DerivedCategory D)
    [sF : F.CommShift ℤ] [sG : G.CommShift ℤ]
    [tF : F.IsTriangulated] [tG : G.IsTriangulated]
    (K : DerivedCategory A)
    (hK : ∃ (P : CochainComplex A ℤ) (b : ℤ),
      (∀ i : ℤ, i < b → IsZero (P.X i)) ∧
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ K))
    (a : ℤ)
    (hF : ∀ (T : CochainComplex A ℤ) (c : ℤ),
      T.IsStrictlyGE c → (∀ i : ℤ, ObjectProperty.flat (T.X i)) →
      (F.obj (DerivedCategory.Q.obj T)).IsGE (a + c))
    (hG : ∀ (T : CochainComplex A ℤ) (c : ℤ),
      T.IsStrictlyGE c → (∀ i : ℤ, ObjectProperty.flat (T.X i)) →
      (G.obj (DerivedCategory.Q.obj T)).IsGE (a + c)) (n : ℤ) :
    ∃ (B : CochainComplex A ℤ) (b N : ℤ),
      B.IsStrictlyGE b ∧ B.IsStrictlyLE N ∧ (∀ i, ObjectProperty.flat (B.X i)) ∧
      ∃ f : K ⟶ DerivedCategory.Q.obj B,
        IsIso ((DerivedCategory.homologyFunctor D n).map (F.map f)) ∧
        IsIso ((DerivedCategory.homologyFunctor D n).map (G.map f)) := by
  obtain ⟨P, b, hz, hflat, ⟨e⟩⟩ := hK
  have : P.IsStrictlyGE b := (P.isStrictlyGE_iff b).2 hz
  let N := max b (n - a + 1)
  let ac := ComplexShape.Embedding.embeddingUpInt_areComplementary N (N + 1) rfl
  let S := P.shortComplexStupidTrunc ac
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (fun i ↦ (P.shortComplexStupidTruncSplitting ac i).shortExact)
  have hb : CochainComplex.IsStrictlyGE S.X₃ b := by
    dsimp only [S, HomologicalComplex.shortComplexStupidTrunc]
    infer_instance
  have hN : CochainComplex.IsStrictlyLE S.X₃ N := by
    dsimp only [S, HomologicalComplex.shortComplexStupidTrunc]
    infer_instance
  have hflatB (i : ℤ) : ObjectProperty.flat (S.X₃.X i) := by
    exact ObjectProperty.flat_of_retract (P.stupidTruncRetract _ i)
      (hflat i)
  have hT : CochainComplex.IsStrictlyGE S.X₁ (N + 1) := by
    dsimp only [S, HomologicalComplex.shortComplexStupidTrunc]
    infer_instance
  have hflatT (i : ℤ) : ObjectProperty.flat (S.X₁.X i) := by
    exact ObjectProperty.flat_of_retract (P.stupidTruncRetract _ i)
      (hflat i)
  have hFT := hF S.X₁ (N + 1) hT hflatT
  have hGT := hG S.X₁ (N + 1) hT hflatT
  have := hFT
  have := hGT
  have hf : IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.map (DerivedCategory.Q.map S.g))) :=
    DerivedCategory.isIso_homologyMap_mor₂ _
      (F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)) n (n + 1) rfl
      ((DerivedCategory.isGE_iff _ _).1 hFT n (by dsimp [N]; omega))
      ((DerivedCategory.isGE_iff _ _).1 hFT (n + 1) (by dsimp [N]; omega))
  have hg : IsIso ((DerivedCategory.homologyFunctor D n).map
      (G.map (DerivedCategory.Q.map S.g))) :=
    DerivedCategory.isIso_homologyMap_mor₂ _
      (G.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)) n (n + 1) rfl
      ((DerivedCategory.isGE_iff _ _).1 hGT n (by dsimp [N]; omega))
      ((DerivedCategory.isGE_iff _ _).1 hGT (n + 1) (by dsimp [N]; omega))
  refine ⟨S.X₃, b, N, hb, hN, hflatB, e.inv ≫ DerivedCategory.Q.map S.g, ?_, ?_⟩
  all_goals simp only [Functor.map_comp]; infer_instance

private noncomputable def constantDerivedComplexIso
    {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (T : CochainComplex A ℤ) :
    let C := constantSheaf X.smallEtaleTopology A
    (constantProjectionLeftDerived A X).obj (DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((C.mapHomologicalComplex (.up ℤ)).obj T) :=
  (constantSheaf X.smallEtaleTopology A).leftDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    (constantSheaf X.smallEtaleTopology A).mapDerivedCategoryFactors.app T

private theorem constantProjectionSource_isGE
    {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (a : ℤ)
    [((rightDerivedGlobalSections A X).obj E).IsGE a]
    (T : CochainComplex A ℤ) (b : ℤ) [T.IsStrictlyGE b]
    (ht : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat T) :
    ((constantProjectionSource A X E).obj (DerivedCategory.Q.obj T)).IsGE (a + b) := by
  dsimp only [constantProjectionSource, Arrow.mk_left, Functor.comp_obj]
  exact tensor_isGE_of_kFlat ((rightDerivedGlobalSections A X).obj E) a T b ht (Iso.refl _)

private theorem constantProjectionTarget_isGE
    {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (a : ℤ) [E.IsGE a]
    (T : CochainComplex A ℤ) (b : ℤ) [T.IsStrictlyGE b]
    (ht : (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology A) (.up ℤ)).kFlat
      (((constantSheaf X.smallEtaleTopology A).mapHomologicalComplex (.up ℤ)).obj T)) :
    ((constantProjectionTarget A X E).obj (DerivedCategory.Q.obj T)).IsGE (a + b) := by
  dsimp only [constantProjectionTarget, Functor.comp_obj]
  let C := constantSheaf X.smallEtaleTopology A
  let T' := (C.mapHomologicalComplex (.up ℤ)).obj T
  have : CochainComplex.IsStrictlyGE T' b := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact C.map_isZero (T.isZero_of_isStrictlyGE b i hi)
  let e := constantDerivedComplexIso X T
  have htensor : (((curriedTensor _).obj E).obj
      ((constantProjectionLeftDerived A X).obj (DerivedCategory.Q.obj T))).IsGE (a + b) :=
    tensor_isGE_of_kFlat E a T' b ht e
  exact @constantSections_isGE A _ _ _ _ X
    (((curriedTensor _).obj E).obj
      ((constantProjectionLeftDerived A X).obj (DerivedCategory.Q.obj T))) (a + b) htensor

private theorem constantProjection_approximation_of_kFlat
    {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (K : DerivedCategory A)
    (hK : ∃ (P : CochainComplex A ℤ) (b : ℤ),
      (∀ i : ℤ, i < b → IsZero (P.X i)) ∧
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ K))
    (a : ℤ) [E.IsGE a]
    (hk : ∀ (T : CochainComplex A ℤ), (∀ i : ℤ, ObjectProperty.flat (T.X i)) →
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat T)
    (hck : ∀ (T : CochainComplex A ℤ), (∀ i : ℤ, ObjectProperty.flat (T.X i)) →
      (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology A) (.up ℤ)).kFlat
        (((constantSheaf X.smallEtaleTopology A).mapHomologicalComplex (.up ℤ)).obj T)) (n : ℤ) :
    ∃ (B : CochainComplex A ℤ) (b N : ℤ),
      B.IsStrictlyGE b ∧ B.IsStrictlyLE N ∧ (∀ i, ObjectProperty.flat (B.X i)) ∧
      ∃ f : K ⟶ DerivedCategory.Q.obj B,
        IsIso ((DerivedCategory.homologyFunctor A n).map
          ((constantProjectionSource A X E).map f)) ∧
        IsIso ((DerivedCategory.homologyFunctor A n).map
          ((constantProjectionTarget A X E).map f)) := by
  have hF (T : CochainComplex A ℤ) (c : ℤ) (hc : T.IsStrictlyGE c)
      (hflat : ∀ i, ObjectProperty.flat (T.X i)) :
      ((constantProjectionSource A X E).obj (DerivedCategory.Q.obj T)).IsGE (a + c) := by
    have : T.IsStrictlyGE c := hc
    have : ((rightDerivedGlobalSections A X).obj E).IsGE a := constantSections_isGE X E a
    exact constantProjectionSource_isGE X E a T c (hk T hflat)
  have hG (T : CochainComplex A ℤ) (c : ℤ) (hc : T.IsStrictlyGE c)
      (hflat : ∀ i, ObjectProperty.flat (T.X i)) :
      ((constantProjectionTarget A X E).obj (DerivedCategory.Q.obj T)).IsGE (a + c) := by
    have : T.IsStrictlyGE c := hc
    exact constantProjectionTarget_isGE X E a T c (hck T hflat)
  let F := constantProjectionSource A X E
  let G := constantProjectionTarget A X E
  let : F.CommShift ℤ := constantProjectionSourceShift A X E
  let : G.CommShift ℤ := constantProjectionTargetShift A X E
  have : F.IsTriangulated := constantProjectionSource_exact A X E
  have : G.IsTriangulated := constantProjectionTarget_exact A X E
  exact boundedFlat_approximation F G K hK a hF hG n

/-- Every cohomological degree of the two constant projection functors can be computed
on a bounded flat quotient of a flat model of the coefficient object. This statement
concerns the two functors separately and makes no assertion about the projection map.
Source: Stacks Project, Tag 0F0E, the high stupid-tail reduction.
(blueprint: lem-kun-constant-projection-flat-approximation).

Proof: choose a flat integer complex P representing K, zero below b, and a complex
representing E, zero below a. Integer flat modules are torsion free, as are their
subgroups, hence their kernels are flat. The good upper truncations of P are bounded
flat complexes, and therefore K-flat. Their filtered colimit is P; total tensor
commutes with filtered colimits, which are exact, so P is K-flat. The same argument
applies to its stupid tails, heads, and their constant sheaf complexes. Global
sections is left exact, so its right derived functor preserves the lower bound a.
Fix n and choose N at least max(b,n-a+1). The stupid tail T of P in degrees at least
N+1 gives a degreewise split short exact sequence T -> P -> B, where B is the bounded
stupid head. Both ordinary tensors with T vanish below a+N+1, as do derived sections
of the sheaf tensor. Thus both tail objects vanish in degrees n and n+1. The long
exact sequences make P -> B an isomorphism in degree n after each functor. Compose
K -> Q(P) with Q(P -> B). Constant sheaves preserve exactness, flatness and colimits,
so all the ordinary tensors used compute the prescribed derived tensors. This also
covers n below either object's lower bound and zero input objects. -/
theorem exists_constantProjection_boundedFlat_approximation
    (X : Scheme.{u})
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (K : DerivedCategory.Plus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (n : ℤ) :
    let A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
    let F := constantProjectionSource A X (DerivedCategory.Plus.ι.obj E)
    let G := constantProjectionTarget A X (DerivedCategory.Plus.ι.obj E)
    ∃ (B : CochainComplex A ℤ) (b N : ℤ),
      B.IsStrictlyGE b ∧ B.IsStrictlyLE N ∧
      (∀ i : ℤ, Module.Flat (ULift.{u + 1} ℤ) (B.X i)) ∧
      ∃ f : (DerivedCategory.Plus.ι.obj K) ⟶ DerivedCategory.Q.obj B,
        IsIso ((DerivedCategory.homologyFunctor A n).map (F.map f)) ∧
        IsIso ((DerivedCategory.homologyFunctor A n).map (G.map f)) := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
  obtain ⟨a, ha⟩ := E.property
  have : (DerivedCategory.Plus.ι.obj E).IsGE a := ha
  have hK : ∃ (P : CochainComplex A ℤ) (b : ℤ),
      (∀ i : ℤ, i < b → IsZero (P.X i)) ∧
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Plus.ι.obj K) := by
    obtain ⟨P, b, hz, hp, he⟩ := ulift_integer_flat_representative K
    exact ⟨P, b, hz, fun i ↦ (ModuleCat.flat_iff_flat _).2 (hp i), he⟩
  obtain ⟨B, b, N, hb, hN, hflat, f, hf, hg⟩ :=
    constantProjection_approximation_of_kFlat X (DerivedCategory.Plus.ι.obj E)
      (DerivedCategory.Plus.ι.obj K) hK a
      (fun T hp ↦ integer_kFlat T (fun i ↦ (ModuleCat.flat_iff_flat _).1 (hp i)))
      (fun T hp ↦ constant_kFlat X T (fun i ↦ (ModuleCat.flat_iff_flat _).1 (hp i))) n
  exact ⟨B, b, N, hb, hN, fun i ↦ (ModuleCat.flat_iff_flat _).1 (hflat i), f, hf, hg⟩

end AlgebraicGeometry.Etale
