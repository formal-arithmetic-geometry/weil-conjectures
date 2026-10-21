/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.CategoryTheory.TorsionSheafComplexRepresentative
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Sites.Pretopology
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Integral derived tensor: lower bound and torsion cohomology

Source: literature/stacks-project/etale-cohomology.tex, Tag 0F0F, lemma-projection-formula-proper
(blueprint: lem-kun-integral-derived-tensor-bounded-torsion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

open MonoidalCategory

attribute [local instance 50000] CommRing.toRing
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance 21000] sheafBraidedCategory

private theorem etaleSheaf_monoidalPreadditive
    (D : Type (u + 2)) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] (T : Scheme.{u}) :
    MonoidalPreadditive (Sheaf T.smallEtaleTopology D) := by
  infer_instance

attribute [local instance 50000] etaleSheaf_monoidalPreadditive

-- Resolve the universal additivity assumption before specializing to sheaves.
private local instance (priority := 50000) tensorObj_additive
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] :
    ∀ X : C, ((curriedTensor C).obj X).Additive :=
  fun X ↦ tensorLeft_additive X

private local instance (priority := 50000) tensor_additive
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] :
    (curriedTensor C).Additive := by
  infer_instance

private local instance integer_isDomain : IsDomain (ULift.{u + 1} ℤ) :=
  MulEquiv.isDomain ℤ (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toMulEquiv

private local instance integer_isPrincipalIdealRing : IsPrincipalIdealRing (ULift.{u + 1} ℤ) :=
  IsPrincipalIdealRing.of_surjective
    (ULift.ringEquiv.symm.toRingHom : ℤ →+* ULift.{u + 1} ℤ)
    ULift.ringEquiv.symm.surjective

private theorem integerSheaf_flat_of_mono (T : Scheme.{u})
    {M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))}
    (f : M ⟶ N) [Mono f] (hN : ObjectProperty.flat N) : ObjectProperty.flat M := by
  apply (flat_iff_forall_flat_sheafFiber_obj M).2
  intro Ω _ _ t
  let F := (Scheme.pointSmallEtale t).ulift.{u + 1}.sheafFiber
    (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
  have : Module.Flat (ULift.{u + 1} ℤ) (F.obj N) :=
    (ModuleCat.flat_iff_flat _).1 ((flat_iff_forall_flat_sheafFiber_obj N).1 hN t)
  have : Mono (F.map f) := F.map_mono f
  have : Module.IsTorsionFree (ULift.{u + 1} ℤ) (F.obj M) :=
    Function.Injective.moduleIsTorsionFree (F.map f)
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
      (fun r x ↦ (F.map f).hom.map_smul r x)
  exact (ModuleCat.flat_iff_flat _).2
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance))

section HereditaryFlat

universe v w
variable {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{w} C]

private local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

private local instance (J : Type) [SmallCategory J] : HasColimitsOfShape J C :=
  HasColimitsOfSize.has_colimits_of_shape J

private local instance (J : Type) [SmallCategory J] (D : J ⥤ C) : HasColimit D :=
  HasColimitsOfShape.has_colimit D

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory C] in
private theorem hereditaryFlat_kFlat
    (hmono : ∀ {M N : C} (f : M ⟶ N) [Mono f],
      ObjectProperty.flat N → ObjectProperty.flat M)
    (P : CochainComplex C ℤ) (hP : ∀ i, ObjectProperty.flat (P.X i)) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  apply ObjectProperty.prop_of_isColimit _ P.isColimitFiltrationLECocone
  intro n
  apply CochainComplex.kFlat_of_isStrictlyLE_of_flat (P.truncLE n) n
  intro i
  exact hmono ((P.ιTruncLE n).f i) (hP i)

private theorem hereditaryFlat_lower_model
    (hmono : ∀ {M N : C} (f : M ⟶ N) [Mono f],
      ObjectProperty.flat N → ObjectProperty.flat M)
    (A : DerivedCategory C) (a : ℤ) [A.IsGE a] :
    ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyGE (a - 1)),
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧ Nonempty (A ≅ DerivedCategory.Q.obj P) := by
  let L := DerivedCategory.Q.objPreimage A
  obtain ⟨P, π, hπ, hP, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat L
  have : QuasiIso π := hπ
  let e : DerivedCategory.Q.obj P ≅ A :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso A
  have : P.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have hop : ObjectProperty.flat (P.opcycles (a - 1)) := by
    have he := CochainComplex.exactAt_of_isGE P a (a - 1)
    have : Mono (P.sc (a - 1)).fromOpcycles :=
      (ShortComplex.exact_iff_mono_fromOpcycles _).1 he
    exact hmono (P.sc (a - 1)).fromOpcycles (hP _)
  have hflat (i : ℤ) : ObjectProperty.flat ((P.truncGE (a - 1)).X i) := by
    obtain hi | rfl | hi := lt_trichotomy i (a - 1)
    · exact ObjectProperty.flat_of_isZero
        ((P.truncGE (a - 1)).isZero_of_isStrictlyGE (a - 1) i hi)
    · exact ObjectProperty.prop_of_iso _ (P.truncGEXIsoOpcycles (a - 1)).symm hop
    · exact ObjectProperty.prop_of_iso _ (P.truncGEXIso (a - 1) i hi).symm (hP i)
  have : P.IsGE (a - 1) := P.isGE_of_ge (a - 1) a (by omega)
  refine ⟨P.truncGE (a - 1), inferInstance, hereditaryFlat_kFlat hmono _ hflat, ?_⟩
  exact ⟨e.symm ≪≫ asIso (DerivedCategory.Q.map (P.πTruncGE (a - 1)))⟩

private theorem hereditaryFlat_tensor_isGE
    (hmono : ∀ {M N : C} (f : M ⟶ N) [Mono f],
      ObjectProperty.flat N → ObjectProperty.flat M)
    (A B : DerivedCategory C) (a b : ℤ) [A.IsGE a] [B.IsGE b] :
    (A ⊗ B).IsGE (a + b - 1) := by
  obtain ⟨P, _, hP, ⟨eA⟩⟩ := hereditaryFlat_lower_model hmono A a
  obtain ⟨L, _, ⟨eB⟩⟩ := B.exists_iso_Q_obj_of_isGE b
  have := CochainComplex.isStrictlyGE_tensorObj P L (a - 1) b
  let e : A ⊗ B ≅ DerivedCategory.Q.obj (P ⊗ L) :=
    tensorIso eA eB ≪≫ DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P L hP
  have h : (DerivedCategory.Q.obj (P ⊗ L)).IsGE (a + b - 1) := by
    have heq : a + b - 1 = (a - 1) + b := by omega
    rw [heq]
    infer_instance
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm _

private noncomputable def tensor_model
    (A B : DerivedCategory C) (L P : CochainComplex C ℤ)
    (eA : A ≅ DerivedCategory.Q.obj L) (eB : B ≅ DerivedCategory.Q.obj P)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    A ⊗ B ≅ DerivedCategory.Q.obj (HomologicalComplex.tensorObj L P) :=
  tensorIso eA eB ≪≫ DerivedCategory.QObjTensorQObjIsoOfKFlatRight L P hP

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory C]
  [BraidedCategory C] [MonoidalClosed C] in
private theorem tensor_complex_terms_property
    (Q : ObjectProperty C)
    (hcolim : ∀ {J : Type} [SmallCategory J] (D : J ⥤ C) (c : Cocone D),
      IsColimit c → (∀ j, Q (D.obj j)) → Q c.pt)
    (htensor : ∀ X Y : C, Q X → Q (X ⊗ Y))
    (L P : CochainComplex C ℤ) (hL : ∀ i, Q (L.X i)) (r : ℤ) :
    Q ((HomologicalComplex.tensorObj L P).X r) := by
  let K := (((curriedTensor C).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj L).obj P
  exact hcolim _ (K.toGradedObject.cofanMapObj
    (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) r)
    (K.toGradedObject.isColimitCofanMapObj _ r)
    (fun ⟨⟨i, j⟩, _⟩ ↦ htensor (L.X i) (P.X j) (hL i))

end HereditaryFlat

private theorem etale_tensor_isGE
    (D : Type (u + 2)) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u})
    (hmono : ∀ {M N : Sheaf T.smallEtaleTopology D} (f : M ⟶ N) [Mono f],
      ObjectProperty.flat N → ObjectProperty.flat M)
    (A B : DerivedCategory (Sheaf T.smallEtaleTopology D))
    (a b : ℤ) [A.IsGE a] [B.IsGE b] :
    (((derivedTensor D T).obj A).obj B).IsGE (a + b - 1) := by
  exact hereditaryFlat_tensor_isGE hmono A B a b

private noncomputable def etale_tensor_model
    (D : Type (u + 2)) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u})
    (A B : DerivedCategory (Sheaf T.smallEtaleTopology D))
    (L P : CochainComplex (Sheaf T.smallEtaleTopology D) ℤ)
    (eA : A ≅ DerivedCategory.Q.obj L) (eB : B ≅ DerivedCategory.Q.obj P)
    (hP : (HomologicalComplex.quasiIso (Sheaf T.smallEtaleTopology D) (.up ℤ)).kFlat P) :
    (((derivedTensor D T).obj A).obj B) ≅
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj L P) :=
  tensor_model A B L P eA eB hP

private theorem torsion_of_injective {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) (hf : Function.Injective f) (hN : IsAddTorsion N) : IsAddTorsion M := by
  intro x
  obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hN (f x))
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hf (by simpa using hx)⟩

private theorem torsion_colimit {J : Type*} [Category J]
    (D : J ⥤ AddCommGrpCat.{u + 1}) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ j, IsAddTorsion (D.obj j)) : IsAddTorsion c.pt := by
  let S : AddSubgroup c.pt :=
    { carrier := {x | IsOfFinAddOrder x}
      zero_mem' := IsOfFinAddOrder.zero
      add_mem' := fun hx hy ↦ hx.add hy
      neg_mem' := fun hx ↦ hx.neg }
  let d : Cocone D :=
    { pt := AddCommGrpCat.of S
      ι :=
        { app j := AddCommGrpCat.ofHom ((c.ι.app j).hom.codRestrict S
            (fun x ↦ (c.ι.app j).hom.isOfFinAddOrder (hD j x)))
          naturality i j f := by
            ext x
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (c.w f) x } }
  let ι : d.pt ⟶ c.pt := AddCommGrpCat.ofHom S.subtype
  have he : hc.desc d ≫ ι = 𝟙 c.pt := by
    apply hc.hom_ext
    intro j
    rw [hc.fac_assoc]
    rfl
  intro x
  have hx := (hc.desc d x).property
  change IsOfFinAddOrder (ι (hc.desc d x)) at hx
  simpa only [← ConcreteCategory.comp_apply, he, CategoryTheory.id_apply] using hx

private theorem torsion_tensor_modules (R : Type (u + 1)) [CommRing R]
    (M N : ModuleCat.{u + 1} R) (hM : IsAddTorsion M) : IsAddTorsion (TensorProduct R M N) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact IsOfFinAddOrder.zero
  | tmul x y =>
      exact ((TensorProduct.mk R M N).flip y).toAddMonoidHom.isOfFinAddOrder (hM x)
  | add x y hx hy => exact hx.add hy

private theorem torsion_sheaf_of_mono (T : Scheme.{u})
    {M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))}
    (f : M ⟶ N) [Mono f] (hN : Scheme.IsTorsionModuleSheaf N) :
    Scheme.IsTorsionModuleSheaf M := by
  refine ⟨fun Ω _ _ t ↦ ?_⟩
  let F := (Scheme.pointSmallEtale t).sheafFiber
    (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
  have : Mono (F.map f) := F.map_mono f
  exact torsion_of_injective (F.map f).hom.toAddMonoidHom
    ((ModuleCat.mono_iff_injective _).1 inferInstance) (hN.isTorsion_sheafFiber Ω t)

private theorem torsion_sheaf_colimit (T : Scheme.{u})
    {J : Type} [SmallCategory J]
    (D : J ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (c : Cocone D) (hc : IsColimit c) (hD : ∀ j, Scheme.IsTorsionModuleSheaf (D.obj j)) :
    Scheme.IsTorsionModuleSheaf c.pt := by
  refine ⟨fun Ω _ _ t ↦ ?_⟩
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let F := (Scheme.pointSmallEtale t).sheafFiber
    (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ⋙
    forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  exact torsion_colimit (D ⋙ F) (F.mapCocone c) (isColimitOfPreserves F hc)
    (fun j ↦ (hD j).isTorsion_sheafFiber Ω t)

private theorem torsion_sheaf_tensor (T : Scheme.{u})
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hM : Scheme.IsTorsionModuleSheaf M) : Scheme.IsTorsionModuleSheaf (M ⊗ N) := by
  refine ⟨fun Ω _ _ t ↦ ?_⟩
  let F := (Scheme.pointSmallEtale t).ulift.{u + 1}.sheafFiber
    (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
  let e : F ≅ (Scheme.pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :=
    (Scheme.pointSmallEtale t).uliftSheafFiberIso _
  have hM' : IsAddTorsion (F.obj M) :=
    IsAddTorsion.of_surjective (f := (e.inv.app M).hom.toAddMonoidHom)
      ((ModuleCat.epi_iff_surjective _).1 inferInstance) (hM.isTorsion_sheafFiber Ω t)
  have ht := torsion_tensor_modules (ULift.{u + 1} ℤ) (F.obj M) (F.obj N) hM'
  let k : F.obj M ⊗ F.obj N ≅
      (Scheme.pointSmallEtale t).sheafFiber.obj (M ⊗ N) :=
    Functor.Monoidal.μIso F M N ≪≫ e.app (M ⊗ N)
  exact IsAddTorsion.of_surjective (f := k.hom.hom.toAddMonoidHom)
    ((ModuleCat.epi_iff_surjective _).1 inferInstance) ht

private theorem torsion_tensor_complex (T : Scheme.{u})
    (L P : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) ℤ)
    (hL : ∀ i, Scheme.IsTorsionModuleSheaf (L.X i)) (r : ℤ) :
    Scheme.IsTorsionModuleSheaf ((HomologicalComplex.tensorObj L P).X r) := by
  exact tensor_complex_terms_property (fun M ↦ Scheme.IsTorsionModuleSheaf M)
    (fun D c hc hD ↦ torsion_sheaf_colimit T D c hc hD)
    (torsion_sheaf_tensor T) L P hL r

private theorem torsion_complex_homology (T : Scheme.{u})
    (L : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) ℤ)
    (hL : ∀ i, Scheme.IsTorsionModuleSheaf (L.X i)) (r : ℤ) :
    Scheme.IsTorsionModuleSheaf (L.homology r) := by
  have := torsion_sheaf_of_mono T (L.iCycles r) (hL r)
  exact Scheme.IsTorsionModuleSheaf.of_epi (L.homologyπ r)

private theorem precoverageSite {C : Type*} [Category C] [HasPullbacks C]
    (J : GrothendieckTopology C) : J.toPrecoverage.IsSiteForCoverings := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro X R T hR hT
    exact J.toPretopology.transitive R (fun _ f hf ↦ T f hf) hR
      (fun _ f hf ↦ hT _ f hf)
  · intro I X U a ha Y b
    refine ⟨fun i ↦ pullback b (a i), fun i ↦ pullback.fst _ _,
      fun i ↦ pullback.snd _ _, fun i ↦ IsPullback.of_hasPullback _ _, ?_⟩
    change Sieve.ofArrows _ _ ∈ J Y
    rw [Sieve.ofArrows_eq_pullback_of_isPullback _
      (fun i ↦ IsPullback.of_hasPullback b (a i))]
    exact J.pullback_stable b ha

private theorem precoverageTopology {C : Type*} [Category C]
    (J : GrothendieckTopology C) : J.toPrecoverage.toGrothendieck = J := by
  apply le_antisymm J.toGrothendieck_toPrecoverage_le
  intro U S hS
  simpa only [Sieve.generate_sieve] using
    J.toPrecoverage.generate_mem_toGrothendieck
      ((J.arrows_mem_toPrecoverage_iff S).2 hS)

universe u₁ v₁ t₁ w₁

private theorem torsion_representative_transport
    {C : Type u₁} [Category.{v₁} C] (P : Precoverage C) (hP : P.IsSiteForCoverings)
    (J : GrothendieckTopology C) (hJ : P.toGrothendieck = J)
    [HasSheafify J AddCommGrpCat.{max u₁ v₁ t₁}]
    [HasDerivedCategory.{w₁} (Sheaf J AddCommGrpCat.{max u₁ v₁ t₁})]
    (K : DerivedCategory (Sheaf J AddCommGrpCat.{max u₁ v₁ t₁}))
    (hK : ∃ a : ℤ, ∀ r : ℤ, r < a →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj K))
    (hT : ∀ r : ℤ, ((DerivedCategory.homologyFunctor _ r).obj K).IsTorsion) :
    ∃ (a : ℤ) (L : CochainComplex (Sheaf J AddCommGrpCat.{max u₁ v₁ t₁}) ℤ),
      (∀ r : ℤ, r < a → IsZero (L.X r)) ∧ (∀ r : ℤ, (L.X r).IsTorsion) ∧
        Nonempty (DerivedCategory.Q.obj L ≅ K) := by
  subst J
  exact Sheaf.exists_torsion_complex_representative.{u₁, v₁, t₁, w₁} P hP K hK hT

private theorem abelian_torsion_of_iso (T : Scheme.{u})
    {M N : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : M ≅ N) (hM : M.IsTorsion) : N.IsTorsion := by
  have : Scheme.IsTorsionSheaf M := (Scheme.isTorsionSheaf_iff_isTorsion M).2 hM
  exact (Scheme.isTorsionSheaf_iff_isTorsion N).1 (Scheme.IsTorsionSheaf.of_iso e)

private theorem integralForget_equivalence (T : Scheme.{u}) :
    (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).IsEquivalence := by
  let U := ModuleCat.restrictScalars (ULift.ringEquiv (R := ℤ)).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e := U.asEquivalence
  let S := sheafCompose T.smallEtaleTopology U
  have : S.EssSurj := ⟨fun P ↦ by
    let Q := (sheafCompose T.smallEtaleTopology e.inverse).obj P
    refine ⟨Q, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ (Functor.isoWhiskerLeft P.obj e.counitIso)⟩
  have : S.IsEquivalence := {}
  exact this

private theorem integer_torsion_model (T : Scheme.{u})
    (A : DerivedCategoryModule (ULift.{u + 1} ℤ) T) (a : ℤ) [A.IsGE a]
    (hA : ∀ r : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.homologyFunctor _ r).obj A))) :
    ∃ L : CochainComplex
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) ℤ,
      (∀ r, Scheme.IsTorsionModuleSheaf (L.X r)) ∧ Nonempty (A ≅ DerivedCategory.Q.obj L) := by
  let F := sheafCompose T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  have : F.IsEquivalence := integralForget_equivalence T
  let e := F.asEquivalence
  have : e.functor.Additive := (inferInstance : F.Additive)
  have : e.inverse.Additive := Equivalence.inverse_additive e
  have : PreservesLimitsOfSize.{0, 0} F := Adjunction.isEquivalencePreservesLimits F
  have : PreservesColimitsOfSize.{0, 0} F := Adjunction.isEquivalence_preservesColimits F
  have : PreservesFiniteLimits F := PreservesLimitsOfSize.preservesFiniteLimits F
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let K := F.mapDerivedCategory.obj A
  have hK : ∃ b : ℤ, ∀ r : ℤ, r < b →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj K) := by
    refine ⟨a, fun r hr ↦ ?_⟩
    exact (Functor.map_isZero F ((DerivedCategory.isGE_iff A a).1 inferInstance r hr)).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso r).app A).symm
  have hT (r : ℤ) : ((DerivedCategory.homologyFunctor _ r).obj K).IsTorsion :=
    abelian_torsion_of_iso T ((F.mapDerivedCategoryHomologyFunctorIso r).app A) (hA r)
  have hrep : ∃ (b : ℤ) (L : CochainComplex
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (∀ r : ℤ, r < b → IsZero (L.X r)) ∧ (∀ r : ℤ, (L.X r).IsTorsion) ∧
        Nonempty (DerivedCategory.Q.obj L ≅ K) := by
    exact torsion_representative_transport.{u + 1, u, 0, u + 1}
      T.smallEtaleTopology.toPrecoverage
      (precoverageSite T.smallEtaleTopology) T.smallEtaleTopology
      (precoverageTopology T.smallEtaleTopology) K hK hT
  obtain ⟨b, L, _, hL, ⟨eL⟩⟩ := hrep
  refine ⟨(e.inverse.mapHomologicalComplex (.up ℤ)).obj L, fun r ↦ ?_, ?_⟩
  · apply (Scheme.isTorsionModuleSheaf_iff_isTorsion _).2
    exact abelian_torsion_of_iso T (e.counitIso.app (L.X r)).symm (hL r)
  · exact ⟨e.mapDerivedCategory.unitIso.app A ≪≫
      e.inverse.mapDerivedCategory.mapIso eL.symm ≪≫
      e.inverse.mapDerivedCategoryFactors.app L⟩

/--
For integer étale coefficients, the derived tensor of two complexes bounded below in
cohomology is bounded below with the one-degree Tor loss.  If the first complex has
torsion cohomology, all cohomology sheaves of the derived tensor are torsion.
Source: literature/stacks-project/etale-cohomology.tex, Tag 0F0F, lemma-projection-formula-proper,
proof paragraphs beginning “Since Z has global dimension 1” and “Moreover”.
(blueprint: lem-kun-integral-derived-tensor-bounded-torsion).

Flat integer sheaves are closed under subobjects, as is checked on geometric stalks.
Upper good truncations therefore show that every complex of flat integer sheaves is K-flat.
Truncating a flat resolution of A below a - 1 gives a K-flat model with that strict bound;
tensoring it with a model of B bounded below by b proves the asserted bound.
For torsion, transport the bounded-below torsion-complex representative across the equivalence
between integer-module sheaves and abelian sheaves. Tensor this representative with a K-flat
model of B. Tensor products and coproducts preserve torsion stalks, and homology is a quotient
of a subobject, so every resulting cohomology sheaf is torsion.
-/
theorem integral_derivedTensor_boundedBelow_torsion
    (T : Scheme.{u})
    (A B : DerivedCategoryModule (ULift.{u + 1} ℤ) T)
    (a b : ℤ)
    (hA : ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) i).obj A))
    (hB : ∀ j : ℤ, j < b →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) j).obj B)) :
    (∀ r : ℤ, r < a + b - 1 →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) r).obj
        (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T).obj A).obj B))) ∧
      ((∀ i : ℤ, CategoryTheory.Sheaf.IsTorsion
        ((sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) i).obj A))) →
        ∀ r : ℤ, CategoryTheory.Sheaf.IsTorsion
          ((sheafCompose T.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) r).obj
              (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T).obj A).obj B)))) := by
  have : A.IsGE a := (DerivedCategory.isGE_iff A a).2 hA
  have : B.IsGE b := (DerivedCategory.isGE_iff B b).2 hB
  have hbound := etale_tensor_isGE (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T
    (integerSheaf_flat_of_mono T) A B a b
  constructor
  · exact (DerivedCategory.isGE_iff _ _).1 hbound
  · intro hT r
    obtain ⟨L, hL, ⟨eA⟩⟩ := integer_torsion_model T A a hT
    obtain ⟨P, _, hP, ⟨eB⟩⟩ :=
      hereditaryFlat_lower_model (integerSheaf_flat_of_mono T) B b
    let e := etale_tensor_model (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T A B L P eA eB hP
    have hh := torsion_complex_homology T (HomologicalComplex.tensorObj L P)
      (torsion_tensor_complex T L P hL) r
    let eH := (DerivedCategory.homologyFunctor _ r).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ r).app (HomologicalComplex.tensorObj L P)
    apply abelian_torsion_of_iso T
      ((sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).mapIso eH.symm)
    exact (Scheme.isTorsionModuleSheaf_iff_isTorsion _).1 hh

end AlgebraicGeometry.Etale
