/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicRealizationData
import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingConstructible
import WeilConjectures.AlgebraicGeometry.Native.NativeAdicConstructibilityEncoding
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import all WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTensorLocalization
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Constructibility through the native section presentation

Source: BS Remark 6.8.15 and the module-object internal-Hom finiteness theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
  Sheaf.symmetricCategory
attribute [local implicit_reducible] Sheaf.monoidalCategory Sheaf.braidedCategory
  Sheaf.symmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory

attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Mod.derivedMonoidalCategory
  CategoryTheory.Mod.braidedCategory CategoryTheory.Mod.symmetricCategory
  RingedDerivedNative.moduleMonoidal RingedDerivedNative.moduleSymmetric
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  RingedDerivedNative.monoidal
  ModuleObjectRingedComparison.ringedMonoidal ModuleObjectRingedComparison.ringedSymmetric

namespace WeilConjectures.AdicQbarRealization

private local instance nativeComm (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    @IsCommMonObj _ _ _ (inferInstance : SymmetricCategory
      (Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))).toBraidedCategory
      (adicConstantSheaf l X) _ := by
  exact adicConstantSheaf.isCommMonObj X

private local instance condensedComm (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    @IsCommMonObj _ _ _ (inferInstance : SymmetricCategory
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) _ := by
  exact isCommMonObj_condensedRingObj _ X

private local instance nativeClosed (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    MonoidalClosed (AdicSheaf l X) := Mod.monoidalClosed

private local instance nativeBraided (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    BraidedCategory (AdicSheaf l X) := Mod.braidedCategory

private local instance nativeFlat (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (AdicSheaf l X) := Mod.hasFunctorialFlatResolution

private local instance condensedClosed (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    MonoidalClosed (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) := Mod.monoidalClosed

private local instance condensedBraided (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    BraidedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) := Mod.braidedCategory

private local instance condensedFlat (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  Mod.hasFunctorialFlatResolution

private def homEquivalence
    {C D : Type*} [Category C] [Category D] (E : C ≌ D)
    {T H : C ⥤ C} {T' H' : D ⥤ D} (a : T ⊣ H) (b : T' ⊣ H')
    (t : T ⋙ E.functor ≅ E.functor ⋙ T') (Q : C) :
    E.functor.obj (H.obj Q) ≅ H'.obj (E.functor.obj Q) := by
  let e := conjugateIsoEquiv (a.comp E.toAdjunction) (E.toAdjunction.comp b) t.symm
  exact E.functor.mapIso (H.mapIso (E.unitIso.app Q)) ≪≫
    E.functor.mapIso (e.app (E.functor.obj Q)) ≪≫
    E.counitIso.app (H'.obj (E.functor.obj Q))

section MixedDerived
universe a b v w₁ w₂ s
open DerivedCategory
variable {C₁ : Type a} {C₂ : Type b}
  [Category.{v} C₁] [Abelian C₁] [IsGrothendieckAbelian.{s} C₁]
  [HasDerivedCategory.{w₁} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁]
  [MonoidalPreadditive C₁] [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
  [Category.{v} C₂] [Abelian C₂] [IsGrothendieckAbelian.{s} C₂]
  [HasDerivedCategory.{w₂} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂]
  [MonoidalPreadditive C₂] [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]
  (F : C₁ ⥤ C₂) [F.Monoidal] [F.IsEquivalence] [F.Additive]
private local instance : HasColimitsOfSize.{0, 0} C₁ := hasColimitsOfSizeShrink C₁
private local instance : HasColimitsOfSize.{0, 0} C₂ := hasColimitsOfSizeShrink C₂

private noncomputable def tensorLeftDerivedIsoOfKFlat (P : HomotopyCategory C₁ (.up ℤ))
    (hP : (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P)
    (hFP : (HomotopyCategory.quasiIso C₂ (.up ℤ)).kFlat
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) :
    (curriedTensor _).obj (Qh.obj P) ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (curriedTensor _).obj (F.mapDerivedCategory.obj (Qh.obj P)) :=
  have := isIso_tensorLeftCounit P hP
  have := isIso_tensorLeftCounit _ hFP
  Localization.liftNatIso Qh (HomotopyCategory.quasiIso C₁ (.up ℤ))
    (Qh ⋙ ((curriedTensor _).obj (Qh.obj P) ⋙ F.mapDerivedCategory))
    (Qh ⋙ (F.mapDerivedCategory ⋙ (curriedTensor _).obj (F.mapDerivedCategory.obj (Qh.obj P))))
    _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (asIso (tensorLeftCounit P)) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ F.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (asIso ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P)) Qh ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (asIso (tensorLeftCounit _)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactorsh.symm _ ≪≫
      Functor.isoWhiskerLeft _
        ((curriedTensor _).mapIso (F.mapDerivedCategoryFactorsh.app P).symm) ≪≫
      Functor.associator _ _ _)

omit [HasDerivedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂] in
/-- Every object `N` of `D(C₁)` is isomorphic to `Qh P` for a complex `P` such that both `P`
and `F(P)` are K-flat: a functorial flat resolution of a representative of `N`. -/
private theorem existsCommonFlat (N : DerivedCategory C₁) :
    ∃ P : HomotopyCategory C₁ (.up ℤ), (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P ∧
      (HomotopyCategory.quasiIso C₂ (.up ℤ)).kFlat ((F.mapHomotopyCategory (.up ℤ)).obj P) ∧
      Nonempty (Qh.obj P ≅ N) := by
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C₁) := Classical.arbitrary _
  have := F.preservesFlat_of_isEquivalence
  let K := Q.objPreimage N
  refine ⟨(HomotopyCategory.quotient _ _).obj (Λ.reduced.resolutionFunctor.obj K),
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K),
    ObjectProperty.prop_of_iso _ ((F.mapHomotopyCategoryFactors (.up ℤ)).app _).symm
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2
        (F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
          ObjectProperty.flat.essImage_ι_le K)),
    ⟨(quotientCompQhIso C₁).app _ ≪≫ asIso (Q.map (Λ.reduced.resolutionNatTrans.app K)) ≪≫
      Q.objObjPreimageIso N⟩⟩

/-- The functor `D(F)` commutes with tensoring on the left:
`D(F)(N ⊗ᴸ M) ≅ D(F) N ⊗ᴸ D(F) M`, naturally in `M`. -/
private noncomputable def tensorLeftDerivedIso (N : DerivedCategory C₁) :
    (curriedTensor _).obj N ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (curriedTensor _).obj (F.mapDerivedCategory.obj N) :=
  have h := existsCommonFlat F N
  Functor.isoWhiskerRight ((curriedTensor _).mapIso h.choose_spec.2.2.some.symm) _ ≪≫
    tensorLeftDerivedIsoOfKFlat F _ h.choose_spec.1 h.choose_spec.2.1 ≪≫
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso
      (F.mapDerivedCategory.mapIso h.choose_spec.2.2.some))

end MixedDerived

set_option maxHeartbeats 1000000 in
-- Comparing the two derived localization tensors requires extra elaboration heartbeats.
private theorem nativeSectionHomIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    (K L : DerivedCategory (AdicSheaf l X)) :
    Nonempty ((sectionDerived l X R).obj ((CategoryTheory.ihom K).obj L) ≅
      (ambientHom l X R).obj
        (op ((sectionDerived l X R).obj K), (sectionDerived l X R).obj L)) := by
  letI := R.commutative
  letI : @IsCommMonObj _ _ _ (inferInstance : SymmetricCategory
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
      (LocallyFiniteAdicRealization.abRing l X) _ := by
    exact R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  letI := RingedDerivedNative.moduleMonoidal.{u + 1, u, u} (Scheme.ProEt.topology X) (ring l X R)
  letI := RingedDerivedNative.moduleSymmetric.{u + 1, u, u} (Scheme.ProEt.topology X) (ring l X R)
  letI := RingedDerivedNative.modulePreadditive.{u + 1, u, u} (Scheme.ProEt.topology X) (ring l X R)
  letI := RingedDerivedNative.moduleClosed.{u + 1, u, u} (Scheme.ProEt.topology X) (ring l X R)
  letI := RingedDerivedNative.moduleGrothendieck.{u + 1, u, u}
    (Scheme.ProEt.topology X) (ring l X R)
  letI := RingedDerivedNative.moduleFlat.{u + 1, u, u} (Scheme.ProEt.topology X) (ring l X R)
  let U := AdicSheaf.forgetAb l X
  let E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (LocallyFiniteAdicRealization.abRing l X) ⥤ modules l X R :=
    sectionModuleFunctor.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (LocallyFiniteAdicRealization.abRing l X)
  obtain ⟨m⟩ := ModuleObjectRingedComparison.section_monoidal_data
    (Scheme.ProEt.topology X) (LocallyFiniteAdicRealization.abRing l X)
  letI : E.Monoidal := m.monoidal
  obtain ⟨c⟩ := nativeScalarForgetting_monoidal l X
  letI : U.Monoidal := c
  let F := U ⋙ E
  haveI : E.IsEquivalence := ModuleObjectRingedComparison.sectionFunctorEquivalenceForSite
    (Scheme.ProEt.topology X) (LocallyFiniteAdicRealization.abRing l X)
  haveI : U.IsEquivalence := nativeScalarForgetting_isEquivalence l X
  haveI : F.IsEquivalence := inferInstance
  haveI : F.Additive := by
    change (LocallyFiniteAdicRealization.sections l X).Additive
    infer_instance
  letI : F.Monoidal := by
    change (U ⋙ E).Monoidal
    infer_instance
  haveI : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  letI : BraidedCategory (DerivedCategory (AdicSheaf l X)) :=
    (DerivedCategory.nonempty_braidedCategory (AdicSheaf l X)).some
  letI : BraidedCategory (DerivedCategory (modules l X R)) :=
    DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (modules l X R) (.up ℤ))
  obtain ⟨S, hS, T, hT⟩ := RingedDerivedNative.closedAdjunction.{u + 1, u, u, u + 2}
    (Scheme.ProEt.topology X) (ring l X R)
  have ht : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (modules l X R))) := hS
  let t₀ : tensorLeft K ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ tensorLeft (F.mapDerivedCategory.obj K) :=
    tensorLeftDerivedIso F K
  let t : tensorLeft K ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ @tensorRight _ _ S.monoidal (F.mapDerivedCategory.obj K) :=
    t₀ ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory
        (by rw [ht]; exact BraidedCategory.tensorLeftIsoTensorRight _)
  exact ⟨homEquivalence F.mapDerivedCategory.asEquivalence
    (CategoryTheory.ihom.adjunction K) (S.adjunction (F.mapDerivedCategory.obj K)) t L⟩

set_option maxHeartbeats 1000000 in
-- The encoding and cohomology transports require extra elaboration heartbeats.
private theorem nativeHomConstructible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    (K L : DerivedCategory (AdicSheaf l T.left))
    (hK : ProEtale.DerivedCategory.boundedAdicConstructible l T.left K)
    (hL : ProEtale.DerivedCategory.boundedAdicConstructible l T.left L) :
    ProEtale.DerivedCategory.boundedAdicConstructible l T.left
      ((CategoryTheory.ihom K).obj L) := by
  haveI : IsNoetherian T.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian T.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace T.hom }
  letI : Fintype D.k₀ := Fintype.ofFinite _
  haveI : Fact D.p.Prime := ⟨D.prime⟩
  haveI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  haveI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  haveI : Fact (ringChar D.k ≠ l) := ⟨by rwa [ringChar.eq D.k D.p, ne_comm]⟩
  haveI : Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩
  let U := AdicSheaf.forgetAb l T.left
  let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology T.left) Ab.{u + 1})
    (NativeEncoding.coefficientIso l T.left).hom
  obtain ⟨c⟩ := nativeScalarForgetting_monoidal l T.left
  letI : U.Monoidal := c
  let F := NativeEncoding.encoding l T.left
  letI : F.Monoidal := by
    change (U ⋙ V).Monoidal
    infer_instance
  haveI : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  letI : BraidedCategory (DerivedCategory (AdicSheaf l T.left)) :=
    (DerivedCategory.nonempty_braidedCategory (AdicSheaf l T.left)).some
  haveI : F.IsEquivalence := NativeEncoding.encoding_isEquivalence l T.left
  let e := homEquivalence F.mapDerivedCategory.asEquivalence
    (CategoryTheory.ihom.adjunction K)
    (CategoryTheory.ihom.adjunction (F.mapDerivedCategory.obj K))
    (DerivedCategory.tensorLeftCompMapDerivedCategoryIso F K) L
  let Λ := Profinite.padicAlgClRingObj.{u} l
  letI : (ProEtale.boundedConstructible (condensedRingObj Λ T.left)).IsMonoidalClosed :=
    CondensedRing.isMonoidalClosed_boundedConstructible l T
  have hHom := (ProEtale.boundedConstructible (condensedRingObj Λ T.left)).prop_ihom
    (NativeEncoding.encoding_boundedConstructible l T.left K hK)
    (NativeEncoding.encoding_boundedConstructible l T.left L hL)
  have hH : ProEtale.boundedConstructible (condensedRingObj Λ T.left)
      (F.mapDerivedCategory.obj ((CategoryTheory.ihom K).obj L)) :=
    ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e.symm hHom.1,
      fun n ↦ constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e.symm)
        (hHom.2 n)⟩
  refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj hH.1, fun n ↦ ?_⟩
  apply (encoding_constructible_iff _).mpr
  exact constructible_of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app
    ((CategoryTheory.ihom K).obj L)).symm (hH.2 n)

/-- The native section presentation of the ambient internal Hom is bounded constructible.
Source: BS Remark 6.8.15; the finite-subextension condensed-coefficient Hom theorem.
(blueprint: lem-sf-native-adic-ambient-hom-constructible).

Proof: encode native modules over the finite-subextension condensed coefficient ring.
This is an exact strong monoidal equivalence, so uniqueness of right adjoints identifies
its derived internal Hom with the condensed internal Hom. The latter preserves bounded
constructibility on a separated finite-type scheme over the specified algebraically closed
field of characteristic different from l. The heart constructibility criterion and the
cohomology comparison reflect this property back to native complexes. Finally the native
section functor is the composite of scalar forgetting and the section-action equivalence,
both exact and strong monoidal. Its derived tensor comparison and the ringed tensor-Hom
adjunction identify the native internal Hom with the specified ambient module Hom.
The same constructions include zero objects, rank zero and the empty scheme. -/
theorem nativeAmbientHom_constructible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    (R : LocallyFiniteAdicRealization.Realization l T.left)
    (K L : DerivedCategory (AdicSheaf l T.left))
    (hK : ProEtale.DerivedCategory.boundedAdicConstructible l T.left K)
    (hL : ProEtale.DerivedCategory.boundedAdicConstructible l T.left L) :
    boundedConstructible l T.left R ((ambientHom l T.left R).obj
      (op ((sectionDerived l T.left R).obj K), (sectionDerived l T.left R).obj L)) := by
  exact ⟨_, nativeHomConstructible D l hl T K L hK hL, nativeSectionHomIso l T.left R K L⟩

end WeilConjectures.AdicQbarRealization
