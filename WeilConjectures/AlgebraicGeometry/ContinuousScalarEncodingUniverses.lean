/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingUniverses
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTowerSupplement
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.ContinuousSubringScalarExactUniverses
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare

/-! # Exact scalar extension under the universe-polymorphic section encodings

Source: Bhatt--Scholze, Lemma 6.8.2(2); Stacks Project, Tags 03EK and 03DA.
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
attribute [local instance] Profinite.isMonHom_continuousMapRingObjMapOfUniverse
attribute [local instance] Profinite.isCommMonObj_continuousMapRingObjOfUniverse
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual integral inclusion, transported through the canonical continuous charts.
Source: Bhatt--Scholze, Lemma 6.8.2(2).
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes). -/
def continuousInternalScalarMapUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    condensedRingObj (Profinite.continuousCoefficientRingObj
      (Padic.coefficientExtensionIntegers l E)) T ⟶
      condensedRingObj (Profinite.continuousCoefficientRingObj E) T := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : IsIso (ContinuousRingUniverse.comparison T E) :=
    ContinuousRingUniverse.comparison_isIso T E
  exact ContinuousRingUniverse.comparison T (Padic.coefficientExtensionIntegers l E) ≫
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((Scheme.adicLisseForget T).map
          (latticeCoefficientSheafMap T
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)) ≫
    inv (ContinuousRingUniverse.comparison T E)

/-- The chart-transported integral inclusion is a ring-object homomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2(2); Stacks 00YV.
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes).
Proof: the two chart maps and the underlying map of the continuous ring-sheaf inclusion
preserve multiplication and the unit; their composite does as well. -/
instance continuousInternalScalarMapUniverses_isMonHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    IsMonHom (continuousInternalScalarMapUniverses l E T) := by
  unfold continuousInternalScalarMapUniverses
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : IsIso (ContinuousRingUniverse.comparison T E) :=
    ContinuousRingUniverse.comparison_isIso T E
  let : IsMonHom ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((Scheme.adicLisseForget T).map
          (latticeCoefficientSheafMap T
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))) :=
    Sheaf.isMonHom_sheafCompose_map (Scheme.ProEt.topology T)
      ((Scheme.adicLisseForget T).map
        (latticeCoefficientSheafMap T
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))
  infer_instance

private theorem internalScalar_eq_coefficientMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    continuousInternalScalarMapUniverses l E X =
      coefficientMap (Profinite.continuousMapRingObjMapOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val) X := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let := ContinuousRingUniverse.comparison_isIso X E
  apply (cancel_mono (ContinuousRingUniverse.comparison X E)).1
  dsimp only [continuousInternalScalarMapUniverses]
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  symm
  let adj := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  unfold coefficientMap ContinuousRingUniverse.comparison upperStarFromPoint
  erw [adj.homEquiv_naturality_left]
  rw [adj.homEquiv_naturality_right]
  dsimp only [adj]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

private theorem universeSectionRestriction (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)) :
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let J := Scheme.ProEt.topology X
  let T := Padic.coefficientExtensionIntegers l E
  let RT := continuousCoefficientRingSheaf X T
  let RS := continuousCoefficientRingSheaf X E
  let AT := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RT
  let AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RS
  let : IsCommMonObj AT := Sheaf.isCommMonObj_sheafCompose_obj J RT
    (fun V a b ↦ by exact @mul_comm (ULift.{u + 1} C(V.unop.left, T)) inferInstance a b)
  let : IsCommMonObj AS := Sheaf.isCommMonObj_sheafCompose_obj J RS
    (fun V a b ↦ by exact @mul_comm (ULift.{u + 1} C(V.unop.left, E)) inferInstance a b)
  let β : AT ⟶ AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((Scheme.adicLisseForget X).map
      (latticeCoefficientSheafMap X T.subtype continuous_subtype_val))
  let GT := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RT).symm).functor ⋙
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X T)).functor ⋙
    (ringModuleEquivalenceOfIso X ((Scheme.adicLisseForget X).mapIso c)).functor
  let GS := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RS).symm).functor ⋙
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X E)).functor
  Nonempty (SheafOfModules.restrictScalars
        ((Scheme.adicLisseForget X).map (sectionRingMap X β)) ⋙ GT ≅
      GS ⋙ Scheme.pbcRestrict
        (c.hom ≫ latticeCoefficientSheafMap X T.subtype continuous_subtype_val)) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let J := Scheme.ProEt.topology X
  let T := Padic.coefficientExtensionIntegers l E
  let RT := continuousCoefficientRingSheaf X T
  let RS := continuousCoefficientRingSheaf X E
  let AT := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RT
  let AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RS
  let : IsCommMonObj AT := Sheaf.isCommMonObj_sheafCompose_obj J RT
    (fun V a b ↦ by exact @mul_comm (ULift.{u + 1} C(V.unop.left, T)) inferInstance a b)
  let : IsCommMonObj AS := Sheaf.isCommMonObj_sheafCompose_obj J RS
    (fun V a b ↦ by exact @mul_comm (ULift.{u + 1} C(V.unop.left, E)) inferInstance a b)
  let β : AT ⟶ AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((Scheme.adicLisseForget X).map
      (latticeCoefficientSheafMap X T.subtype continuous_subtype_val))
  let GT := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RT).symm).functor ⋙
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X T)).functor ⋙
    (ringModuleEquivalenceOfIso X ((Scheme.adicLisseForget X).mapIso c)).functor
  let GS := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RS).symm).functor ⋙
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X E)).functor
  refine ⟨NatIso.ofComponents (fun M ↦ ?_) ?_⟩
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      rfl
    · intro Z W f
      ext
      rfl
  · intro M N f
    ext Z m
    rfl

set_option maxHeartbeats 800000 in
-- The chart and reconstructed section equivalences require a large definitional comparison.
private theorem universeRestriction (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)) :
    let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
    Nonempty (Mod.comap (continuousInternalScalarMapUniverses l E X) ⋙
        (completedContinuousModuleEquivalence l E X c).functor ≅
      (continuousFieldModuleEquivalenceUniverse l E X).functor ⋙
        Scheme.pbcRestrict (c.hom ≫ latticeCoefficientSheafMap X
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let J := Scheme.ProEt.topology X
  let T := Padic.coefficientExtensionIntegers l E
  let RT := continuousCoefficientRingSheaf X T
  let RS := continuousCoefficientRingSheaf X E
  let AT := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RT
  let AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RS
  let : IsCommMonObj AT := Sheaf.isCommMonObj_sheafCompose_obj J RT
    (fun V a b ↦ by exact @mul_comm (ULift.{u + 1} C(V.unop.left, T)) inferInstance a b)
  let : IsCommMonObj AS := Sheaf.isCommMonObj_sheafCompose_obj J RS
    (fun V a b ↦ by exact @mul_comm (ULift.{u + 1} C(V.unop.left, E)) inferInstance a b)
  let := ContinuousRingUniverse.comparison_isIso X T
  let := ContinuousRingUniverse.comparison_isIso X E
  let α := continuousInternalScalarMapUniverses l E X
  let β : AT ⟶ AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((Scheme.adicLisseForget X).map
      (latticeCoefficientSheafMap X T.subtype continuous_subtype_val))
  have hc : inv (ContinuousRingUniverse.comparison X T) ≫ α =
      β ≫ inv (ContinuousRingUniverse.comparison X E) := by
    dsimp only [α, continuousInternalScalarMapUniverses]
    change inv (ContinuousRingUniverse.comparison X T) ≫
      (ContinuousRingUniverse.comparison X T ≫ β ≫
        inv (ContinuousRingUniverse.comparison X E)) = _
    simp only [IsIso.inv_hom_id_assoc]
  let e₀ : Mod.comap α ⋙ Mod.comap (inv (ContinuousRingUniverse.comparison X T)) ≅
      Mod.comap (inv (ContinuousRingUniverse.comparison X E)) ⋙ Mod.comap β :=
    (Mod.comapComp _ _).symm ≪≫ Mod.comapCongr hc ≪≫ Mod.comapComp _ _
  let FT := (InternalAbelianSheafModule.sectionModuleEquivalence J AT).functor
  let FS := (InternalAbelianSheafModule.sectionModuleEquivalence J AS).functor
  let GT := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RT).symm).functor ⋙
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X T)).functor ⋙
    (ringModuleEquivalenceOfIso X ((Scheme.adicLisseForget X).mapIso c)).functor
  let GS := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RS).symm).functor ⋙
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X E)).functor
  let e₁ := sectionModuleComapIso X β
  obtain ⟨e₂⟩ := universeSectionRestriction l E X c
  let e := Functor.isoWhiskerRight e₀ (FT ⋙ GT) ≪≫
    Functor.isoWhiskerLeft (Mod.comap (inv (ContinuousRingUniverse.comparison X E)))
      (Functor.isoWhiskerRight e₁ GT) ≪≫
    Functor.isoWhiskerLeft
      (Mod.comap (inv (ContinuousRingUniverse.comparison X E)) ⋙ FS) e₂
  refine ⟨NatIso.ofComponents (fun M ↦ e.app M) ?_⟩
  intro M N f
  exact e.hom.naturality f

/-- Exact continuous localization commutes with the specified ordinary encodings.
There is no completeness, boundedness, or constructibility hypothesis on the module.
Source: Bhatt--Scholze, Lemma 6.8.2(2); Stacks 03EK, 03DA.
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes).

Proof: the continuous field sheaf is the sheaf localization of the continuous integral
ring at the constant uniformizer. Every continuous field-valued function has locally
bounded denominator, so its numerator is integral on a covering by open subobjects.
The sheaf localization is therefore the field sheaf, and localization is flat. Extension
along c is an equivalence, so completed-to-field extension is exact as well. For the
comparison, scalar restriction under the section-action equivalences is the identity
on the underlying abelian sheaf: the scalar acts by its image under the actual inclusion.
The definition of continuousInternalScalarMapUniverses is precisely the conjugation
of this inclusion by the two continuous charts. Thus the ordinary restrictions commute.
Their left adjoints are scalar extensions; uniqueness of left adjoints gives the natural
isomorphism stated below. It applies to arbitrary module sheaves and all universes.
Zero modules and the empty base are included by the same localization and adjunctions. -/
theorem continuousScalarEncodingUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (c : Scheme.pbcAdicCompletion T (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf T (Padic.coefficientExtensionIntegers l E)) :
    let a := c.hom ≫ latticeCoefficientSheafMap T
      (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val
    PreservesFiniteLimits
        (Mod.extendScalars (continuousInternalScalarMapUniverses l E T)) ∧
      Nonempty (Scheme.pbcExtend a ⋙
          (continuousFieldModuleEquivalenceUniverse l E T).inverse ≅
        (completedContinuousModuleEquivalence l E T c).inverse ⋙
          Mod.extendScalars (continuousInternalScalarMapUniverses l E T)) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let a := c.hom ≫ latticeCoefficientSheafMap T
    (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val
  let EA := completedContinuousModuleEquivalence l E T c
  let EE := continuousFieldModuleEquivalenceUniverse l E T
  obtain ⟨er⟩ := universeRestriction l E T c
  let adj₁ := EA.symm.toAdjunction.comp
    (Mod.extendRestrictAdjunction (continuousInternalScalarMapUniverses l E T))
  let adj₂ := (Scheme.pbcScalarAdjunction a).comp EE.symm.toAdjunction
  refine ⟨?_, ⟨(adj₂.ofNatIsoRight er.symm).leftAdjointUniq
    adj₁⟩⟩
  have hA (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔ ‖x‖ ≤ 1 := by
    have hm := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x
    change x ∈ Padic.coefficientExtensionIntegers l E ↔ _ at hm
    rw [hm]
    change spectralNorm ℚ_[l] E x ≤ 1 ↔ ‖x‖ ≤ 1
    rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[l]]
  have := continuousSubringScalarExtension_exact E (Padic.coefficientExtensionIntegers l E)
    l hA T
  exact preservesFiniteLimits_of_natIso
    (Mod.extendScalarsIsoOfEq (internalScalar_eq_coefficientMap l E T)).symm

end AlgebraicGeometry.ProEtale.CondensedRing
