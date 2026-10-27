/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import all Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.ContinuousIntegralScalarExact
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Sheaf.CategoryTheory.DerivedAdjointCochainCounit

/-! # Exact continuous scalar extension under the specified module encodings

Source: Bhatt--Scholze, Lemma 6.8.2(1),(2); Stacks Tags 03EK, 03DA, 015F and 07A6.
(blueprint: lem-weil-pbc-continuous-scalar-derived-encoding).

The sectionwise coefficient map is the actual inclusion on continuous functions.
The completed integral coefficient ring is identified with this ring by the canonical
quotient projections of the coefficient-completion dependency. All derived functors below
are the existing universal left-derived pairs, rather than arbitrary adjoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe uA vA wA uB vB wB uC vC wC uD vD wD u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
attribute [local instance] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The exact scalar square, including its all-complex and unit normalizations.
This helper packages the clauses for the fixed functors, equivalences and derived pairs
supplied to it; it makes no choice of coefficients, encodings or derived operations.
Source: Bhatt--Scholze, Lemma 6.8.2; Stacks Tags 015F, 03EK and 07A6
(blueprint: lem-weil-pbc-continuous-scalar-derived-encoding). -/
structure ContinuousScalarDerivedEncodingData
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (L : C ⥤ D) (U : D ⥤ C) (Lc : A ⥤ B) (Uc : B ⥤ A)
    [L.Additive] [U.Additive] [Lc.Additive] [Uc.Additive]
    (ΦA : A ≌ C) (ΦE : B ≌ D)
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (Fc : DerivedCategory A ⥤ DerivedCategory B)
    (εc : DerivedCategory.Qh ⋙ Fc ⟶
      Lc.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ac : Lc ⊣ Uc)
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits Uc] [PreservesFiniteColimits Uc]
    (adc : Fc ⊣ Uc.mapDerivedCategory) where
  /-- Ordinary sectionwise scalar extension is left exact. -/
  [extensionLimits : PreservesFiniteLimits L]
  /-- Ordinary sectionwise scalar extension is right exact. -/
  [extensionColimits : PreservesFiniteColimits L]
  /-- Ordinary internal scalar extension is left exact. -/
  [internalLimits : PreservesFiniteLimits Lc]
  /-- Ordinary internal scalar extension is right exact. -/
  [internalColimits : PreservesFiniteColimits Lc]
  /-- The specified integral encoding is additive. -/
  [integralAdditive : ΦA.functor.Additive]
  /-- The specified rational encoding is additive. -/
  [fieldAdditive : ΦE.functor.Additive]
  /-- The termwise derived integral encoding is an equivalence. -/
  integralDerivedEquivalence : ΦA.functor.mapDerivedCategory.IsEquivalence
  /-- The termwise derived rational encoding is an equivalence. -/
  fieldDerivedEquivalence : ΦE.functor.mapDerivedCategory.IsEquivalence
  /-- The ordinary scalar adjunction to the actual restriction. -/
  ordinary : L ⊣ U
  /-- The ordinary extension comparison under the specified encodings. -/
  extension : Lc ⋙ ΦE.functor ≅ ΦA.functor ⋙ L
  /-- The ordinary restriction comparison under the specified encodings. -/
  restriction : Uc ⋙ ΦA.functor ≅ ΦE.functor ⋙ U
  /-- The ordinary comparisons preserve the specified unit. -/
  ordinaryUnit : ∀ M : A,
    ΦA.functor.map (ac.unit.app M) ≫ restriction.hom.app (Lc.obj M) ≫
        U.map (extension.hom.app M) = ordinary.unit.app (ΦA.functor.obj M)
  /-- The actual sectionwise derived functor agrees with the exact termwise functor. -/
  comparison : F ≅ L.mapDerivedCategory
  /-- Its comparison is the given universal derived counit, on every homotopy object. -/
  comparisonCounit : ∀ K : HomotopyCategory C (.up ℤ),
    comparison.hom.app (DerivedCategory.Qh.obj K) ≫
      L.mapDerivedCategoryFactorsh.hom.app K = ε.app K
  /-- The actual internal derived functor agrees with the exact termwise functor. -/
  internalComparison : Fc ≅ Lc.mapDerivedCategory
  /-- The internal comparison retains the actual universal derived counit. -/
  internalComparisonCounit : ∀ K : HomotopyCategory A (.up ℤ),
    internalComparison.hom.app (DerivedCategory.Qh.obj K) ≫
      Lc.mapDerivedCategoryFactorsh.hom.app K = εc.app K
  /-- Shift on the actual sectionwise derived functor. -/
  [commShift : F.CommShift ℤ]
  /-- This is precisely the shift transported from termwise extension. -/
  commShift_eq : commShift = Functor.CommShift.ofIso comparison.symm ℤ
  /-- The actual scalar extension is triangulated for that shift. -/
  triangulated : F.IsTriangulated
  /-- Derived extension commutes with the specified encodings. -/
  derivedExtension : Fc ⋙ ΦE.functor.mapDerivedCategory ≅
    ΦA.functor.mapDerivedCategory ⋙ F
  /-- On every complex this is localization of the ordinary comparison degree by degree. -/
  derivedExtensionComplex : ∀ K : CochainComplex A ℤ,
    ΦE.functor.mapDerivedCategory.map
        (Scheme.reductionComplexCounit Lc Fc εc K) ≫
      ΦE.functor.mapDerivedCategoryFactors.hom.app
        ((Lc.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex extension (.up ℤ)).hom.app K) =
    derivedExtension.hom.app (DerivedCategory.Q.obj K) ≫
      F.map (ΦA.functor.mapDerivedCategoryFactors.hom.app K) ≫
      Scheme.reductionComplexCounit L F ε
        ((ΦA.functor.mapHomologicalComplex (.up ℤ)).obj K)
  /-- The actual derived scalar adjunction to exact termwise restriction. -/
  adjunction : F ⊣ U.mapDerivedCategory
  /-- The sectionwise unit is the localized ordinary tensor unit on every complex. -/
  unit : ∀ K : CochainComplex C ℤ,
    adjunction.unit.app (DerivedCategory.Q.obj K) ≫
      U.mapDerivedCategory.map (Scheme.reductionComplexCounit L F ε K) ≫
      U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((ordinary.mapHomologicalComplex (.up ℤ)).unit.app K)
  /-- The same normalization holds for the specified actual internal adjunction. -/
  internalUnit : ∀ K : CochainComplex A ℤ,
    adc.unit.app (DerivedCategory.Q.obj K) ≫
      Uc.mapDerivedCategory.map (Scheme.reductionComplexCounit Lc Fc εc K) ≫
      Uc.mapDerivedCategoryFactors.hom.app ((Lc.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((ac.mapHomologicalComplex (.up ℤ)).unit.app K)

private theorem ringRestriction (X : Scheme.{u}) (T S : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [TotallyDisconnectedSpace S]
    (φ : T →+* S) (hφ : Continuous φ) :
    ∃ ρ : Mod.comap ((upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap φ hφ))) ⋙
      (continuousRingModuleEquivalence X T).functor ≅
    (continuousRingModuleEquivalence X S).functor ⋙
      SheafOfModules.restrictScalars (continuousMapRingSheafMap X φ hφ),
      ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj S) X))
        (V : X.ProEtᵒᵖ) (x : N.X.obj.obj V),
        (ρ.hom.app N).val.app V x = x := by
  let J := Scheme.ProEt.topology X
  let RT := continuousMapRingSheaf X T
  let RS := continuousMapRingSheaf X S
  let AT := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RT
  let AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RS
  let : IsCommMonObj AT := Sheaf.isCommMonObj_sheafCompose_obj J RT
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let : IsCommMonObj AS := Sheaf.isCommMonObj_sheafCompose_obj J RS
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, S)) inferInstance a b)
  let α := (upperStarFromPoint X).map
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap φ hφ))
  let β := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X φ hφ)
  have hc : inv (chartComparison X T) ≫ α = β ≫ inv (chartComparison X S) := by
    apply (cancel_epi (chartComparison X T)).1
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, ← chartComparison_naturality X T S φ hφ]
    simp
    rfl
  let e₀ : Mod.comap α ⋙ Mod.comap (inv (chartComparison X T)) ≅
      Mod.comap (inv (chartComparison X S)) ⋙ Mod.comap β :=
    (Mod.comapComp _ _).symm ≪≫ Mod.comapCongr hc ≪≫ Mod.comapComp _ _
  let FT := (InternalAbelianSheafModule.sectionModuleEquivalence J AT).functor
  let FS := (InternalAbelianSheafModule.sectionModuleEquivalence J AS).functor
  let GT := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RT).symm).functor
  let GS := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RS).symm).functor
  let e₁ := sectionModuleComapIso X β
  let e₂ : SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (sectionRingMap X β)) ⋙ GT ≅
      GS ⋙ SheafOfModules.restrictScalars (continuousMapRingSheafMap X φ hφ) := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
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
  refine ⟨NatIso.ofComponents (fun M ↦
    (FT ⋙ GT).mapIso (e₀.app M) ≪≫
      GT.mapIso (e₁.app ((Mod.comap (inv (chartComparison X S))).obj M)) ≪≫
      e₂.app (FS.obj ((Mod.comap (inv (chartComparison X S))).obj M))) ?_, ?_⟩
  · intro M N f
    ext Z m
    rfl
  · intros
    rfl

private theorem ringIsoRestriction (X : Scheme.{u})
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    (eR : R' ≅ R) (eS : S' ≅ S) (φ : R ⟶ S) (φ' : R' ⟶ S')
    (h : φ' ≫ eS.hom = eR.hom ≫ φ) :
    ∃ τ : SheafOfModules.restrictScalars φ ⋙ (ringModuleEquivalenceOfIso X eR).functor ≅
      (ringModuleEquivalenceOfIso X eS).functor ⋙ SheafOfModules.restrictScalars φ',
      ∀ (M : SheafOfModules.{u + 1} S) (V : X.ProEtᵒᵖ) (m : M.val.obj V),
        (τ.hom.app M).val.app V m = m := by
  refine ⟨NatIso.ofComponents (fun M ↦ ?_) ?_, ?_⟩
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      have hs := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app V) h) r
      change (eS.hom.hom.app V (φ'.hom.app V r)) • (show M.val.obj V from m) =
        (φ.hom.app V (eR.hom.hom.app V r)) • (show M.val.obj V from m)
      exact congrArg (fun z ↦ z • (show M.val.obj V from m)) hs
    · intro V W f
      ext m
      rfl
  · intro M N f
    ext V m
    rfl
  · intros
    rfl

private theorem spectralRestriction (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    ∃ ρ : Mod.comap (coefficientMap (integralScalarMap ℓ E) X) ⋙
        (continuousIntegerModuleEquivalence ℓ E X).functor ≅
      (continuousFieldModuleEquivalence ℓ E X).functor ⋙
        Scheme.reductionRestrict X (lisseIntegerToField ℓ E X),
      ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (V : X.ProEtᵒᵖ) (x : N.X.obj.obj V),
        (ρ.hom.app N).val.app V x = x := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let : TotallySeparatedSpace E :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
      obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
      refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
      · simp only [Metric.mem_ball, dist_self, hr]
      · simp only [Set.mem_compl, Metric.mem_ball, dist_comm, not_lt, hr'.le]
  have hr := ringRestriction X (continuousIntegers ℓ E) E
    (continuousIntegers ℓ E).subtype continuous_subtype_val
  let ρ := hr.choose
  have hρ := hr.choose_spec
  let G := (ringModuleEquivalenceOfIso X
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseIntegerSheaf_eq ℓ E X)))).functor
  let H := (ringModuleEquivalenceOfIso X
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseFieldSheaf_eq ℓ E X)))).functor
  let β := continuousMapRingSheafMap X (continuousIntegers ℓ E).subtype
    continuous_subtype_val
  have hs := ringIsoRestriction X
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseIntegerSheaf_eq ℓ E X)))
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseFieldSheaf_eq ℓ E X))) β
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (lisseIntegerToField ℓ E X))
    (by
      exact congrArg ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (lisseScalar_square ℓ E X))
  let τ := hs.choose
  have hτ := hs.choose_spec
  refine ⟨NatIso.ofComponents (fun N ↦ ?_) ?_, ?_⟩
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext x
      have hG (y : N.X.obj.obj V) : (G.map (ρ.hom.app N)).val.app V y = y :=
        hρ N V y
      have h₁ := ((G.map (ρ.hom.app N)).val.app V).hom.map_smul r x
      have h₂ := ((τ.hom.app
        ((continuousRingModuleEquivalence X E).functor.obj N)).val.app V).hom.map_smul r x
      rw [hG, hG] at h₁
      rw [hτ, hτ] at h₂
      exact h₂.symm.trans h₁.symm
    · intro V W f
      ext x
      rfl
  · intro M N f
    ext V x
    rfl
  · intros
    rfl

private theorem inverseMateIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {F : C ⥤ D} {V : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} [G.IsEquivalence] [H.IsEquivalence]
    (a : L ⊣ U) (b : F ⊣ V) (ρ : U ⋙ G ≅ H ⋙ V) :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ ρ.hom)).natTrans) := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ ρ.hom)).natTrans
  let βop : TwoSquare H.op U.op V.op G.op :=
    TwoSquare.mk _ _ _ _ (NatTrans.op ρ.hom)
  have hi := isIso_mateEquiv_of_isEquivalence a.op b.op βop
  have he : NatTrans.op α = (mateEquiv a.op b.op βop).natTrans := by
    ext X
    simp [α, βop, mateEquiv]
  have : IsIso (NatTrans.op α) := by rw [he]; exact hi
  have (X : A) : IsIso (α.app X) := by
    have : IsIso ((α.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
    exact isIso_of_op (α.app X)
  exact NatIso.isIso_of_isIso_app α

private theorem inverseMateUnit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {F : C ⥤ D} {V : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ U) (b : F ⊣ V) (ρ : U ⋙ G ≅ H ⋙ V)
    [IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ ρ.hom)).natTrans)] (M : A) :
    let α := (asIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ ρ.hom)).natTrans)).symm
    G.map (a.unit.app M) ≫ ρ.hom.app (L.obj M) ≫ V.map (α.hom.app M) =
      b.unit.app (G.obj M) := by
  dsimp only
  have h := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ ρ.hom) M
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← V.map_comp]
  erw [← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app, V.map_id, Category.comp_id]
  rfl

private theorem ordinaryScalar (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    ∃ a : Scheme.reductionChange X φ ⊣ Scheme.reductionRestrict X φ,
      ∀ (M : Scheme.reductionModules X R) (V : X.ProEtᵒᵖ) (x : M.val.obj V),
        (a.unit.app M).val.app V x = Scheme.reductionTensorSection X φ M V 1 x := by
  exact ⟨(Scheme.ordinaryAdjunction_exists X φ).choose,
    fun M V x ↦ Scheme.reductionUnit_apply X φ M V x⟩

private theorem exactTransfer
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (f : B ≌ D) (Lc : A ⥤ B) (L : C ⥤ D)
    [PreservesFiniteLimits Lc] (α : Lc ⋙ f.functor ≅ e.functor ⋙ L) :
    PreservesFiniteLimits L := by
  have : PreservesFiniteLimits (Lc ⋙ f.functor) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (e.functor ⋙ L) := preservesFiniteLimits_of_natIso α
  have : PreservesFiniteLimits (e.inverse ⋙ e.functor ⋙ L) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits ((e.inverse ⋙ e.functor) ⋙ L) :=
    preservesFiniteLimits_of_natIso (Functor.associator _ _ _).symm
  exact preservesFiniteLimits_of_natIso
    (Functor.isoWhiskerRight e.counitIso L ≪≫ Functor.leftUnitor L)

section DerivedAssembly

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem complexCounit_eq (L : C ⥤ D) [L.Additive]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex C ℤ) :
    Scheme.reductionComplexCounit L F ε K =
      F.map ((DerivedCategory.quotientCompQhIso C).inv.app K) ≫
        ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
          (DerivedCategory.quotientCompQhIso D).hom.app
            ((L.mapHomologicalComplex (.up ℤ)).obj K) := by
  dsimp only [Scheme.reductionComplexCounit]
  rw [show (L.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ from rfl]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]

private def exactComparison (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    F ≅ L.mapDerivedCategory :=
  Functor.leftDerivedUnique L.mapDerivedCategory F ε L.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso C (.up ℤ))

private theorem exactComparison_fac (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (K : HomotopyCategory C (.up ℤ)) :
    (exactComparison L F ε).hom.app (DerivedCategory.Qh.obj K) ≫
      L.mapDerivedCategoryFactorsh.hom.app K = ε.app K := by
  simp [exactComparison]

private theorem exactComparison_complex (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (K : CochainComplex C ℤ) :
    Scheme.reductionComplexCounit L F ε K =
      (exactComparison L F ε).hom.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategoryFactors.hom.app K := by
  rw [Scheme.reductionComplexCounit]
  have h := exactComparison_fac L F ε ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  have hf := L.mapDerivedCategoryFactorsh_hom_app K
  change _ = _ at hf
  rw [← h, hf]
  simp only [Category.assoc]
  rw [← (exactComparison L F ε).hom.naturality_assoc]
  rw [← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rw [← DerivedCategory.Qh.map_comp_assoc, Iso.inv_hom_id_app]
  erw [DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem squareComplex
    (L : C ⥤ D) (Lc : A ⥤ B) (G : A ⥤ C) (H : B ⥤ D)
    [L.Additive] [Lc.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits Lc] [PreservesFiniteColimits Lc]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (α : Lc ⋙ H ≅ G ⋙ L) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso α).hom.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (Lc.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((Lc.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso Lc H).hom.app
    (DerivedCategory.Q.obj K))).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Iso.hom_inv_id_app_assoc]
  rfl

private theorem assembleDerived
    (L : C ⥤ D) (U : D ⥤ C) (Lc : A ⥤ B) (Uc : B ⥤ A)
    [L.Additive] [U.Additive] [Lc.Additive] [Uc.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits Lc] [PreservesFiniteColimits Lc]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits Uc] [PreservesFiniteColimits Uc]
    (ΦA : A ≌ C) (ΦE : B ≌ D) [ΦA.functor.Additive] [ΦE.functor.Additive]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (Fc : DerivedCategory A ⥤ DerivedCategory B)
    (εc : DerivedCategory.Qh ⋙ Fc ⟶ Lc.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [Fc.IsLeftDerivedFunctor εc (HomotopyCategory.quasiIso A (.up ℤ))]
    (ac : Lc ⊣ Uc) (adc : Fc ⊣ Uc.mapDerivedCategory)
    (a : L ⊣ U) (α : Lc ⋙ ΦE.functor ≅ ΦA.functor ⋙ L)
    (ρ : Uc ⋙ ΦA.functor ≅ ΦE.functor ⋙ U)
    (hu : ∀ M : A, ΦA.functor.map (ac.unit.app M) ≫
      ρ.hom.app (Lc.obj M) ≫ U.map (α.hom.app M) = a.unit.app (ΦA.functor.obj M))
    (hic : ∀ K : CochainComplex A ℤ,
      adc.unit.app (DerivedCategory.Q.obj K) ≫
        Uc.mapDerivedCategory.map (Scheme.reductionComplexCounit Lc Fc εc K) ≫
        Uc.mapDerivedCategoryFactors.hom.app ((Lc.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((ac.mapHomologicalComplex (.up ℤ)).unit.app K))
    {P : (L ⊣ U) → Prop} {Q : (Uc ⋙ ΦA.functor ≅ ΦE.functor ⋙ U) → Prop}
    (ha : P a) (hρ : Q ρ) :
    ∃ d : ContinuousScalarDerivedEncodingData L U Lc Uc ΦA ΦE F ε Fc εc ac adc,
      P d.ordinary ∧ Q d.restriction := by
  let b := exactComparison L F ε
  let bc := exactComparison Lc Fc εc
  let δ : DerivedCategory.Q ⋙ F ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q b ≪≫ L.mapDerivedCategoryFactors
  let : CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
    DerivedCategory.Q F := ⟨δ.symm⟩
  let : CatCommSq (U.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
    DerivedCategory.Q U.mapDerivedCategory := ⟨U.mapDerivedCategoryFactors.symm⟩
  let ad := (a.mapHomologicalComplex (.up ℤ)).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso D (.up ℤ)) F U.mapDerivedCategory
  have hd (K : CochainComplex C ℤ) : δ.hom.app K =
      Scheme.reductionComplexCounit L F ε K :=
    (exactComparison_complex L F ε K).symm
  have hunit (K : CochainComplex C ℤ) :
      ad.unit.app (DerivedCategory.Q.obj K) ≫
        U.mapDerivedCategory.map (Scheme.reductionComplexCounit L F ε K) ≫
        U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
    rw [← hd]
    dsimp only [ad]
    rw [Adjunction.localization_unit_app]
    change (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      U.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
      U.mapDerivedCategory.map (δ.inv.app K)) ≫ U.mapDerivedCategory.map (δ.hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) = _
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [U.mapDerivedCategory.map_id]
    simp only [Category.id_comp]
    erw [Iso.inv_hom_id_app, Category.comp_id]
  let de : Fc ⋙ ΦE.functor.mapDerivedCategory ≅ ΦA.functor.mapDerivedCategory ⋙ F :=
    Functor.isoWhiskerRight bc ΦE.functor.mapDerivedCategory ≪≫
      Functor.mapDerivedCategorySquareIso α ≪≫
      Functor.isoWhiskerLeft ΦA.functor.mapDerivedCategory b.symm
  have hde (K : CochainComplex A ℤ) :
      ΦE.functor.mapDerivedCategory.map (Scheme.reductionComplexCounit Lc Fc εc K) ≫
        ΦE.functor.mapDerivedCategoryFactors.hom.app
          ((Lc.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app K) =
      de.hom.app (DerivedCategory.Q.obj K) ≫
        F.map (ΦA.functor.mapDerivedCategoryFactors.hom.app K) ≫
        Scheme.reductionComplexCounit L F ε
          ((ΦA.functor.mapHomologicalComplex (.up ℤ)).obj K) := by
    rw [exactComparison_complex Lc Fc εc, exactComparison_complex L F ε]
    dsimp only [de]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
    rw [← b.inv.naturality_assoc]
    erw [Iso.inv_hom_id_app_assoc]
    have hs := squareComplex L Lc ΦA.functor ΦE.functor α K
    dsimp only [Functor.mapDerivedCategorySquareIso] at hs
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] at hs
    erw [hs]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  -- Transport the canonical exact-functor shift and triangulated structure.
  let : F.CommShift ℤ := Functor.CommShift.ofIso b.symm ℤ
  have : NatTrans.CommShift b.symm.hom ℤ := Functor.CommShift.ofIso_compatibility b.symm ℤ
  have : F.IsTriangulated := Functor.isTriangulated_of_iso b.symm
  refine ⟨{ extensionLimits := inferInstance
            extensionColimits := inferInstance
            internalLimits := inferInstance
            internalColimits := inferInstance
            integralAdditive := inferInstance
            fieldAdditive := inferInstance
            integralDerivedEquivalence := inferInstance
            fieldDerivedEquivalence := inferInstance
            ordinary := a
            extension := α
            restriction := ρ
            ordinaryUnit := hu
            comparison := b
            comparisonCounit := exactComparison_fac L F ε
            internalComparison := bc
            internalComparisonCounit := exactComparison_fac Lc Fc εc
            commShift := inferInstance
            commShift_eq := rfl
            triangulated := inferInstance
            derivedExtension := de
            derivedExtensionComplex := hde
            adjunction := ad
            unit := hunit
            internalUnit := hic }, ha, hρ⟩

end DerivedAssembly

section InternalUnit

attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem internalDerivedUnit
    {C : Type uA} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type uB} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (L : C ⥤ D) (U : D ⥤ C) [L.Additive] [U.Additive] [L.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : L ⊣ U) (K : CochainComplex C ℤ) :
    let ad := a.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    ad.unit.app (DerivedCategory.Q.obj K) ≫
      U.mapDerivedCategory.map (Scheme.reductionComplexCounit L L.leftDerivedFunctor
        L.leftDerivedFunctorCounit K) ≫
      U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  dsimp only
  rw [complexCounit_eq]
  have h := CategoryTheory.derived_unit_cochain L U a K
  dsimp only at h
  rw [← Category.assoc]
  erw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]


private theorem scalarDerivedUnit
    {C : Type uA} [Category.{u + 1} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (K : CochainComplex (Mod C R) ℤ) :
    let L := Mod.extendScalars φ
    let U := Mod.comap φ
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Q.obj K) ≫
      U.mapDerivedCategory.map (Scheme.reductionComplexCounit L L.leftDerivedFunctor
        L.leftDerivedFunctorCounit K) ≫
      U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map
      (((Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).unit.app K) := by
  exact internalDerivedUnit (C := Mod C R) (D := Mod C S)
    (Mod.extendScalars φ) (Mod.comap φ) (Mod.extendRestrictAdjunction φ) K

end InternalUnit

attribute [local irreducible] Scheme.reductionChange Scheme.reductionDerivedChange
attribute [local irreducible] Scheme.reductionDerivedCounit
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
attribute [local irreducible] Functor.mapDerivedCategory

/-- The continuous scalar square for the actual integral inclusion and the specified
internal-to-sectionwise encodings. Completion is understood via the canonical quotient
projections, so the sectionwise integral ring is B_T = A_T.
Source: Bhatt--Scholze, Lemma 6.8.2(1),(2); Stacks Tags 03EK, 015F and 07A6
(blueprint: lem-weil-pbc-continuous-scalar-derived-encoding).

Proof:
1. The continuous coefficient completion and localization comparisons identify B_T with
A_T and E_T with A_T[1/varpi], preserving quotient maps and coefficient inclusion
(lem-weil-pbc-continuous-coefficients-immersion-restriction). Coefficient naturality of
lem-weil-pbc-continuous-coefficient-realizations identifies the internal inclusion.
2. Apply lem-weil-pbc-scalar-localization-sheaf-exact to the constant uniformizer and
lem-pur-sheaf-ring-coefficient-ordinary-adjunction to this ring map. Extension and
restriction are additive and exact; the ordinary unit sends m to 1 tensor m.
3. Apply lem-sfb-internal-section-scalar-adjunction and compose its reconstruction with
both chart restrictions of def-weil-pbc-continuous-coefficient-module-encoding.
The resulting extension and restriction comparisons preserve balanced generators and
ordinary units; exactness transports through these equivalences to internal modules.
4. Apply lem-weil-pbc-exact-functor-derived-factorization and
lem-weil-pbc-exact-functor-derived-functor. Uniqueness of universal derived pairs
identifies the actual derived extensions with the termwise functors on all complexes.
Transport the termwise shift comparison; preservation of distinguished triangles follows.
5. Localize the ordinary extension comparison using lem-sfb-exact-derived-natural-iso
and lem-sfb-exact-derived-composition. Its components are exactly the localized
termwise comparison, and the localized encodings remain equivalences.
6. Apply lem-pur-sheaf-ring-derived-coefficient-adjunction on a flat-term K-flat
resolution P to K, supplied by lem-pc-kflat-resolution. Naturality of the derived counit
and unit gives the ordinary unit equation after Q(P to K); cancel this invertible map.
Exactness makes extension of the resolution a quasi-isomorphism. This proves the unit
formula for every complex K, without boundedness, constructibility or completeness.
7. The specified adjunction of def-weil-exact-derived-adjunction is the localization of
the ordinary one. The normalized internal/sectionwise adjunction comparison carries
the internal unit to the sectionwise unit. Apply step 6 internally and compose with the
chart restrictions, which preserve 1 tensor m, to obtain the same all-complex equation. -/
theorem continuousScalarDerivedEncoding (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) [IsNoetherian X] :
    ∃ d : ContinuousScalarDerivedEncodingData
      (Scheme.reductionChange X (lisseIntegerToField ℓ E X))
      (Scheme.reductionRestrict X (lisseIntegerToField ℓ E X))
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X))
      (Mod.comap (coefficientMap (integralScalarMap ℓ E) X))
      (continuousIntegerModuleEquivalence ℓ E X) (continuousFieldModuleEquivalence ℓ E X)
      (Scheme.reductionDerivedChange X (lisseIntegerToField ℓ E X))
      (Scheme.reductionDerivedCounit X (lisseIntegerToField ℓ E X))
      (integralScalarExtension ℓ E X)
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).leftDerivedFunctorCounit
      (Mod.extendRestrictAdjunction (coefficientMap (integralScalarMap ℓ E) X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (integralScalarMap ℓ E) X)),
    (∀ (M : Scheme.reductionModules X (lisseIntegerSheaf ℓ E X))
      (V : X.ProEtᵒᵖ) (m : M.val.obj V),
      (d.ordinary.unit.app M).val.app V m =
        Scheme.reductionTensorSection X (lisseIntegerToField ℓ E X) M V 1 m) ∧
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (V : X.ProEtᵒᵖ) (x : N.X.obj.obj V),
      (d.restriction.hom.app N).val.app V x = x := by
  let C₀ := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let : Category.{u + 1} C₀ := inferInstance
  let : Abelian C₀ := inferInstance
  let : MonoidalCategory C₀ := inferInstance
  let : SymmetricCategory C₀ := inferInstance
  let : MonoidalClosed C₀ := inferInstance
  have : MonoidalPreadditive C₀ := inferInstance
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) X)
  let B := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj E) X)
  let : Category.{u + 1} A := inferInstance
  let : Category.{u + 1} B := inferInstance
  let : Abelian A := inferInstance
  let : Abelian B := inferInstance
  let : MonoidalCategory A := inferInstance
  let : SymmetricCategory A := inferInstance
  let : MonoidalClosed A := inferInstance
  have : MonoidalPreadditive A := inferInstance
  have : IsGrothendieckAbelian.{u + 1} A := inferInstance
  have : IsGrothendieckAbelian.{u + 1} B := inferInstance
  have : Abelian.HasFunctorialFlatResolution A := inferInstance
  let : HasDerivedCategory.{u + 1} A := inferInstance
  let : HasDerivedCategory.{u + 1} B := inferInstance
  let L := Scheme.reductionChange X (lisseIntegerToField ℓ E X)
  let U := Scheme.reductionRestrict X (lisseIntegerToField ℓ E X)
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let Lc : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X) := Mod.extendScalars φ
  let Uc : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X) := Mod.comap φ
  let ΦA := continuousIntegerModuleEquivalence ℓ E X
  let ΦE := continuousFieldModuleEquivalence ℓ E X
  let ac : Lc ⊣ Uc := Mod.extendRestrictAdjunction φ
  let adc := Mod.derivedExtendMapDerivedCategoryAdjunction
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  let a := (ordinaryScalar X (lisseIntegerToField ℓ E X)).choose
  have ha := (ordinaryScalar X (lisseIntegerToField ℓ E X)).choose_spec
  let ρ := (spectralRestriction ℓ E X).choose
  have hρ := (spectralRestriction ℓ E X).choose_spec
  let τ := ((mateEquiv ac a).symm (TwoSquare.mk _ _ _ _ ρ.hom)).natTrans
  have : IsIso τ := inverseMateIso ac a ρ
  let α := (asIso τ).symm
  have hu := inverseMateUnit ac a ρ
  have : PreservesFiniteLimits Lc := integralScalarExtension_exact ℓ E X
  have : PreservesFiniteColimits Lc := inferInstance
  have : PreservesFiniteLimits L := exactTransfer ΦA ΦE Lc L α
  have : PreservesColimitsOfSize.{0, 0} L := a.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L := inferInstance
  have : ΦA.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : ΦE.functor.Additive := Functor.additive_of_preserves_binary_products _
  have hic := scalarDerivedUnit (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  -- Assemble the normalized ordinary and derived data.
  exact assembleDerived L U Lc Uc ΦA ΦE
    (Scheme.reductionDerivedChange X (lisseIntegerToField ℓ E X))
    (Scheme.reductionDerivedCounit X (lisseIntegerToField ℓ E X))
    (integralScalarExtension ℓ E X) Lc.leftDerivedFunctorCounit ac
    adc a α ρ hu hic
    (P := fun a ↦ ∀ (M : Scheme.reductionModules X (lisseIntegerSheaf ℓ E X))
      (V : X.ProEtᵒᵖ) (m : M.val.obj V),
      (a.unit.app M).val.app V m =
        Scheme.reductionTensorSection X (lisseIntegerToField ℓ E X) M V 1 m)
    (Q := fun r ↦ ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (V : X.ProEtᵒᵖ) (x : N.X.obj.obj V), (r.hom.app N).val.app V x = x) ha hρ

end AlgebraicGeometry.ProEtale.CondensedRing
