/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.Paper.IntegralCriterionReductions
import Sheaf.Paper.IntegralLfpConstantModelComparison
import all Sheaf.Paper.IntegralConstantModelHeartClosure
import all Sheaf.Paper.ContinuousIntegralConstructibleComparison
import Sheaf.Paper.IntegralSectionLocalModels
import Sheaf.Paper.ContinuousIntegralCoefficientComparison
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Sheaf.CategoryTheory.SectionActionInternal

/-! # Constructibility under continuous integral section encoding

Source: Bhatt--Scholze, Definition 6.8.10; Stacks Project, Tag 00YV.
(blueprint: lem-weil-pbc-integral-continuous-encoding-constructible)
-/

@[expose] public section
set_option autoImplicit false
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  Scheme.integralDetailedCoefficientComparison



attribute [local instance 100000] Sheaf.monoidalCategory Sheaf.braidedCategory

private theorem ring_map_isMonHom (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (f : R ⟶ S) :
    IsMonHom ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f) := by
  set_option backward.isDefEq.respectTransparency true in
    exact Sheaf.isMonHom_sheafCompose_map.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) f

private noncomputable def pointIntegerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCondensedRing l E) ≅ Mon.mk (DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e : latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l E :=
    RingEquiv.restrict (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E))
      _ _ (fun _ ↦ Iff.rfl)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hi : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let c : Profinite.continuousMapRingSheafOfUniverse (latticeCoefficientIntegers l E) ≅
      DerivedNakayama.integerRingSheaf l E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let cAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso c
  have : IsMonHom cAb.hom := Sheaf.isMonHom_sheafCompose_map _ c.hom
  have : IsMonHom cAb.inv := Sheaf.isMonHom_sheafCompose_map _ c.inv
  exact
    { hom := Mon.ofHom cAb.hom
      inv := Mon.ofHom cAb.inv
      hom_inv_id := by apply Mon.Hom.ext; exact cAb.hom_inv_id
      inv_hom_id := by apply Mon.Hom.ext; exact cAb.inv_hom_id }

attribute [local irreducible] pointIntegerIso

private theorem integral_internal_constant_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [EssentiallySmall.{u + 1} X.ProEt] [IsNoetherian X]
    (M : AdicCompletion.Modules l E X)
    (hM : IsConstructibleModuleObject (AdicCompletion.ring l E X) M) :
    IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M := by
  let e := pointIntegerIso l E
  let φ := e.hom.hom
  let ψ := coefficientMap φ X
  have h := integralLfpConstantModelComparison l E X ((Mod.comap ψ).obj M)
  exact (constantModel_comap_iff φ X M).mp
    (h.mp (_root_.constructible_comap ψ hM))

private theorem normalized_transport {C : Type*} [Category C]
    {A B D Z : C} (d : A ⟶ B) (di : B ⟶ A)
    (p : B ⟶ Z) (q : Z ⟶ B) (r : A ⟶ D)
    (hd : d ≫ di = 𝟙 A) (hp : p ≫ q = 𝟙 B) :
    d ≫ p ≫ (q ≫ (di ≫ r)) = r := by
  rw [← Category.assoc p, hp, Category.id_comp, ← Category.assoc, hd, Category.id_comp]

private theorem sectionRingMap_underlying (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (CondensedRing.sectionRingMap X φ)) = φ := by
  rfl

private theorem reconstructedRingIso_underlying (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (CondensedRing.reconstructedRingIso X R).inv = 𝟙 _ := by
  rfl

private theorem map_inv_normalized
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} (e : A ≅ B) (q : F.obj A ⟶ F.obj B)
    (h : F.map e.hom = q) : F.map e.inv ≫ q = 𝟙 (F.obj B) := by
  rw [← h]
  exact (F.mapIso e).inv_hom_id

private noncomputable def transport_chain_iso
    (X : Scheme.{u}) {R₀ R₁ R₂ S₀ S₁ S₂ S₃ S₄ :
      Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    (α : R₀ ⟶ R₁) (β : R₁ ⟶ R₂) (γ : R₂ ⟶ S₄)
    (c₀ : R₀ ≅ S₀) (c₁ : S₀ ≅ S₁) (c₂ : S₁ ≅ S₂)
    (c₃ : S₂ ≅ S₃) (ε : S₃ ⟶ S₄)
    (h : α ≫ β ≫ γ = c₀.hom ≫ c₁.hom ≫ c₂.hom ≫ c₃.hom ≫ ε)
    (M : SheafOfModules.{u + 1} S₄) :
    (SheafOfModules.restrictScalars α).obj
      ((SheafOfModules.restrictScalars β).obj
        ((SheafOfModules.restrictScalars γ).obj M)) ≅
    (CondensedRing.ringModuleEquivalenceOfIso X c₀).functor.obj
      ((CondensedRing.ringModuleEquivalenceOfIso X c₁).functor.obj
        ((CondensedRing.ringModuleEquivalenceOfIso X c₂).functor.obj
          ((CondensedRing.ringModuleEquivalenceOfIso X c₃).functor.obj
            ((SheafOfModules.restrictScalars ε).obj M)))) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext m
    have hr := congrArg
      (fun g : R₀ ⟶ S₄ ↦ (g.hom.app U).hom r) h
    change (ε.hom.app U (c₃.hom.hom.app U (c₂.hom.hom.app U
      (c₁.hom.hom.app U (c₀.hom.hom.app U r))))) • (show M.val.obj U from m) =
      (γ.hom.app U (β.hom.app U (α.hom.app U r))) • (show M.val.obj U from m)
    exact congrArg (fun t ↦ t • (show M.val.obj U from m)) hr.symm
  · intro U V g
    ext m
    rfl

/-- Integral constructibility is preserved by section-action reconstruction and a
coefficient-ring isomorphism. No rationalization or lattice-existence assertion is
involved. The coefficient isomorphism need not preserve chosen scalar coordinates:
a finite presentation is invariant under arbitrary coefficient isomorphisms, and
the integral finite-local-presentation criterion supplies scalar local models.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3); Stacks 00YV.
(blueprint: lem-weil-pbc-integral-continuous-encoding-constructible).

Proof in words. Identify the two condensed integral point rings by postcomposing
continuous functions with the WithAbs valuation-ring equivalence. Transport M to
the derived integer coefficient ring by the normalized completed section-ring
comparison, the detailed completed coefficient comparison, c and the chart
comparison. Constructibility is invariant under this coefficient isomorphism.
The integral local-finite-presentation/constant-model theorem gives constant local
models, and integralSectionLocalModels transports them to completed sectionwise
models. Compare this sectionwise module with the continuous encoding in the
statement: sectionModuleComapIso supplies the two section-action comparisons;
the intervening map is identity on sections, and its linearity is the normalized
coefficient identity with the inverse coefficient maps cancelled. Transport the
stratified completed models along that isomorphism. On each stratum,
continuousIntegralSliceModelComparison gives the continuous scalar models;
replace the covering sieve by its generating covering family. Keep the finite
stratification. Empty covers and zero presentations give the empty and rank-zero
cases. -/
theorem integralContinuousEncoding_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (X : Scheme.{u}) [IsNoetherian X]
    (c : latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      lisseIntegerSheaf l K X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff l K) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (CondensedRing.integralCoeff l K) X) M) :
    IsContinuousConstructible X (latticeCoefficientIntegers l E)
      ((CondensedRing.ringModuleEquivalenceOfIso X
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)).functor.obj
        ((CondensedRing.continuousIntegerModuleEquivalence l K X).functor.obj M)) := by
  classical
  have : EssentiallySmall.{u + 1} X.ProEt := CategoryTheory.essentiallySmallSelf.{0} X.ProEt
  let J := Scheme.ProEt.topology X
  let : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : TotallyDisconnectedSpace K := inferInstance
  let f : Sheaf J CommRingCat.{u + 1} ⥤ Sheaf J RingCat.{u + 1} :=
    sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let b : Sheaf J RingCat.{u + 1} ⥤ Sheaf J Ab.{u + 1} :=
    sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})
  obtain ⟨s, c₀, hc₀⟩ := continuousIntegralCoefficientComparison X l E
  let d : (Scheme.adicLisseForget X).obj
      (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)) ≅
      WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E X :=
    Scheme.integralDetailedCoefficientComparison.{u} X l E
  let δ : f.obj (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      J (AdicCompletion.ring l E X)) ≅
      WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E X :=
    f.mapIso (integralSectionRingIso l E X)
  let cp := eqToIso (congrArg (coefficientRing X) (integralPointMon_eq l E))
  have ha : IsMonHom (integralLimitAbComparison l E X).hom :=
    (integralLimitAbComparison_existsUnique l E X).exists.choose_spec.1
  let := ha
  let am := cp ≪≫ Mon.mkIso' (integralLimitAbComparison l E X)
  let ac : AdicCompletion.ring l E X ≅ sfbCompletedIntegersAb l E X :=
    (Mon.forget _).mapIso am
  have hac : IsMonHom ac.hom := am.hom.isMonHom_hom
  let := hac
  let k := (eqToIso (CondensedRing.lisseIntegerSheaf_eq l K X))
  let chart := asIso (chartComparison X (CondensedRing.continuousIntegers l K))
  let w := b.mapIso d.symm ≪≫ b.mapIso (f.mapIso c₀) ≪≫
    b.mapIso (f.mapIso c) ≪≫ b.mapIso (f.mapIso k) ≪≫ chart.symm
  have hw : IsMonHom w.hom := by
    dsimp only [w, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    have : IsMonHom (b.map d.inv) := ring_map_isMonHom X d.inv
    have : IsMonHom (b.map (f.map c₀.hom)) :=
      ring_map_isMonHom X (f.map c₀.hom)
    have : IsMonHom (b.map (f.map c.hom)) :=
      ring_map_isMonHom X (f.map c.hom)
    have : IsMonHom (b.map (f.map k.hom)) :=
      ring_map_isMonHom X (f.map k.hom)
    infer_instance
  let := hw
  let a : AdicCompletion.ring l E X ≅
      condensedRingObj (CondensedRing.integralCoeff l K) X := ac ≪≫ w
  have haa : IsMonHom a.hom := by
    dsimp only [a, Iso.trans_hom]
    infer_instance
  let := haa
  let N := (Mod.comap a.hom).obj M
  have hN : IsConstructibleModuleObject (AdicCompletion.ring l E X) N :=
    _root_.constructible_comap a.hom hM
  have hconst := integral_internal_constant_models l E X N hN
  have hmodels := (integralSectionLocalModels l E X N).mp hconst
  let Q := (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso c)).functor.obj
    ((CondensedRing.continuousIntegerModuleEquivalence l K X).functor.obj M)
  let B := (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso c₀)).functor.obj Q
  let W := (SheafOfModules.restrictScalars d.hom).obj
    ((integralSectionFunctor l E X).obj N)
  have hn : b.map δ.hom = ac.hom := by
    have hn := (integralSectionRingIso_existsUnique l E X).exists.choose_spec
    change b.map δ.hom = _ at hn
    symm
    dsimp only [ac, am, cp, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
    rw [Functor.map_comp]
    change (Mon.forget (Sheaf J Ab.{u + 1})).map (eqToHom _) ≫ _ = _
    rw [eqToHom_map]
    simp only [eqToHom_refl, Category.comp_id] at hn ⊢
    change eqToHom _ ≫ (integralLimitAbComparison l E X).hom = _
    exact hn.symm
  have hi : b.map δ.inv ≫ ac.hom = 𝟙 _ := by
    set_option backward.isDefEq.respectTransparency true in
      exact map_inv_normalized b δ ac.hom hn
  have hd : b.map d.hom ≫ b.map d.inv = 𝟙 _ := (b.mapIso d).hom_inv_id
  have hs : b.map d.hom ≫ b.map δ.inv ≫
      a.hom = b.map (f.map c₀.hom) ≫ b.map (f.map c.hom) ≫
        b.map (f.map k.hom) ≫ chart.inv := by
    set_option backward.isDefEq.respectTransparency true in
      exact normalized_transport (b.map d.hom) (b.map d.inv) (b.map δ.inv) ac.hom
        (b.map (f.map c₀.hom) ≫ b.map (f.map c.hom) ≫
          b.map (f.map k.hom) ≫ chart.inv) hd hi
  let R := continuousMapRingSheaf X (CondensedRing.continuousIntegers l K)
  let A := b.obj R
  let : IsCommMonObj A := by
    set_option backward.isDefEq.respectTransparency true in
      exact Sheaf.isCommMonObj_sheafCompose_obj J R
        (fun U x y ↦ by exact @mul_comm (ULift C(U.unop.left,
          CondensedRing.continuousIntegers l K)) inferInstance x y)
  let H := SheafOfModules.restrictScalars δ.inv ⋙
    SheafOfModules.restrictScalars d.hom
  let G := (CondensedRing.ringModuleEquivalenceOfIso X
      (CondensedRing.reconstructedRingIso X R).symm).functor ⋙
    (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso k)).functor ⋙
    (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso c)).functor ⋙
    (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso c₀)).functor
  let eA := H.mapIso ((CondensedRing.sectionModuleComapIso X a.hom).app M)
  let eB := G.mapIso ((CondensedRing.sectionModuleComapIso X chart.inv).app M)
  let F := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    J (condensedRingObj (CondensedRing.integralCoeff l K) X)).functor
  let W₁ := H.obj ((SheafOfModules.restrictScalars
    (f.map (CondensedRing.sectionRingMap X a.hom))).obj (F.obj M))
  let B₁ := G.obj ((SheafOfModules.restrictScalars
    (f.map (CondensedRing.sectionRingMap X chart.inv))).obj (F.obj M))
  have hc : d.hom ≫ δ.inv ≫ f.map (CondensedRing.sectionRingMap X a.hom) =
      (f.mapIso c₀).hom ≫ (f.mapIso c).hom ≫ (f.mapIso k).hom ≫
        (CondensedRing.reconstructedRingIso X R).inv ≫
          f.map (CondensedRing.sectionRingMap X chart.inv) := by
    have hγ : b.map (f.map (CondensedRing.sectionRingMap X a.hom)) = a.hom :=
      sectionRingMap_underlying X a.hom
    have hε : b.map (f.map (CondensedRing.sectionRingMap X chart.inv)) = chart.inv :=
      sectionRingMap_underlying X chart.inv
    have hρ : b.map (CondensedRing.reconstructedRingIso X R).inv = 𝟙 _ :=
      reconstructedRingIso_underlying X R
    apply b.map_injective
    simp only [b.map_comp, Functor.mapIso_hom, hγ, hε, hρ]
    exact hs
  have ec : W₁ ≅ B₁ := by
    set_option backward.isDefEq.respectTransparency true in
      exact transport_chain_iso X d.hom δ.inv
        (f.map (CondensedRing.sectionRingMap X a.hom))
        (f.mapIso c₀) (f.mapIso c) (f.mapIso k)
        (CondensedRing.reconstructedRingIso X R).symm
        (f.map (CondensedRing.sectionRingMap X chart.inv)) hc (F.obj M)
  have ecomp : W ≅ B := eA ≪≫ ec ≪≫ eB.symm
  have hB := Scheme.fp_iso X (Scheme.pbcIntegralDatum l E) ecomp hmodels
  obtain ⟨S, hS⟩ := hB
  refine ⟨S, fun i ↦ ?_⟩
  obtain ⟨V, hV, hv⟩ := hS i
  apply (localModels_cover_iff_sieve
    (Scheme.ProEt.topology (S.domain i))
    (latticeModuleRing (S.domain i) (latticeCoefficientIntegers l E))
    (fun P : ModuleCat.{u + 1} (ULift.{u + 1} (latticeCoefficientIntegers l E)) ↦
      Module.FinitePresentation _ P)
    (continuousCoefficientModule (S.domain i) (latticeCoefficientIntegers l E))
    (continuousModulePullback (S.immersion i) (latticeCoefficientIntegers l E) Q)).mpr
  exact ⟨V, hV, fun U g hg ↦
    (continuousIntegralSliceModelComparison X l E s c₀ hc₀
      (S.immersion i) Q U).mpr (hv U g hg)⟩

end AlgebraicGeometry.ProEtale
