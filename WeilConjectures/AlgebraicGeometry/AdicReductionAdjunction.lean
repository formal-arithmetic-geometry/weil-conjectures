/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletionMap
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsGeneral
import WeilConjectures.Algebra.Homology.KFlatResolutionGeneral

/-! # The canonical derived reduction Hom equivalence

Source: blueprint proper base change, order 1260, proof step 6.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv).
-/

@[expose] public section
set_option autoImplicit false

universe t
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

-- The imported adjunction specializes its site-size instance to another coefficient universe.
-- Keep that instance out of this proof; the site here already has size t + 1.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of scalars is exact, also when the small site's object and morphism
universes differ. Source: order 1260, proof step 6; Stacks Tag 03D3.
Proof: restriction leaves the underlying abelian sheaf unchanged. Kernels and cokernels
are computed on those sheaves, with the restricted action, so it preserves both.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicRestrictScalars_exact (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) := by
  let F := SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)
  let UA := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X A)
  let UB := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X B)
  have hs : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have hw : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have : PreservesFiniteColimits UA :=
    @SheafOfModules.preservesFiniteColimits_toSheaf.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) _ hs hw
  have : PreservesFiniteColimits UB :=
    @SheafOfModules.preservesFiniteColimits_toSheaf.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) _ hs hw
  have : PreservesFiniteLimits (F ⋙ UA) :=
    inferInstanceAs (PreservesFiniteLimits UB)
  have : PreservesFiniteColimits (F ⋙ UA) :=
    inferInstanceAs (PreservesFiniteColimits UB)
  have : ReflectsFiniteColimits UA :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F UA,
    preservesFiniteColimits_of_reflects_of_preserves F UA⟩

/-- Exact derived restriction along the constant coefficient map.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicDerivedRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory X A :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X A))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapDerivedCategory

/-- The canonical factorization of derived restriction through termwise restriction.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicDerivedRestrictFactors (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :
    (adicDerivedRestrict X φ).obj ((adicLocalization X B).obj P) ≅
      (adicLocalization X A).obj (adicRestrict X φ P) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X A))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapDerivedCategoryFactors.app P

/-- The unit L → Res(L tensor P_(n+1)), with its canonical tensor-generator formula.
Source: order 1260, adjunction in proof step 6
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionDerivedUnit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ) :
    L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj
      (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩) :=
  N.realization.inv ≫ (adicLocalization X Λ).map (adicReductionAugmentation X d N n) ≫
    (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) N.complex)).inv

set_option linter.style.haveILetI false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived change-of-rings construction supplies the canonical Hom equivalence and
the displayed unit formula. Use the generic tensor--restriction adjunction and its derived
unit compatibility, resolve homotopy objects by K-flat complexes, and transport the resulting
Hom equivalence along the chosen realization. The tensor-unit formula identifies the ordinary
complex unit with the unique quotient augmentation, so the derived unit is
`adicReductionDerivedUnit`.
Source: order 1260, proof step 6 (blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionAdjunction_homEquiv_exists (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    ∃ e : (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H),
      ∀ f, e f = adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f := by
  classical
  have hs : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have hw : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X Λ))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{t + 1} (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))))
  let φ := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let A := SheafOfModules.{t + 1} (adicModuleRing X Λ)
  let B := SheafOfModules.{t + 1} (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1)))
  let R : B ⥤ A := SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  obtain ⟨E, hE, hmE, hAdd, _, _, LF, ε, hLF, _, hε⟩ :=
    SheafOfModules.derivedChangeOfRingsGeneral (adicConstantMap X φ)
  letI := hAdd
  obtain ⟨adj, hadj⟩ :=
    SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications
      (adicConstantMap X φ) E hE hmE
  have hres : ∀ G : HomotopyCategory A (.up ℤ),
      ∃ (P : HomotopyCategory A (.up ℤ)) (s : P ⟶ G),
        IsIso (ε.app P) ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro G
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective G
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionGeneral (R := adicConstantRing X Λ) G
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, hε P hP,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  obtain ⟨adjD, hunit⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    E R adj LF ε hLF hres
  let eC : (E.mapHomologicalComplex (.up ℤ)).obj N.complex ≅
      adicChange X φ N.complex :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (hE (N.complex.X i))) (by
      intro i j hij
      change eqToHom (hE (N.complex.X i)) ≫
          SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (N.complex.d i j) =
        E.map (N.complex.d i j) ≫ eqToHom (hE (N.complex.X j))
      rw [hmE]
      simp)
  let qN := (HomotopyCategory.quotient A (.up ℤ)).obj N.complex
  letI := hε N.complex N.isKFlat
  let EC := (E.mapHomologicalComplex (.up ℤ)).obj N.complex
  let eps : LF.obj (DerivedCategory.Qh.obj qN) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj EC) := ε.app qN
  let u : LF.obj (DerivedCategory.Qh.obj qN) ≅ adicReduction X d N ⟨n + 1,
      Nat.succ_pos n⟩ :=
    asIso eps ≪≫
      (DerivedCategory.quotientCompQhIso B).app
        ((E.mapHomologicalComplex (.up ℤ)).obj N.complex) ≪≫
      (adicLocalization X _).mapIso eC
  let v : DerivedCategory.Qh.obj qN ≅ L :=
    (DerivedCategory.quotientCompQhIso A).app N.complex ≪≫ N.realization
  let e := (Iso.homCongr u (Iso.refl H)).symm.trans
    ((adjD.homEquiv _ H).trans (Iso.homCongr v (Iso.refl _)))
  refine ⟨e, ?_⟩
  intro f
  change (Iso.homCongr v (Iso.refl _))
    (adjD.homEquiv _ H ((Iso.homCongr u (Iso.refl H)).symm f)) = _
  simp only [Iso.homCongr_apply, Iso.homCongr_symm, Iso.symm_inv, Iso.symm_hom,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  suffices h : v.inv ≫ adjD.unit.app (DerivedCategory.Qh.obj qN) ≫
      R.mapDerivedCategory.map u.hom = adicReductionDerivedUnit X d N n by
    change v.inv ≫ adjD.unit.app (DerivedCategory.Qh.obj qN) ≫
        R.mapDerivedCategory.map u.hom ≫ R.mapDerivedCategory.map f =
      adicReductionDerivedUnit X d N n ≫ R.mapDerivedCategory.map f
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ R.mapDerivedCategory.map f) h
  let ηC : N.complex ⟶ (R.mapHomologicalComplex (.up ℤ)).obj EC :=
    (adj.mapHomologicalComplex (.up ℤ)).unit.app N.complex
  have hAug : ηC ≫ (R.mapHomologicalComplex (.up ℤ)).map eC.hom =
      adicReductionAugmentation X d N n := by
    apply (Classical.choose_spec (adicReductionAugmentation_exists X d N n)).2
    intro p U m
    change (eC.hom.f p).val.app U ((ηC.f p).val.app U m) = _
    dsimp only [ηC]
    erw [Adjunction.mapHomologicalComplex_unit_app_f]
    change (eqToHom (hE (N.complex.X p))).val.app U
      ((adj.unit.app (N.complex.X p)).val.app U m) = _
    rw [hadj]
    change (eqToHom (hE (N.complex.X p))).val.app U
      ((eqToHom (hE (N.complex.X p)).symm).val.app U _) = _
    change ((eqToHom (hE (N.complex.X p)).symm ≫
      eqToHom (hE (N.complex.X p))).val.app U) _ = _
    simp only [eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply]
    rfl
  let fh : R.mapDerivedCategory.obj (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient B (.up ℤ)).obj EC)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj EC)) :=
    R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient B (.up ℤ)).obj EC)
  let fD : R.mapDerivedCategory.obj (DerivedCategory.Q.obj EC) ⟶
      DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj EC) :=
    R.mapDerivedCategoryFactors.hom.app EC
  have hfac : R.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso B).hom.app EC) ≫
        R.mapDerivedCategoryFactors.hom.app EC =
      fh ≫
        (DerivedCategory.quotientCompQhIso A).hom.app
          ((R.mapHomologicalComplex (.up ℤ)).obj EC) := by
    dsimp only [fh]
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change R.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj EC)) ≫ fD =
      (R.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj EC)) ≫ fD ≫
        𝟙 (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj EC)) ≫
        (DerivedCategory.Qh (C := A)).map
          (𝟙 ((HomotopyCategory.quotient A (.up ℤ)).obj
            ((R.mapHomologicalComplex (.up ℤ)).obj EC)))) ≫
      𝟙 (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj EC))
    have hq : (DerivedCategory.Qh (C := A)).map
        (𝟙 ((HomotopyCategory.quotient A (.up ℤ)).obj
          ((R.mapHomologicalComplex (.up ℤ)).obj EC))) =
        𝟙 (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj EC)) :=
      CategoryTheory.Functor.map_id _ _
    rw [hq, CategoryTheory.Functor.map_id]
    simp only [Category.comp_id]
    exact (Category.comp_id _).symm
  have hu := hunit qN
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hu
  change adjD.unit.app (DerivedCategory.Qh.obj qN) ≫
      R.mapDerivedCategory.map eps ≫ fh =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map ηC) at hu
  have hu' : adjD.unit.app (DerivedCategory.Qh.obj qN) ≫
      R.mapDerivedCategory.map u.hom ≫
        R.mapDerivedCategoryFactors.hom.app (adicChange X φ N.complex) =
      (DerivedCategory.quotientCompQhIso A).hom.app N.complex ≫
        (adicLocalization X Λ).map (adicReductionAugmentation X d N n) := by
    change adjD.unit.app (DerivedCategory.Qh.obj qN) ≫
        R.mapDerivedCategory.map (eps ≫
          (DerivedCategory.quotientCompQhIso B).hom.app EC ≫
            DerivedCategory.Q.map eC.hom) ≫
        R.mapDerivedCategoryFactors.hom.app (adicChange X φ N.complex) =
      (DerivedCategory.quotientCompQhIso A).hom.app N.complex ≫
        DerivedCategory.Q.map (adicReductionAugmentation X d N n)
    simp only [Functor.map_comp, Category.assoc]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality]
    rw [reassoc_of% hfac]
    rw [← Category.assoc (R.mapDerivedCategory.map eps),
      ← Category.assoc (adjD.unit.app (DerivedCategory.Qh.obj qN)), hu]
    rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
    simp only [← Functor.map_comp]
    rw [hAug]
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
    (adicChange X φ N.complex))).1
  simp only [Category.assoc]
  rw [hu']
  dsimp only [v, Iso.trans_inv, adicReductionDerivedUnit, adicDerivedRestrictFactors]
  change (N.realization.inv ≫
      (DerivedCategory.quotientCompQhIso A).inv.app N.complex) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app N.complex ≫
          (adicLocalization X Λ).map (adicReductionAugmentation X d N n) =
      (N.realization.inv ≫
        (adicLocalization X Λ).map (adicReductionAugmentation X d N n) ≫
          R.mapDerivedCategoryFactors.inv.app (adicChange X φ N.complex)) ≫
            R.mapDerivedCategoryFactors.hom.app (adicChange X φ N.complex)
  simp only [Category.assoc, Iso.inv_hom_id_app]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, Category.comp_id]

/-- The unit formula is bijective because it is the canonical Hom equivalence supplied by
the preceding derived change-of-rings construction. Source: order 1260, proof step 6.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicReductionAdjunction_bijective (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    Function.Bijective (fun f : adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H ↦
      adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f) := by
  obtain ⟨e, he⟩ := adicReductionAdjunction_homEquiv_exists X d N n H
  refine ⟨?_, ?_⟩
  · intro f g h
    apply e.injective
    calc
      e f = _ := he f
      _ = _ := h
      _ = e g := (he g).symm
  · intro g
    obtain ⟨f, hf⟩ := e.surjective g
    refine ⟨f, ?_⟩
    change adicReductionDerivedUnit X d N n ≫
      (adicDerivedRestrict (X := X)
        (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f = g
    exact (he f).symm.trans hf

/-- The canonical Hom equivalence, rather than an arbitrary choice of adjunction.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionHomEquiv (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H) :=
  Equiv.ofBijective _ (adicReductionAdjunction_bijective X d N n H)

/-- Reduction on a derived morphism, characterized by the naturality of the scalar unit.
Source: order 1260, functoriality in proof step 6
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K') (n : ℕ) (f : K ⟶ K') :
    adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ ⟶
      adicReduction X d M' ⟨n + 1, Nat.succ_pos n⟩ :=
  (adicReductionHomEquiv X d M n _).symm (f ≫ adicReductionDerivedUnit X d M' n)


/-- The defining scalar-unit square of reduction on derived morphisms.
Source: blueprint order 1260, step 6; apply the canonical Hom equivalence to its inverse.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_unit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K L : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ L) (n : ℕ) (f : K ⟶ L) :
    adicReductionDerivedUnit X d M n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map
          (adicReductionMap X d M N n f) = f ≫ adicReductionDerivedUnit X d N n :=
  (adicReductionHomEquiv X d M n _).apply_symm_apply _

/-- Reduction respects composition, independently of the chosen K-flat models.
Source: blueprint order 1260, step 6; apply the Hom equivalence and its unit square twice.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_comp (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K L H : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ L)
    (P : AdicKFlatModel X Λ H) (n : ℕ) (f : K ⟶ L) (g : L ⟶ H) :
    adicReductionMap X d M P n (f ≫ g) =
      adicReductionMap X d M N n f ≫ adicReductionMap X d N P n g := by
  apply (adicReductionHomEquiv X d M n _).injective
  change adicReductionDerivedUnit X d M n ≫
      (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map
        (adicReductionMap X d M P n (f ≫ g)) =
    adicReductionDerivedUnit X d M n ≫
      (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map _
  rw [adicReductionMap_unit]
  rw [Functor.map_comp, ← Category.assoc, adicReductionMap_unit]
  simp only [Category.assoc]
  rw [adicReductionMap_unit]

/-- Reduction respects identities.
Source: blueprint order 1260, step 6; the identity has the required unit square.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_id (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ) :
    adicReductionMap X d M M n (𝟙 K) = 𝟙 _ := by
  apply (adicReductionHomEquiv X d M n _).injective
  change adicReductionDerivedUnit X d M n ≫
      (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map
        (adicReductionMap X d M M n (𝟙 K)) =
    adicReductionDerivedUnit X d M n ≫
      (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map (𝟙 _)
  rw [adicReductionMap_unit, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]

/-- Reduction takes isomorphisms to isomorphisms.
Source: blueprint order 1260, step 6; reduce an inverse and use composition and identities.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_isIso (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K L : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ L) (n : ℕ)
    (f : K ⟶ L) [IsIso f] : IsIso (adicReductionMap X d M N n f) := by
  refine ⟨⟨adicReductionMap X d N M n (inv f), ?_, ?_⟩⟩
  · rw [← adicReductionMap_comp, IsIso.hom_inv_id, adicReductionMap_id]
  · rw [← adicReductionMap_comp, IsIso.inv_hom_id, adicReductionMap_id]

end AlgebraicGeometry.Scheme
