/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NH and D4
-/
module

public import Sheaf.Paper.CompletionMap
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Paper.StrictPerfectCoefficientPackage
import Sheaf.Paper.IntrinsicKoszulCompletion
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.KoszulQuotientLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# Reduction of adic completion

Source: Weil conjectures blueprint, proper base change, order 1260,
`lemma-weil-pbc-adic-completion-reduction.md`
(blueprint: lemma-weil-pbc-adic-completion-reduction).

The completion object and its evaluation are those of the landed strict product-cone
construction. Its reduction is computed on an arbitrary K-flat model of that object.
The comparison is defined by the derived scalar adjunction, using its unit, so the
isomorphism assertion concerns the specified evaluation map. Positive level a is n+1.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme

-- The imported adjunction specializes its site-size instance to another coefficient universe.
-- Keep that instance out of this proof; the site here already has size t + 1.
attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
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

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
set_option linter.style.haveILetI false in
/-- Naturality of the exact scalar-restriction localization comparison.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction).
Proof: this is the inverse naturality square of mapDerivedCategoryFactors. -/
private theorem adicDerivedRestrictFactors_naturality (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ}
    (f : P ⟶ Q) :
    (adicLocalization X A).map
        (((SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) ≫ (adicDerivedRestrictFactors X φ Q).inv =
      (adicDerivedRestrictFactors X φ P).inv ≫
        (adicDerivedRestrict X φ).map ((adicLocalization X B).map f) := by
  have : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X A))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  exact (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapDerivedCategoryFactors
    |>.inv.naturality f

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

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
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

/-- Evaluation from the specified strict product-cone limit at level n+1.
Source: order 1260, statement (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionEvaluation (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ) :
    adicCompletionObject X d M ⟶ adicReductionSequence X d M n :=
  (adicLocalization X Λ).map
    (adicCompletionProjection X d M ≫ Pi.π (adicReductionComplex X d M) n)

/-- The adjoint of evaluation, with the quotient coefficient action retained.
Source: order 1260, displayed map (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionReduction (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) :
    adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶
      adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ :=
  (adicReductionHomEquiv X d N n _).symm
    (adicCompletionEvaluation X d M n ≫
      (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv)

/-- The Koszul tower computation gives an isomorphism after exact scalar restriction.
Use the quotient-limit comparison, perfect coefficient package, exact countable products,
and the strict tower homotopy-limit calculation to split the tower into its degree-zero
constant part and contractible shifted parts. Source: order 1260, proof steps 1--5
(blueprint: lem-weil-pbc-adic-completion-reduction-restricted). -/
theorem adicCompletionReduction_restricted_isIso (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) :
    IsIso ((adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map
      (adicCompletionReduction X d M N n)) := by
  sorry

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
set_option linter.style.haveILetI false in
/-- Exact restriction is conservative on the derived categories. Reflect the vanishing of
the cone degree by degree through the exact underlying sheaf functor, using derived
change of rings. Source: order 1260, proof step 6
(blueprint: lem-weil-pbc-adic-derived-restrict-conservative). -/
theorem adicDerivedRestrict_reflectsIsomorphisms (X : Scheme.{t})
    {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∀ {Y Z : proEtaleDerivedCategory X B} (f : Y ⟶ Z),
      IsIso ((adicDerivedRestrict (X := X) (A := A) (B := B) φ).map f) → IsIso f := by
  have hs : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have hw : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  letI : HasDerivedCategory.{t + 2, t + 1, t + 2}
      (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{t + 2, t + 1, t + 2}
      (SheafOfModules.{t + 1} (adicModuleRing X B)) :=
    HasDerivedCategory.standard _
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  let UA := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X A)
  let UB := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X B)
  let F := SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)
  letI : F.Additive := inferInstance
  have hF : F.ReflectsIsomorphisms := by
    have hcomp : (F ⋙ UA).ReflectsIsomorphisms := by
      change UB.ReflectsIsomorphisms
      infer_instance
    letI := hcomp
    exact reflectsIsomorphisms_of_comp F UA
  letI := hF
  intro Y Z f hf
  change IsIso ((F.mapDerivedCategory).map f) at hf
  rw [DerivedCategory.isIso_iff]
  intro i
  have hi : IsIso (F.map ((DerivedCategory.homologyFunctor
      (SheafOfModules.{t + 1} (adicModuleRing X B)) i).map f)) := by
    exact (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) f).2
      (by
        change IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{t + 1} (adicModuleRing X A)) i).map
          ((F.mapDerivedCategory).map f))
        infer_instance)
  exact isIso_of_reflects_iso _ F

set_option linter.style.haveILetI false
/-- Every finite reduction of completion is the original reduction via evaluation's
adjoint. The restricted Koszul calculation and conservativity of exact scalar restriction
imply the unreduced isomorphism (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
theorem adicCompletionReduction_isIso (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) : IsIso (adicCompletionReduction X d M N n) := by
  letI := adicCompletionReduction_restricted_isIso X d M N n
  letI : (adicDerivedRestrict X
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).ReflectsIsomorphisms :=
    ⟨fun f hf ↦ adicDerivedRestrict_reflectsIsomorphisms X
      (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f hf⟩
  exact isIso_of_reflects_iso _ (adicDerivedRestrict X
    (Ideal.Quotient.mk (d.ideal ^ (n + 1))))

/-- Reduction on a derived morphism, characterized by the naturality of the scalar unit.
Source: order 1260, functoriality in proof step 6
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K') (n : ℕ) (f : K ⟶ K') :
    adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ ⟶
      adicReduction X d M' ⟨n + 1, Nat.succ_pos n⟩ :=
  (adicReductionHomEquiv X d M n _).symm (f ≫ adicReductionDerivedUnit X d M' n)

/-- The strict reduction of a chain map between the chosen models.
Source: order 1260, functoriality in proof step 6
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionComplexMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionComplex X d M n ⟶ adicReductionComplex X d M' n :=
  ((SheafOfModules.restrictScalars.{t + 1}
    (adicModuleMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f)

/-- Quotient transitions are natural in the original complex.
Source: order 1260, proof step 6.
Proof: both paths send r tensor m to q(r) tensor f(m). The local tensor generators
characterize the sheaf maps and therefore their chain maps uniquely.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicReductionComplexMap_step (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionComplexMap X d M M' f (n + 1) ≫
        adicReductionComplexStep X d M' n =
      adicReductionComplexStep X d M n ≫ adicReductionComplexMap X d M M' f n := by
  exact adicTransitionComplex_naturality X d.ideal f
    ⟨n + 1 + 1, Nat.succ_pos _⟩ ⟨n + 1, Nat.succ_pos _⟩ (Nat.le_succ _)

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Quotient augmentation commutes with maps of the chosen models.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction).
Proof: naturality of module sheafification applied to the sectionwise tensor map sends
one tensor m to one tensor f(m). The uniquely specified augmentation has that formula. -/
private theorem adicReductionAugmentation_naturality (X : Scheme.{t})
    {Λ : Type t} [CommRing Λ] (d : CompleteCoefficientDatum Λ)
    {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionAugmentation X d M n ≫ adicReductionComplexMap X d M M' f n =
      f ≫ adicReductionAugmentation X d M' n := by
  have : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  ext p U m
  have hM := (Classical.choose_spec (adicReductionAugmentation_exists X d M n)).1 p U m
  have hM' := (Classical.choose_spec (adicReductionAugmentation_exists X d M' n)).1
    p U ((f.f p).val.app U m)
  change (SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (adicConstantMap X
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) (M.complex.X p) (f.f p)).val.app U
      ((adicReductionAugmentation X d M n).f p |>.val.app U m) = _
  dsimp only [adicReductionAugmentation] at ⊢
  rw [hM]
  change _ = ((adicReductionAugmentation X d M' n).f p).val.app U
    ((f.f p).val.app U m)
  dsimp only [adicReductionAugmentation] at ⊢
  rw [hM']
  let φ := adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let a : SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ (M.complex.X p) ⟶
      SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ (M'.complex.X p) :=
    { app := fun W ↦ (ModuleCat.extendScalars (φ.hom.app W).hom).map ((f.f p).val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{t, t + 1, t + 1} φ _ (f.f p) }
  have hn := (PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))).obj)).unit.naturality a
  have hx := congrArg (fun g ↦ g.app U
    ((1 : (adicConstantRing X (Λ ⧸ d.ideal ^ (n + 1))).obj.obj U)
      ⊗ₜ[(adicConstantRing X Λ).obj.obj U, (φ.hom.app U).hom] m)) hn
  change (((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ (M'.complex.X p))).app U
        ((ModuleCat.extendScalars (φ.hom.app U).hom).map ((f.f p).val.app U)
          ((1 : (adicConstantRing X (Λ ⧸ d.ideal ^ (n + 1))).obj.obj U)
            ⊗ₜ[(adicConstantRing X Λ).obj.obj U, (φ.hom.app U).hom] m))) = _ at hx
  erw [ModuleCat.ExtendScalars.map_tmul] at hx
  exact hx.symm

/-- Completion of a model map, using the same product map in both cone coordinates.
Source: order 1260, proof step 6; the strict cone construction at order 1258
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionModelMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) :
    adicCompletionObject X d M ⟶ adicCompletionObject X d M' :=
  (adicLocalization X Λ).map
    (adicCompletionTowerMap X d M M' (adicReductionComplexMap X d M M' f)
      (adicReductionComplexMap_step X d M M' f))

/-- The abstract reduction of a represented morphism is its strict scalar extension.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction).
Proof: apply the defining Hom equivalence. Naturality of the quotient augmentation and
of the exact scalar-restriction comparison identifies the two resulting units. -/
private theorem adicReductionMap_model (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionMap X d M M' n
        (M.realization.inv ≫ (adicLocalization X Λ).map f ≫ M'.realization.hom) =
      (adicLocalization X (Λ ⧸ d.ideal ^ (n + 1))).map
        (adicChangeHom X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f) := by
  apply (adicReductionHomEquiv X d M n _).injective
  simp only [adicReductionMap, Equiv.apply_symm_apply]
  change (M.realization.inv ≫ (adicLocalization X Λ).map f ≫ M'.realization.hom) ≫
      adicReductionDerivedUnit X d M' n =
    adicReductionDerivedUnit X d M n ≫
      (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map _
  dsimp only [adicReductionDerivedUnit]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← adicDerivedRestrictFactors_naturality]
  simp only [← Category.assoc, ← Functor.map_comp]
  congr 2
  exact (adicLocalization X Λ).congr_map
    (adicReductionAugmentation_naturality X d M M' f n).symm

/-- Evaluation on the strict cone commutes with a map of models.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction).
Proof: use the first coordinate formula of adicCompletionTowerMap_exists, compose with
one product projection, and localize. -/
private theorem adicCompletionEvaluation_naturality (X : Scheme.{t})
    {Λ : Type t} [CommRing Λ] (d : CompleteCoefficientDatum Λ)
    {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicCompletionModelMap X d M M' f ≫ adicCompletionEvaluation X d M' n =
      adicCompletionEvaluation X d M n ≫
        (adicLocalization X Λ).map (adicReductionComplexMap X d M M' f n) := by
  have h := (Classical.choose_spec (adicCompletionTowerMap_exists X d M M'
    (adicReductionComplexMap X d M M' f) (adicReductionComplexMap_step X d M M' f))).1.1
  change (adicLocalization X Λ).map _ ≫ (adicLocalization X Λ).map _ =
    (adicLocalization X Λ).map _ ≫ (adicLocalization X Λ).map _
  simp only [← Functor.map_comp]
  apply (adicLocalization X Λ).congr_map
  change adicCompletionTowerMap X d M M'
    (adicReductionComplexMap X d M M' f) (adicReductionComplexMap_step X d M M' f) ≫ _ = _ at h
  rw [← Category.assoc, h, Category.assoc, Limits.Pi.map_π, ← Category.assoc]

/-- The comparison is natural on all K-flat representatives. Since those representatives
localize to the derived category, this is functoriality in K, including the inverse maps
of quasi-isomorphisms; no particular resolution or boundedness is required.
Source: order 1260, functoriality clause and proof step 6.
Proof: scalar extension's unit is natural, with formula m ↦ 1 tensor m. Evaluation from
the cone is natural for the product map in both coordinates, by
adicCompletionTowerMap_exists. Thus the two sides have the same adjoint under
adicReductionHomEquiv, namely evaluation followed by the scalar-restricted reduction
of f. Injectivity of that equivalence gives equality. K-flat resolutions and
lem-pur-derived-change-of-rings identify model changes canonically, so the equality
passes through roofs and inverts quasi-isomorphisms.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicCompletionReduction_naturality (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (N' : AdicKFlatModel X Λ (adicCompletionObject X d M'))
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionMap X d N N' n (adicCompletionModelMap X d M M' f) ≫
        adicCompletionReduction X d M' N' n =
      adicCompletionReduction X d M N n ≫
        adicReductionMap X d M M' n
          (M.realization.inv ≫ (adicLocalization X Λ).map f ≫ M'.realization.hom) := by
  let R := adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have hunit (A : proEtaleDerivedCategory X Λ)
      (P : AdicKFlatModel X Λ A)
      (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1)))
      (g : A ⟶ R.obj H) :
      adicReductionDerivedUnit X d P n ≫
        R.map ((adicReductionHomEquiv X d P n H).symm g) = g :=
    (adicReductionHomEquiv X d P n H).apply_symm_apply g
  apply (adicReductionHomEquiv X d N n _).injective
  change adicReductionDerivedUnit X d N n ≫ R.map _ =
    adicReductionDerivedUnit X d N n ≫ R.map _
  simp only [Functor.map_comp, ← Category.assoc]
  rw [show adicReductionDerivedUnit X d N n ≫
      R.map (adicReductionMap X d N N' n (adicCompletionModelMap X d M M' f)) =
      adicCompletionModelMap X d M M' f ≫ adicReductionDerivedUnit X d N' n from
    hunit _ N _ _]
  simp only [Category.assoc]
  rw [show adicReductionDerivedUnit X d N' n ≫
      R.map (adicCompletionReduction X d M' N' n) =
      adicCompletionEvaluation X d M' n ≫
        (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
          (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M'.complex)).inv from
    hunit _ N' _ _]
  rw [← Category.assoc, adicCompletionEvaluation_naturality]
  rw [Category.assoc]
  change adicCompletionEvaluation X d M n ≫
    (adicLocalization X Λ).map
      (((SheafOfModules.restrictScalars.{t + 1}
          (adicModuleMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f)) ≫ _ = _
  rw [adicDerivedRestrictFactors_naturality]
  rw [adicReductionMap_model]
  simp only [← Category.assoc]
  congr 1
  exact (hunit _ N _ _).symm


end AlgebraicGeometry.Scheme
