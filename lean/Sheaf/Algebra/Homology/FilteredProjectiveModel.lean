/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Algebra.Homology.TwoStepFilteredModuleDerived
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import WeilConjectures.CategoryTheory.PBCFiltration
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
import Sheaf.Algebra.Homology.FilteredProjectiveComparison
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingTriangleClosure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# A finite projective model of a two-step filtered endomorphism

Source: Stacks Project, Tags 03TB and 03TJ; blueprint main-20261015,
prop-trf-trace-formal-laws, proof of clause (2)
(blueprint: lem-trf-filtered-projective-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
private theorem homotopy_of_Q_map_eq {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {X Y : CochainComplex (ModuleCat.{u} A) ℤ} [X.IsKProjective]
    (f g : X ⟶ Y) (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g
    ((IsKProjective.Qh_map_bijective X _).1 ?_)⟩
  have hf := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality f
  have hg := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality g
  dsimp at hf hg
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app Y),
    hf, hg, h]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_filteredProjectiveModelCore {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (P : TwoStepModuleDerived A)
    (hP : ∀ c : Bool, DerivedCategory.IsPerfectRingComplex ((twoStepGraded A c).obj P)) :
    ∃ M : TwoStepModuleComplex A,
      (∃ a b : ℤ,
        M.obj.right.IsStrictlyGE a ∧ M.obj.right.IsStrictlyLE b ∧
        ∀ c : Bool, ((twoStepGradedComplex A c).obj M).IsStrictlyGE a ∧
          ((twoStepGradedComplex A c).obj M).IsStrictlyLE b) ∧
      (∀ n : ℤ,
        (Module.Finite A (M.obj.right.X n) ∧ Module.Projective A (M.obj.right.X n)) ∧
        ∀ c : Bool, Module.Finite A (((twoStepGradedComplex A c).obj M).X n) ∧
          Module.Projective A (((twoStepGradedComplex A c).obj M).X n)) ∧
      (ShortComplex.mk M.obj.hom (cokernel.π M.obj.hom)
        (cokernel.condition M.obj.hom)).ShortExact ∧
      (∀ n : ℤ, ∃ s : (cokernel M.obj.hom).X n ⟶ M.obj.right.X n,
        s ≫ (cokernel.π M.obj.hom).f n = 𝟙 _) ∧
      Nonempty ((twoStepModuleQ A).obj M ≅ P) := by
  classical
  obtain ⟨K, rfl⟩ := (Localization.Construction.objEquiv
    (twoStepModuleQuasiIso A)).surjective P
  obtain ⟨K⟩ := K
  have hKmono : Mono K.obj.hom := K.property
  let S := ShortComplex.mk K.obj.hom (cokernel.π K.obj.hom)
    (cokernel.condition K.obj.hom)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel _
      mono_f := hKmono }
  have hsub : DerivedCategory.IsPerfectRingComplex (DerivedCategory.Q.obj K.obj.left) :=
    hP true
  have hquot : DerivedCategory.IsPerfectRingComplex
      (DerivedCategory.Q.obj (cokernel K.obj.hom)) := hP false
  have htotal := DerivedCategory.isPerfectRingComplex_obj₂_of_distTriang
    (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)
    hsub hquot
  obtain ⟨X, ax, bx, hxa, hxb, hX, ⟨ex⟩⟩ := hsub
  obtain ⟨Y, ay, by', hya, hyb, hY, ⟨ey⟩⟩ := htotal
  have : ∀ n, Projective (X.X n) := fun n ↦ by
    have := (hX n).1
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : ∀ n, Projective (Y.X n) := fun n ↦ by
    have := (hY n).1
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : X.IsKProjective := isKProjective_of_projective X bx
  have : Y.IsKProjective := isKProjective_of_projective Y by'
  obtain ⟨a, ha⟩ := IsKProjective.exists_Q_map_eq X K.obj.left ex.inv
  obtain ⟨b, hb⟩ := IsKProjective.exists_Q_map_eq Y K.obj.right ey.inv
  have : IsIso (DerivedCategory.Q.map a) := by rw [ha]; infer_instance
  have : IsIso (DerivedCategory.Q.map b) := by rw [hb]; infer_instance
  have hqa : QuasiIso a :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat A) a).1 inferInstance
  have hqb : QuasiIso b :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat A) b).1 inferInstance
  obtain ⟨g, hg⟩ := IsKProjective.exists_Q_map_eq X Y
    (ex.inv ≫ DerivedCategory.Q.map K.obj.hom ≫ ey.hom)
  obtain ⟨h⟩ := homotopy_of_Q_map_eq (a ≫ K.obj.hom) (g ≫ b) (by
    simp [Functor.map_comp, ha, hb, hg])
  let C := mappingCone (𝟙 X)
  let T := C ⊞ Y
  let i : X ⟶ T := biprod.lift (mappingCone.inr (𝟙 X)) g
  let δ := a ≫ K.obj.hom - g ≫ b
  have hδ : Homotopy ((𝟙 X) ≫ δ) 0 := by
    simpa [δ] using (Homotopy.equivSubZero h)
  let t : C ⟶ K.obj.right := HomologicalComplex.homotopyCofiber.desc (𝟙 X) δ hδ
  let q : T ⟶ K.obj.right := biprod.desc t b
  have hiq : i ≫ q = a ≫ K.obj.hom := by
    simp [i, q, t, δ, mappingCone.inr]
  have hir (n : ℤ) : i.f n ≫
      (biprod.fst : T ⟶ C).f n ≫ HomologicalComplex.homotopyCofiber.sndX (𝟙 X) n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f_assoc, biprod.lift_fst]
    simp [mappingCone.inr]
  have hmono (n : ℤ) : Mono (i.f n) :=
    mono_of_mono_fac (hir n)
  have : Mono i := HomologicalComplex.mono_of_mono_f i hmono
  let M : TwoStepModuleComplex A := ⟨Arrow.mk i, by change Mono i; infer_instance⟩
  have hMexact : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hSplit (n : ℤ) : ∃ s : (cokernel i).X n ⟶ T.X n,
      s ≫ (cokernel.π i).f n = 𝟙 _ := by
    let E := (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).map
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n)
    have hE : E.ShortExact := hMexact.map_of_exact _
    let splitting := ShortComplex.Splitting.ofExactOfRetraction E hE.exact
      ((biprod.fst : T ⟶ C).f n ≫ HomologicalComplex.homotopyCofiber.sndX (𝟙 X) n) (hir n) hE.epi_g
    exact ⟨splitting.s, splitting.s_g⟩
  let eC (n : ℤ) : C.X n ≅ X.X (n + 1) ⊞ X.X n :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 X) n (n + 1) rfl
  let eT (n : ℤ) : T.X n ≅ (X.X (n + 1) ⊞ X.X n) ⊞ Y.X n :=
    (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).mapBiprod C Y ≪≫
      biprod.mapIso (eC n) (Iso.refl _)
  have hFC (n : ℤ) : Module.Finite A (C.X n) ∧ Module.Projective A (C.X n) := by
    have := (hX (n + 1)).1
    have := (hX (n + 1)).2
    have := (hX n).1
    have := (hX n).2
    let e := eC n ≪≫ ModuleCat.biprodIsoProd _ _
    exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
      Module.Projective.of_equiv e.toLinearEquiv.symm⟩
  have hFT (n : ℤ) : Module.Finite A (T.X n) ∧ Module.Projective A (T.X n) := by
    have := (hFC n).1
    have := (hFC n).2
    have := (hY n).1
    have := (hY n).2
    let e : T.X n ≅ ModuleCat.of A (C.X n × Y.X n) :=
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).mapBiprod C Y ≪≫
      ModuleCat.biprodIsoProd _ _
    exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
      Module.Projective.of_equiv e.toLinearEquiv.symm⟩
  have hFQ (n : ℤ) : Module.Finite A ((cokernel i).X n) ∧
      Module.Projective A ((cokernel i).X n) := by
    have := (hFT n).1
    have := (hFT n).2
    obtain ⟨s, hs⟩ := hSplit n
    refine ⟨Module.Finite.of_surjective ((cokernel.π i).f n).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance), ?_⟩
    exact Module.Projective.of_split s.hom ((cokernel.π i).f n).hom
      (by simpa only [← ModuleCat.hom_comp, ModuleCat.hom_id] using congrArg ModuleCat.Hom.hom hs)
  let lo := min ax ay - 1
  let hi := max bx by'
  have hTb : T.IsStrictlyGE lo ∧ T.IsStrictlyLE hi := by
    constructor
    · rw [isStrictlyGE_iff]
      intro n hn
      apply IsZero.of_iso _ (eT n)
      rw [biprod_isZero_iff, biprod_isZero_iff]
      exact ⟨⟨X.isZero_of_isStrictlyGE ax _ (by dsimp [lo] at hn; omega),
        X.isZero_of_isStrictlyGE ax _ (by dsimp [lo] at hn; omega)⟩,
        Y.isZero_of_isStrictlyGE ay _ (by dsimp [lo] at hn; omega)⟩
    · rw [isStrictlyLE_iff]
      intro n hn
      apply IsZero.of_iso _ (eT n)
      rw [biprod_isZero_iff, biprod_isZero_iff]
      exact ⟨⟨X.isZero_of_isStrictlyLE bx _ (by dsimp [hi] at hn; omega),
        X.isZero_of_isStrictlyLE bx _ (by dsimp [hi] at hn; omega)⟩,
        Y.isZero_of_isStrictlyLE by' _ (by dsimp [hi] at hn; omega)⟩
  have hQb : (cokernel i).IsStrictlyGE lo ∧ (cokernel i).IsStrictlyLE hi := by
    have := hTb.1
    have := hTb.2
    constructor
    · rw [isStrictlyGE_iff]
      exact fun n hn ↦ IsZero.of_epi ((cokernel.π i).f n)
        (T.isZero_of_isStrictlyGE lo n hn)
    · rw [isStrictlyLE_iff]
      exact fun n hn ↦ IsZero.of_epi ((cokernel.π i).f n)
        (T.isZero_of_isStrictlyLE hi n hn)
  have hXb : X.IsStrictlyGE lo ∧ X.IsStrictlyLE hi := by
    constructor
    · rw [isStrictlyGE_iff]
      exact fun n hn ↦ X.isZero_of_isStrictlyGE ax n (by dsimp [lo] at hn; omega)
    · rw [isStrictlyLE_iff]
      exact fun n hn ↦ X.isZero_of_isStrictlyLE bx n (by dsimp [hi] at hn; omega)
  have hC : Homotopy (𝟙 C) 0 :=
    mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
  have hT := (hC.compRight (biprod.inl : C ⟶ T)).compLeft (biprod.fst : T ⟶ C)
  let e : HomotopyEquiv Y T :=
    { hom := biprod.inr
      inv := biprod.snd
      homotopyHomInvId := Homotopy.ofEq (by simp)
      homotopyInvHomId := by
        have hh := hT.symm.add
          (Homotopy.refl (biprod.snd ≫ biprod.inr : T ⟶ T))
        refine (Homotopy.ofEq (by simp)).trans (hh.trans (Homotopy.ofEq ?_))
        simpa only [Category.id_comp, Category.comp_id] using
          (biprod.total (X := C) (Y := Y)) }
  have : QuasiIso (biprod.inr : Y ⟶ T) := e.quasiIso_hom
  have : QuasiIso ((biprod.inr : Y ⟶ T) ≫ q) := by simpa [q] using hqb
  have hqq : QuasiIso q := quasiIso_of_comp_left
    (biprod.inr : Y ⟶ T) q
  let f : M ⟶ K := ObjectProperty.homMk (Arrow.homMk a q hiq.symm)
  let ψ : ShortComplex.mk i (cokernel.π i) (cokernel.condition i) ⟶ S :=
    { τ₁ := a
      τ₂ := q
      τ₃ := (coker _).map f.hom
      comm₁₂ := hiq.symm
      comm₂₃ := by
        change q ≫ cokernel.π K.obj.hom =
          cokernel.π i ≫ cokernel.desc i (q ≫ cokernel.π K.obj.hom) _
        simp }
  have hqquot : QuasiIso ((coker _).map f.hom) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ hMexact hS hqa hqq
  have hf : twoStepModuleQuasiIso A ((twoStepModuleHomotopyQuotient A).map f) := by
    refine ⟨f, rfl, ?_⟩
    intro c
    cases c
    · exact hqquot
    · exact hqa
  have hj : Nonempty ((twoStepModuleQ A).obj M ≅
      (twoStepModuleQuasiIso A).Q.obj ⟨K⟩) :=
    ⟨Localization.Construction.wIso _ hf⟩
  refine ⟨M, ⟨lo, hi, hTb.1, hTb.2, ?_⟩, ?_, hMexact, hSplit, hj⟩
  · intro c
    cases c
    · exact hQb
    · exact hXb
  · intro n
    refine ⟨hFT n, ?_⟩
    intro c
    cases c
    · exact hFQ n
    · exact ⟨(hX n).2, (hX n).1⟩

set_option backward.isDefEq.respectTransparency false in
private theorem lift_filtered_endomorphism {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (M : TwoStepModuleComplex A)
    (P : TwoStepModuleDerived A) (uP : P ⟶ P)
    (hM : (∃ a b : ℤ,
      M.obj.right.IsStrictlyGE a ∧ M.obj.right.IsStrictlyLE b ∧
      ∀ c : Bool, ((twoStepGradedComplex A c).obj M).IsStrictlyGE a ∧
        ((twoStepGradedComplex A c).obj M).IsStrictlyLE b))
    (hMF : ∀ n : ℤ,
      (Module.Finite A (M.obj.right.X n) ∧ Module.Projective A (M.obj.right.X n)) ∧
      ∀ c : Bool, Module.Finite A (((twoStepGradedComplex A c).obj M).X n) ∧
        Module.Projective A (((twoStepGradedComplex A c).obj M).X n))
    (j : (twoStepModuleQ A).obj M ≅ P) :
    ∃ ū : M ⟶ M,
      (twoStepModuleQ A).map ū ≫ j.hom = j.hom ≫ uP ∧
      ∀ c : Bool,
        DerivedCategory.Q.map ((twoStepGradedComplex A c).map ū) ≫
            (twoStepGraded A c).map j.hom =
          (twoStepGraded A c).map j.hom ≫ (twoStepGraded A c).map uP := by
  let K := (twoStepModuleHomotopyQuotient A).obj M
  have hbound : IsTwoStepBoundedAbove A K := by
    obtain ⟨a, b, ha, hb, hgr⟩ := hM
    have := hb
    exact ⟨b, fun n hn ↦ M.obj.right.isZero_of_isStrictlyLE b n hn⟩
  have hproj : IsTwoStepGradedProjective A K := fun c n ↦ (hMF n).2 c |>.2
  obtain ⟨v, hv⟩ :=
    (filteredProjectiveComparison A).2.2.2.2.2.1 K K hbound hproj |>.2
      (j.hom ≫ uP ≫ j.inv)
  obtain ⟨ū, hū⟩ := Quot.exists_rep v
  dsimp only [K, twoStepModuleHomotopyQuotient, CategoryTheory.Quotient.functor] at ū hū
  change (twoStepModuleHomotopyQuotient A).map ū = v at hū
  have hu : (twoStepModuleQ A).map ū ≫ j.hom = j.hom ≫ uP := by
    change (twoStepModuleQh A).map
      ((twoStepModuleHomotopyQuotient A).map ū) ≫ j.hom = _
    rw [hū]
    change (MorphismProperty.Q (twoStepModuleQuasiIso A)).map v ≫ j.hom = _
    dsimp only at hv
    rw [hv]
    simp only [Category.assoc, j.inv_hom_id, Category.comp_id]
  refine ⟨ū, hu, ?_⟩
  intro c
  have hcomp : twoStepModuleQ A ⋙ twoStepGraded A c =
      twoStepGradedComplex A c ⋙ DerivedCategory.Q := by
    change twoStepModuleHomotopyQuotient A ⋙
      (twoStepModuleQh A ⋙ twoStepGraded A c) = _
    have hfac := Localization.Construction.fac
      (twoStepGradedHomotopy A c) (twoStepGraded_inverts A c)
    change (twoStepModuleQuasiIso A).Q ⋙ twoStepGraded A c = _ at hfac
    change twoStepModuleHomotopyQuotient A ⋙
      ((twoStepModuleQuasiIso A).Q ⋙ twoStepGraded A c) = _
    rw [hfac]
    rfl
  have hmap := Functor.congr_hom hcomp ū
  dsimp only [Functor.comp_map] at hmap
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hmap
  rw [← hmap]
  simpa only [Functor.map_comp] using congrArg ((twoStepGraded A c).map) hu

/-- A two-step filtered derived object with perfect graded pieces, together with any
localized endomorphism, admits a bounded finite-projective filtered chain model.
The restricted and quotient maps represent the induced graded endomorphisms.
Filtration preservation is encoded by a commutative square of complexes; it does
not require equality of the image of a filtration step with an intersection.

Source: Stacks, Tags 03TB and 03TJ; blueprint main-20261015,
prop-trf-trace-formal-laws, proof of clause (2).

Proof:
Choose a representative inclusion K′ → K. Its short exact triangle and perfect
subcomplex and quotient show that K is perfect. Choose bounded finite-projective
models X,Y of K′,K. The K-projective Hom bijection represents the inclusion by
X → Y and supplies a homotopy-commuting square to K′ → K. Adding cone(id X) to Y
rectifies this square to a strict square X → cone(id X) ⊞ Y mapping to K′ → K.
The new inclusion splits degreewise; its total map is a quasi-isomorphism since
the added cone is contractible. The homology sequences give the quotient
quasi-isomorphism. Direct sums and direct summands give finite projectivity;
the explicit cone terms give common upper and lower bounds.
Finally filtered projective comparison lifts the conjugated endomorphism to a
filtered chain map. Applying the canonical graded functors to the conjugacy
identity gives the two required graded identities.
(blueprint: lem-trf-filtered-projective-model). -/
theorem exists_filteredProjectiveModel {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (P : TwoStepModuleDerived A)
    (hP : ∀ c : Bool, DerivedCategory.IsPerfectRingComplex ((twoStepGraded A c).obj P))
    (uP : P ⟶ P) :
    ∃ M : TwoStepModuleComplex A,
      (∃ a b : ℤ,
        M.obj.right.IsStrictlyGE a ∧ M.obj.right.IsStrictlyLE b ∧
        ∀ c : Bool, ((twoStepGradedComplex A c).obj M).IsStrictlyGE a ∧
          ((twoStepGradedComplex A c).obj M).IsStrictlyLE b) ∧
      (∀ n : ℤ,
        (Module.Finite A (M.obj.right.X n) ∧ Module.Projective A (M.obj.right.X n)) ∧
        ∀ c : Bool, Module.Finite A (((twoStepGradedComplex A c).obj M).X n) ∧
          Module.Projective A (((twoStepGradedComplex A c).obj M).X n)) ∧
      (ShortComplex.mk M.obj.hom (cokernel.π M.obj.hom)
        (cokernel.condition M.obj.hom)).ShortExact ∧
      (∀ n : ℤ, ∃ s : (cokernel M.obj.hom).X n ⟶ M.obj.right.X n,
        s ≫ (cokernel.π M.obj.hom).f n = 𝟙 _) ∧
      ∃ j : (twoStepModuleQ A).obj M ≅ P, ∃ ū : M ⟶ M,
        (twoStepModuleQ A).map ū ≫ j.hom = j.hom ≫ uP ∧
        ∀ c : Bool,
          DerivedCategory.Q.map ((twoStepGradedComplex A c).map ū) ≫
              (twoStepGraded A c).map j.hom =
            (twoStepGraded A c).map j.hom ≫ (twoStepGraded A c).map uP := by
  obtain ⟨M, hM, hMF, hE, hS, ⟨j⟩⟩ := exists_filteredProjectiveModelCore P hP
  obtain ⟨ū, hu, hgraded⟩ := lift_filtered_endomorphism M P uP hM hMF j
  exact ⟨M, hM, hMF, hE, hS, j, ū, hu, hgraded⟩

end CochainComplex
