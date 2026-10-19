/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.Triangulated.MilnorSequence
import Sheaf.CategoryTheory.DerivedLimitEventuallyIso
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Reconstruction from lower truncations on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0D6P, lemma-is-limit-dimension
(blueprint: lem-kun-site-truncation-derived-limit).

Vanishing of H^p(V,M) is written using its defining K-injective computation: for every
K-injective resolution of the single complex M[0], the degree-p homology of its
section complex is zero. Thus no choice of a resolution or total derived functor is
introduced. The specified product lift retains all the canonical truncation maps.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private noncomputable def sectionsUnit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  let q := HomotopyCategory.quotient A (.up ℤ)
  let a := Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _
  a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
      F.rightDerivedFunctor).hom

private instance sectionsUnit_isIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ D) [F.Additive]
    (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso ((sectionsUnit F).app I) := by
  dsimp [sectionsUnit]
  infer_instance

private theorem sections_homology_isIso_iff
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ D) [F.Additive]
    {I L : CochainComplex A ℤ} [I.IsKInjective] [L.IsKInjective]
    (f : I ⟶ L) (m : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor D m).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map f))) ↔
      IsIso (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map f) m) := by
  let H := DerivedCategory.homologyFunctor D m
  let G := F.mapHomologicalComplex (.up ℤ)
  have h := congrArg H.map ((sectionsUnit F).naturality f)
  simp only [Functor.map_comp, Functor.comp_map] at h
  have hq : IsIso (H.map (DerivedCategory.Q.map (G.map f))) ↔
      IsIso (HomologicalComplex.homologyMap (G.map f) m) :=
    NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors D m) (G.map f)
  rw [← hq]
  constructor
  · intro h'
    have : IsIso (H.map (DerivedCategory.Q.map (G.map f)) ≫
        H.map ((sectionsUnit F).app L)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (H.map ((sectionsUnit F).app L))
  · intro h'
    have : IsIso (H.map ((sectionsUnit F).app I) ≫
        H.map (F.rightDerivedFunctor.map (DerivedCategory.Q.map f))) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_left (H.map ((sectionsUnit F).app I)) _

private theorem sheafified_isIso_of_cover
    {C : Type c} [Category.{v} C] (J : Precoverage C)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max c v r}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (B : Set C)
    (hB : ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f → V ∈ B)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max c v r}} (f : P ⟶ Q)
    (hf : ∀ V : C, V ∈ B → IsIso (f.app (op V))) :
    IsIso ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max c v r}).map f) := by
  have hinj : Presheaf.IsLocallyInjective J.toGrothendieck f := by
    constructor
    intro U x y hxy
    obtain ⟨S, hS, hSB⟩ := hB U.unop
    apply J.toGrothendieck.superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (J.generate_mem_toGrothendieck hS)
    intro V a ha
    have := hf V (hSB V a ha)
    apply (ConcreteCategory.bijective_of_isIso (f.app (op V))).injective
    simpa only [NatTrans.naturality_apply] using congrArg (Q.map a.op) hxy
  have hsurj : Presheaf.IsLocallySurjective J.toGrothendieck f := by
    constructor
    intro U x
    obtain ⟨S, hS, hSB⟩ := hB U
    apply J.toGrothendieck.superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (J.generate_mem_toGrothendieck hS)
    intro V a ha
    have := hf V (hSB V a ha)
    exact (ConcreteCategory.bijective_of_isIso (f.app (op V))).surjective (Q.map a.op x)
  exact (J.toGrothendieck.W_iff f).1 (J.toGrothendieck.W_of_isLocallyBijective f)

private noncomputable def sheafificationHomologyIso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J RingCat.{max c v r}) (m : ℤ) :
    (SheafOfModules.toSheaf.{max c v r} R ⋙
      sheafToPresheaf J AddCommGrpCat.{max c v r}).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor _ (.up ℤ) m ⋙
        presheafToSheaf J AddCommGrpCat.{max c v r} ≅
      HomologicalComplex.homologyFunctor (ringedSiteModules.{max c v r} R) (.up ℤ) m ⋙
        SheafOfModules.toSheaf R := by
  have := (moduleSheaves_colimits_forgetful R).2.1
  have := (moduleSheaves_colimits_forgetful R).2.2.1
  let T := SheafOfModules.toSheaf.{max c v r} R
  let U := sheafToPresheaf J AddCommGrpCat.{max c v r}
  let S := presheafToSheaf J AddCommGrpCat.{max c v r}
  let e : (T ⋙ U) ⋙ S ≅ T :=
    Functor.associator T U S ≪≫
      Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction _ _).counit) ≪≫
        T.rightUnitor
  exact Functor.isoWhiskerLeft ((T ⋙ U).mapHomologicalComplex (.up ℤ))
      (S.mapHomologicalComplexHomologyIso (.up ℤ) m).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ))
      (HomologicalComplex.homologyFunctor _ (.up ℤ) m) ≪≫
    T.mapHomologicalComplexHomologyIso (.up ℤ) m

private theorem homology_isIso_of_sections
    {C : Type c} [Category.{v} C] (J : Precoverage C)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max c v r}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J.toGrothendieck RingCat.{max c v r})
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r} R)]
    [HasDerivedCategory AddCommGrpCat.{max c v r}]
    [Abelian.HasKInjectiveResolutions (ringedSiteModules.{max c v r} R)]
    (B : Set C)
    (hB : ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f → V ∈ B)
    {X Y : DerivedCategory (ringedSiteModules.{max c v r} R)}
    (f : X ⟶ Y) (m : ℤ)
    (hf : ∀ V : C, V ∈ B → IsIso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} m).map
        ((SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{max c v r}).obj (op V)).rightDerivedFunctor.map f))) :
    IsIso ((DerivedCategory.homologyFunctor (ringedSiteModules.{max c v r} R) m).map f) := by
  classical
  let A := ringedSiteModules.{max c v r} R
  let U := SheafOfModules.toSheaf.{max c v r} R ⋙
    sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max c v r}
  obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  obtain ⟨L, hL, ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective Y
  let q := HomotopyCategory.quotient A (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨a, ha⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj I) L).surjective
    ((e.app I).hom ≫ eI.inv ≫ f ≫ eL.hom ≫ (e.app L).inv)
  obtain ⟨g, rfl⟩ := q.map_surjective a
  have hg : eI.hom ≫ DerivedCategory.Q.map g = f ≫ eL.hom := by
    have hn := e.hom.naturality g
    change DerivedCategory.Qh.map (q.map g) ≫ (e.app L).hom =
      (e.app I).hom ≫ DerivedCategory.Q.map g at hn
    calc
      eI.hom ≫ DerivedCategory.Q.map g =
          eI.hom ≫ (e.app I).inv ≫ DerivedCategory.Qh.map (q.map g) ≫
            (e.app L).hom := by
        have hn' := congrArg (fun k ↦ eI.hom ≫ (e.app I).inv ≫ k) hn
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hn'.symm
      _ = f ≫ eL.hom := by rw [ha]; simp
  have hsec (V : C) (hV : V ∈ B) :
      IsIso (HomologicalComplex.homologyMap
        (((U ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{max c v r}).obj (op V)).mapHomologicalComplex
          (.up ℤ)).map g) m) := by
    let F := U ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{max c v r}).obj (op V)
    let H := F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat m
    have := hf V hV
    have hiso : IsIso (H.map f) := hf V hV
    have h := congrArg H.map hg
    rw [Functor.map_comp, Functor.map_comp] at h
    have : IsIso (H.map eI.hom ≫ H.map (DerivedCategory.Q.map g)) := by
      rw [h]
      infer_instance
    have : IsIso (H.map (DerivedCategory.Q.map g)) :=
      IsIso.of_isIso_comp_left (H.map eI.hom) _
    exact (sections_homology_isIso_iff F g m).1 this
  let P := U.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.homologyFunctor _ (.up ℤ) m
  have hP (V : C) (hV : V ∈ B) : IsIso ((P.map g).app (op V)) := by
    let ev := (evaluation Cᵒᵖ AddCommGrpCat.{max c v r}).obj (op V)
    have : IsIso (((ev.mapHomologicalComplex (.up ℤ)) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℤ) m).map
          ((U.mapHomologicalComplex (.up ℤ)).map g)) := hsec V hV
    exact (NatIso.isIso_map_iff (ev.mapHomologicalComplexHomologyIso (.up ℤ) m)
      ((U.mapHomologicalComplex (.up ℤ)).map g)).1 this
  have : IsIso ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max c v r}).map (P.map g)) :=
    sheafified_isIso_of_cover.{c, v, r} J B hB (P.map g) hP
  have : IsIso ((SheafOfModules.toSheaf R).map (HomologicalComplex.homologyMap g m)) :=
    (NatIso.isIso_map_iff (sheafificationHomologyIso.{c, v, r} J.toGrothendieck R m) g).1 this
  have : IsIso (HomologicalComplex.homologyMap g m) :=
    isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)
  have : IsIso ((DerivedCategory.homologyFunctor A m).map (DerivedCategory.Q.map g)) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A m) g).2 this
  have h := congrArg (DerivedCategory.homologyFunctor A m).map hg
  rw [Functor.map_comp, Functor.map_comp] at h
  have : IsIso ((DerivedCategory.homologyFunctor A m).map f ≫
      (DerivedCategory.homologyFunctor A m).map eL.hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((DerivedCategory.homologyFunctor A m).map f)
    ((DerivedCategory.homologyFunctor A m).map eL.hom)

private theorem truncation_stabilization
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] [HasDerivedCategory AddCommGrpCat.{r}]
    (F : A ⥤ AddCommGrpCat.{r}) [F.Additive] (E : DerivedCategory A) (d : ℕ)
    (hv : ∀ p : ℤ, (d : ℤ) < p → ∀ q : ℤ, q < 0 →
      ∀ (I : CochainComplex A ℤ)
        (ι : (CochainComplex.singleFunctor A 0).obj
          ((DerivedCategory.homologyFunctor A q).obj E) ⟶ I),
      I.IsKInjective → QuasiIso ι →
        IsZero (((F.mapHomologicalComplex (.up ℤ)).obj I).homology p))
    (m : ℤ) (n : ℕ) (hn : (d : ℤ) - m + 1 ≤ (n : ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{r} (m - 1)).map
      (F.rightDerivedFunctor.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))) ∧
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{r} m).map
      (F.rightDerivedFunctor.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))) := by
  let M := (DerivedCategory.homologyFunctor A (-((n + 1 : ℕ) : ℤ))).obj E
  let S := (CochainComplex.singleFunctor A 0).obj M
  let D := F.rightDerivedFunctor
  have hz (j : ℤ) (hj : j = m - 1 ∨ j = m ∨ j = m + 1) :
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{r} j).obj
        (D.obj ((DerivedCategory.Q.obj S)⟦((n + 1 : ℕ) : ℤ)⟧))) := by
    obtain ⟨I, hI, ι, _, hι⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective S
    have hvan := hv (j + ((n + 1 : ℕ) : ℤ))
      (by rcases hj with rfl | rfl | rfl <;> omega)
      (-((n + 1 : ℕ) : ℤ)) (by omega) I ι hI hι
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{r}
      (j + ((n + 1 : ℕ) : ℤ))
    let e := (DerivedCategory.homologyFunctor AddCommGrpCat.{r} j).mapIso
        ((D.commShiftIso ((n + 1 : ℕ) : ℤ)).app (DerivedCategory.Q.obj S)) ≪≫
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{r} 0).shiftIso
        ((n + 1 : ℕ) : ℤ) j (j + ((n + 1 : ℕ) : ℤ)) (by omega)).app
          (D.obj (DerivedCategory.Q.obj S)) ≪≫
      H.mapIso (D.mapIso (asIso (DerivedCategory.Q.map ι))) ≪≫
      H.mapIso (asIso ((sectionsUnit F).app I)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{r}
        (j + ((n + 1 : ℕ) : ℤ))).app ((F.mapHomologicalComplex (.up ℤ)).obj I)
    exact hvan.of_iso e
  obtain ⟨a, b, hT⟩ := DerivedCategory.exists_lowerTruncationStepTriangle E
    ((n + 1 : ℕ) : ℤ)
  let T := Pretriangulated.Triangle.mk a
    ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) (by omega)).app E) b
  let DT := D.mapTriangle.obj T
  have hDT := D.map_distinguished T hT
  have h₁ := DerivedCategory.isIso_homologyMap_mor₂ DT hDT (m - 1) m (by omega)
    (hz (m - 1) (Or.inl rfl)) (hz m (Or.inr (Or.inl rfl)))
  have h₂ := DerivedCategory.isIso_homologyMap_mor₂ DT hDT m (m + 1) rfl
    (hz m (Or.inr (Or.inl rfl))) (hz (m + 1) (Or.inr (Or.inr rfl)))
  have he : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
  change IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{r} (m - 1)).map
    (D.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) (by omega)).app E))) at h₁
  change IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{r} m).map
    (D.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) (by omega)).app E))) at h₂
  rw! [he] at h₁ h₂
  exact ⟨h₁, h₂⟩

private theorem tower_map_isIso
    {D : Type*} [Category D] (A : ℕᵒᵖ ⥤ D) (N : ℕ)
    (hA : ∀ n : ℕ, N ≤ n → IsIso (A.map (homOfLE (Nat.le_succ n)).op))
    (n : ℕ) (hn : N ≤ n) : IsIso (A.map (homOfLE hn).op) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using (inferInstance : IsIso (𝟙 (A.obj (op N))))
  | succ n hn ih =>
    have := hA n hn
    have := ih
    have he : (homOfLE (show N ≤ n + 1 by omega)).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op := Subsingleton.elim _ _
    rw [he, A.map_comp]
    infer_instance

private theorem limit_projection_isIso
    {D : Type*} [Category D] [Balanced D] (A : ℕᵒᵖ ⥤ D) [HasLimit A] (N : ℕ)
    (hA : ∀ n : ℕ, N ≤ n → IsIso (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsIso (limit.π A (op N)) := by
  classical
  have hm : Mono (limit.π A (op N)) := by
    constructor
    intro Z u v huv
    apply limit.hom_ext
    rintro ⟨n⟩
    by_cases hn : n ≤ N
    · have hw := limit.w A (homOfLE hn).op
      simp only [← hw, ← Category.assoc, huv]
    · have hn' : N ≤ n := by omega
      have := tower_map_isIso A N hA n hn'
      apply (cancel_mono (A.map (homOfLE hn').op)).1
      simpa only [Category.assoc, limit.w] using huv
  let K := fun n : ℕ ↦ A.obj (op n)
  let f := fun n : ℕ ↦ A.map (homOfLE (Nat.le_succ n)).op
  let up : ∀ z : ℤ, (N : ℤ) ≤ z → (K N ⟶ K z.toNat) → (K N ⟶ K (z + 1).toNat) :=
    fun z hz a ↦ by
      have : IsIso (f z.toNat) := hA z.toNat (by omega)
      exact a ≫ inv (f z.toNat) ≫
        eqToHom (congrArg K (show z.toNat + 1 = (z + 1).toNat by omega))
  let down : ∀ z : ℤ, z ≤ (N : ℤ) → (K N ⟶ K z.toNat) → (K N ⟶ K (z - 1).toNat) :=
    fun z _ a ↦ if h : 0 < z then a ≫
      eqToHom (congrArg K (show z.toNat = (z - 1).toNat + 1 by omega)) ≫
        f (z - 1).toNat else a ≫ eqToHom (congrArg K (by omega))
  let qInt : ∀ z : ℤ, K N ⟶ K z.toNat := fun z ↦
    z.inductionOn' (N : ℤ) (eqToHom (by simp)) up down
  let q : ∀ n : ℕ, K N ⟶ K n := fun n ↦ qInt n
  have hq : ∀ n : ℕ, q (n + 1) ≫ f n = q n := by
    intro n
    by_cases hn : N ≤ n
    · have he := Int.inductionOn'_add_one (motive := fun z : ℤ ↦ K N ⟶ K z.toNat)
        (zero := (eqToHom (by simp) : K N ⟶ K (N : ℤ).toNat))
        (succ := up) (pred := down) (show (N : ℤ) ≤ (n : ℤ) by omega)
      have : IsIso (f n) := hA n hn
      dsimp [up] at he
      simp only [Category.comp_id] at he
      change q (n + 1) = q n ≫ inv (f n) at he
      rw [he, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · have he := Int.inductionOn'_sub_one (motive := fun z : ℤ ↦ K N ⟶ K z.toNat)
        (zero := (eqToHom (by simp) : K N ⟶ K (N : ℤ).toNat))
        (succ := up) (pred := down) (show ((n + 1 : ℕ) : ℤ) ≤ (N : ℤ) by omega)
      dsimp [down] at he
      rw [dif_pos (show 0 < (n : ℤ) + 1 by omega)] at he
      rw! [show (n : ℤ) + 1 - 1 = (n : ℤ) by omega] at he
      simp only [eqToHom_refl, Category.id_comp,
        Int.toNat_natCast] at he
      change q n = q (n + 1) ≫ f n at he
      exact he.symm
  let s : Cone A :=
    { pt := K N
      π := NatTrans.ofOpSequence q (by
        intro n
        change 𝟙 (K N) ≫ q n = q (n + 1) ≫ f n
        simpa only [Category.id_comp] using (hq n).symm) }
  have hs : limit.lift A s ≫ limit.π A (op N) = 𝟙 _ := by
    rw [limit.lift_π]
    change qInt (N : ℤ) = 𝟙 _
    simp only [qInt, Int.inductionOn'_self, eqToHom_refl]
  have : IsSplitEpi (limit.π A (op N)) := ⟨⟨⟨limit.lift A s, hs⟩⟩⟩
  exact isIso_of_mono_of_epi _

private theorem derivedLimit_projection_isIso
    [HasDerivedCategory.{w} AddCommGrpCat.{r}]
    (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{r})
    [HasProduct (fun n : ℕ ↦ K.obj (op n))]
    (L : DerivedCategory AddCommGrpCat.{r})
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ K.obj (op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op) L p δ)
    (m : ℤ) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n →
      IsIso ((K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{r} (m - 1)).map
        (homOfLE (Nat.le_succ n)).op) ∧
      IsIso ((K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{r} m).map
        (homOfLE (Nat.le_succ n)).op)) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{r} m).map
      (p ≫ Pi.π (fun n : ℕ ↦ K.obj (op n)) N)) := by
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{r} m
  obtain ⟨a, b, hseq, _⟩ := milnor_shortExact m
  obtain ⟨⟨hz, hshort⟩, hπ⟩ := hseq K L p δ hK
  have hzero := isZero_firstDerivedLimit_of_eventually_isIso
    (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{r} (m - 1))
    ⟨N, fun n hn ↦ (hN n hn).1⟩
  have : IsIso (b K L p δ) := hshort.isIso_g_iff.mpr hzero
  have : IsIso (limit.π (K ⋙ H) (op N)) :=
    limit_projection_isIso (K ⋙ H) N (fun n hn ↦ (hN n hn).2)
  rw [← hπ N]
  infer_instance

private theorem derived_hasProduct
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] [HasLimitsOfShape (Discrete ℕ) A]
    (K : ℕ → DerivedCategory A) : HasProduct K := by
  classical
  have hex (n : ℕ) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
  choose I hI he using hex
  have : ∀ n, (I n).IsKInjective := hI
  obtain ⟨_, hP⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit I
  have : HasLimit (Discrete.functor I ⋙ DerivedCategory.Q) := ⟨⟨_, hP.some⟩⟩
  let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
    Discrete.natIso fun n ↦ (Classical.choice (he n.as)).symm
  exact hasLimit_of_iso α

set_option backward.isDefEq.respectTransparency false in
/-- A uniform local bound for negative cohomology sheaves gives the distinguished
Roos triangle of the lower-truncation tower, with the specified canonical projections.
Source: Stacks Project, Cohomology on Sites, Tag 0D6P
(blueprint: lem-kun-site-truncation-derived-limit).

Proof:
1. Resolve every truncation by a K-injective complex (prop-pur-kinjective-resolutions-exist).
Sectionwise products exist (lem-weil-pbc-module-sheaves-colimits-forgetful); their complex
represents the derived product (lem-pc-ringed-space-product-kinjective). Complete 1-s
by lem-weil-derived-limit-existence (1), obtaining L -> P -> P -> L[1].
2. The canonical maps satisfy f_n c_(n+1) = c_n. Their product lift is killed by 1-s.
Hom exactness (lem-weil-pbc-hom-into-triangle-exact) supplies c : E -> L with p_n c = c_n;
no uniqueness of this lift is needed.
3. On a representative, the kernel of the successive lower-truncation quotient has
terms coker d^(a-1) and im d^a in degrees a=-n-1 and a+1. Its cohomology is H^a(E)
in degree a. The complex SES triangle (lem-weil-pbc-complex-ses-triangle) yields
H^(-n-1)(E)[n+1] -> E_(n+1) -> E_n -> H^(-n-1)(E)[n+2].
4. Derived sections preserve this triangle and shifts
(lem-pc-right-derived-functor-triangulated). The long exact sequence
(lem-sf-derived-homology-long-exact) and N >= max(0,-m,d-m+1) show that both degree
m-1 and degree m section-cohomology transitions are isomorphisms for n >= N, uniformly
on B: all three intervening groups have section degree > d and sheaf degree < 0.
5. Apply lem-kun-site-rgamma-derived-limit and lem-pc-derived-limit-milnor-sequence.
The first derived limit vanishes by lem-pc-derived-limit-eventually-iso. The ordinary
limit projects isomorphically to stage N. Thus H^m(V,p_N) is an isomorphism on B.
6. The sheafification of V |-> H^m(V,T) is the underlying abelian sheaf of H^m(T):
exact sheafification commutes with cohomology, and forgetting module scalars is exact
(lem-weil-pbc-site-module-presheaf-sheafification-exact and
lem-weil-pbc-module-sheaves-colimits-forgetful). This is natural for derived morphisms
using K-injective chain-map representatives (lem-weil-pbc-kinjective-hom-derived).
7. A covering by B makes the presheaf map for p_N locally injective and surjective.
By lem-weil-pbc-site-sheafification-iso-locally-bijective its sheafification, hence
H^m(p_N), is invertible.
8. Since N >= -m, H^m(c_N) is invertible. From p_N c = c_N it follows that H^m(c)
is invertible for every m. Represent c by a chain map into a K-injective target;
it is a quasi-isomorphism and is inverted in the derived localization.
9. Transport the distinguished triangle along c. Its first arrow is exactly the
product lift of c_n. Its middle arrow remains 1-s. The final arrow is the old boundary
followed by the shifted inverse of c. This is def-weil-derived-limit, indexed by n+1.
No exactness of products of module sheaves is used. -/
theorem site_truncation_isDerivedLimitTriangle
    {C : Type c} [Category.{v} C] (J : Precoverage C)
    (_hJ : J.IsSiteForCoverings)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max c v r}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J.toGrothendieck RingCat.{max c v r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r} R)]
    (E : DerivedCategory (ringedSiteModules.{max c v r} R))
    (hE : ∃ (d : ℕ) (B : Set C),
      (∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
        ∀ (V : C) (f : V ⟶ U), S f → V ∈ B) ∧
      ∀ (V : C), V ∈ B → ∀ (p : ℤ), (d : ℤ) < p → ∀ (q : ℤ), q < 0 →
        ∀ (I : CochainComplex (ringedSiteModules.{max c v r} R) ℤ)
          (ι : (CochainComplex.singleFunctor (ringedSiteModules.{max c v r} R) 0).obj
            ((DerivedCategory.homologyFunctor (ringedSiteModules.{max c v r} R) q).obj E)
              ⟶ I),
          I.IsKInjective → QuasiIso ι →
            IsZero (((SheafOfModules.toSheaf R ⋙
              sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max c v r} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{max c v r}).obj (op V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I |>.homology p)) :
    ∃ (_ : HasProduct (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
        (C := ringedSiteModules.{max c v r} R)).truncGE (-(n : ℤ))).obj E)),
      ∃ δ : (∏ᶜ (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
          (C := ringedSiteModules.{max c v r} R)).truncGE (-(n : ℤ))).obj E)) ⟶ E⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
          (C := ringedSiteModules.{max c v r} R)).natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (Int.neg_le_neg (Int.ofNat_le.mpr
              (Nat.le_succ n)))).app E) E
          (Pi.lift (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
            (C := ringedSiteModules.{max c v r} R)).truncGEπ (-(n : ℤ))).app E)) δ := by
  classical
  let A := ringedSiteModules.{max c v r} R
  let t := DerivedCategory.TStructure.t (C := A)
  let : ∀ U : Cᵒᵖ, CommRing (R.obj.obj U) := fun U ↦
    { (inferInstance : Ring (R.obj.obj U)) with mul_comm := _hcomm U }
  let Opre : Cᵒᵖ ⥤ CommRingCat.{max c v r} :=
    { obj := fun U ↦ CommRingCat.of (R.obj.obj U)
      map := fun f ↦ CommRingCat.ofHom (R.obj.map f).hom }
  let O : Sheaf J.toGrothendieck CommRingCat.{max c v r} :=
    ⟨Opre, Presheaf.isSheaf_of_isSheaf_comp J.toGrothendieck Opre
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r}) R.property⟩
  have hR : (sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O = R := rfl
  let : HasDerivedCategory.{w} (ringedSiteModules.{max c v r}
      ((sheafCompose J.toGrothendieck
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) := by
    change HasDerivedCategory.{w} A
    infer_instance
  let : Abelian.HasKInjectiveResolutions A :=
    siteModuleKInjectiveResolutions.{c, v, r} J.toGrothendieck O
  let : Abelian.HasKInjectiveResolutions (ringedSiteModules.{max c v r}
      ((sheafCompose J.toGrothendieck
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) :=
    siteModuleKInjectiveResolutions.{c, v, r} J.toGrothendieck O
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v r}
  let K : ℕ → DerivedCategory A := fun n ↦ (t.truncGE (-(n : ℤ))).obj E
  let f : ∀ n : ℕ, K (n + 1) ⟶ K n := fun n ↦
    (t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E
  let c : ∀ n : ℕ, E ⟶ K n := fun n ↦ (t.truncGEπ (-(n : ℤ))).app E
  have hc (n : ℕ) : c (n + 1) ≫ f n = c n := by
    exact t.π_natTransTruncGEOfLE_app _ _ _ E
  have hP : HasProduct K := derived_hasProduct K
  let := hP
  obtain ⟨L, p, δ, hL⟩ := (exists_isDerivedLimit_and_iso K f).1
  let T := Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ
  have hzero : Pi.lift c ≫ towerTransitionEndomorphism f = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.assoc, Category.comp_id,
      Pi.lift_π, Pi.lift_π_assoc, zero_comp, hc, sub_self]
  obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hL (Pi.lift c) hzero
  change E ⟶ L at a
  change Pi.lift c = a ≫ p at ha
  have hap (n : ℕ) : a ≫ p ≫ Pi.π K n = c n := by rw [← Category.assoc, ← ha]; simp
  obtain ⟨d, B, hB, hvan⟩ := hE
  have hhom (m : ℤ) : IsIso ((DerivedCategory.homologyFunctor A m).map a) := by
    let N : ℕ := (max (-m) ((d : ℤ) - m + 1)).toNat
    have hNm : -(N : ℤ) ≤ m := by dsimp [N]; omega
    have hNd : (d : ℤ) - m + 1 ≤ (N : ℤ) := by dsimp [N]; omega
    have hproj : IsIso ((DerivedCategory.homologyFunctor A m).map (p ≫ Pi.π K N)) := by
      apply homology_isIso_of_sections.{c, v, r} J R B hB
      intro V hV
      let F := siteModuleSections.{c, v, r} J.toGrothendieck O V
      obtain ⟨e, he, hT, hπ⟩ := site_rgamma_derivedLimit.{c, v, r}
        J.toGrothendieck O V K f L p δ hL
      let KD := Functor.ofOpSequence
        (X := fun n ↦ F.rightDerivedFunctor.obj (K n))
        (fun n ↦ F.rightDerivedFunctor.map (f n))
      have hst (n : ℕ) (hn : N ≤ n) :=
        truncation_stabilization F E d (hvan V hV) m n (by omega)
      have hT' : IsDerivedLimitTriangle
          (fun n ↦ KD.map (homOfLE (Nat.le_succ n)).op)
          (F.rightDerivedFunctor.obj L) (F.rightDerivedFunctor.map p ≫ e.hom)
          (e.inv ≫ F.rightDerivedFunctor.map δ ≫
            (F.rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app L) := by
        simpa only [KD, Functor.ofOpSequence_map_homOfLE_succ] using hT
      have hi := derivedLimit_projection_isIso KD (F.rightDerivedFunctor.obj L)
        (F.rightDerivedFunctor.map p ≫ e.hom) _ hT' m N (by
          intro n hn
          simpa only [KD, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ]
            using hst n hn)
      have hπ' : F.rightDerivedFunctor.map p ≫ e.hom ≫
          Pi.π (fun n ↦ KD.obj (op n)) N =
            F.rightDerivedFunctor.map (p ≫ Pi.π K N) := hπ N
      rw [Category.assoc, hπ'] at hi
      exact hi
    have htr : IsIso ((DerivedCategory.homologyFunctor A m).map (c N)) :=
      DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E (-(N : ℤ)) m hNm
    have : IsIso ((DerivedCategory.homologyFunctor A m).map a ≫
        (DerivedCategory.homologyFunctor A m).map (p ≫ Pi.π K N)) := by
      rw [← Functor.map_comp, hap]
      exact htr
    exact IsIso.of_isIso_comp_right
      ((DerivedCategory.homologyFunctor A m).map a)
      ((DerivedCategory.homologyFunctor A m).map (p ≫ Pi.π K N))
  have : IsIso a := (DerivedCategory.isIso_iff A a).2 hhom
  refine ⟨hP, δ ≫ (shiftFunctor _ (1 : ℤ)).map (inv a), ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hL _
  refine Pretriangulated.Triangle.isoMk _ _ (asIso a) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change Pi.lift c ≫ 𝟙 _ = a ≫ p
    simpa using ha
  · change towerTransitionEndomorphism _ ≫ 𝟙 _ = 𝟙 _ ≫ towerTransitionEndomorphism f
    simp only [Category.comp_id, Category.id_comp]
    congr 1
  · simp

end CategoryTheory
