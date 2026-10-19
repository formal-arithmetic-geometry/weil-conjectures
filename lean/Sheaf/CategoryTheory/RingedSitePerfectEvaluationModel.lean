/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps

import Sheaf.CategoryTheory.RingedSiteStrictPerfectEvaluation
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Sites.LocalProperties
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # RingedSitePerfectEvaluationModel

Source: Stacks Project, Tag 08JJ (blueprint: lem-sfb-perfect-evaluation-model).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u v' u' w' s
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem evaluation_isIso_of_iso
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (O : D) (u : S.monoidal.tensorUnit ≅ O)
    {P Q : D} (e : P ≅ Q) (N : D)
    (hQ : IsIso (ringedSiteDualEvaluation S O u Q N)) :
    IsIso (ringedSiteDualEvaluation S O u P N) := by
  have := hQ
  let d := H.mapIso (Iso.prod e.op (Iso.refl O))
  have hd : IsIso (H.map (Prod.mkHom e.hom.op (𝟙 O))) := d.isIso_hom
  have hn : IsIso (H.map (Prod.mkHom e.hom.op (𝟙 N))) :=
    (H.mapIso (Iso.prod e.op (Iso.refl N))).isIso_hom
  have ht : IsIso (S.tensor.map (Prod.mkHom (𝟙 N)
      (H.map (Prod.mkHom e.hom.op (𝟙 O))))) :=
    (S.tensor.mapIso (Iso.prod (Iso.refl N) d)).isIso_hom
  have : IsIso (S.tensor.map (Prod.mkHom (𝟙 N)
      (H.map (Prod.mkHom e.hom.op (𝟙 O)))) ≫ ringedSiteDualEvaluation S O u P N) := by
    rw [ringedSiteDualEvaluation_source_naturality S O u e.hom N]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (S.tensor.map (Prod.mkHom (𝟙 N) (H.map (Prod.mkHom e.hom.op (𝟙 O))))) _


section Detection
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{max c v r})
  (P : C → Prop)
  (hP : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃U : C⦄ (f : U ⟶ V), S f → P U)

include hP in
private theorem module_isIso_of_local
    {X Y : SheafOfModules.{max c v r} R} (f : X ⟶ Y)
    (h : ∀ U, P U → IsIso ((SheafOfModules.overFunctor.{max c v r} R U).map f)) : IsIso f := by
  have hcover : J.CoversTop (fun U : { U : C // P U } ↦ U.val) := by
    intro V
    obtain ⟨S, hS, hs⟩ := hP V
    apply J.superset_covering _ hS
    intro U g hg
    exact ⟨⟨U, hs g hg⟩, ⟨𝟙 U⟩⟩
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply Sheaf.isIso_of_coversTop hcover
    intro U
    have := h U.val U.property
    exact Functor.map_isIso (SheafOfModules.toSheaf (R.over U.val))
      ((SheafOfModules.overFunctor.{max c v r} R U.val).map f)
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

section Complex
variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R' : Sheaf J CommRingCat.{max c v r})


include hP in
private theorem complex_quasiIso_of_local
    {X Y : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R')) ℤ} (f : X ⟶ Y)
    (h : ∀ U, P U → QuasiIso
      (((SheafOfModules.overFunctor.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R') U).mapHomologicalComplex
          (.up ℤ)).map f)) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply module_isIso_of_local.{c, v, r} J ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R') P hP
  intro U hU
  let F := SheafOfModules.localizedSystemRestriction.{c, v, r} R' U
  have := h U hU
  have hs : IsIso (ShortComplex.homologyMap
      (F.mapShortComplex.map ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) n).map f))) := by
    change IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) n)
    infer_instance
  have he := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) n).map f) F
  change IsIso (F.map (HomologicalComplex.homologyMap f n))
  have heq : F.map (HomologicalComplex.homologyMap f n) =
      ((X.sc n).mapHomologyIso F).inv ≫
      ShortComplex.homologyMap
        (F.mapShortComplex.map ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) n).map f)) ≫
      ((Y.sc n).mapHomologyIso F).hom := by
    rw [he, ← Category.assoc]
    simp
    rfl
  rw [heq]
  infer_instance

end Complex

end Detection
section DerivedDetection
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {I : Type s} {B : I → Type u'} [∀ i, Category.{v'} (B i)] [∀ i, Abelian (B i)]
  [∀ i, HasDerivedCategory.{w'} (B i)]
  (G : ∀ i, CochainComplex A ℤ ⥤ CochainComplex (B i) ℤ)
  (F : ∀ i, DerivedCategory A ⥤ DerivedCategory (B i))
  (e : ∀ i, DerivedCategory.Q ⋙ F i ≅ G i ⋙ DerivedCategory.Q)
  (hG : ∀ ⦃X Y : CochainComplex A ℤ⦄ (f : X ⟶ Y),
    (∀ i, QuasiIso ((G i).map f)) → QuasiIso f)

include e hG in
private theorem derived_isIso_of_local_Q
    {X Y : CochainComplex A ℤ} (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y)
    (hf : ∀ i, IsIso ((F i).map f)) : IsIso f := by
  obtain ⟨X', s, hs, g, hfg⟩ := DerivedCategory.right_fac f
  have hg : ∀ i, QuasiIso ((G i).map g) := by
    intro i
    have := hf i
    have hq : IsIso ((F i).map (DerivedCategory.Q.map g)) := by
      rw [hfg] at hf
      have : IsIso ((F i).map (inv (DerivedCategory.Q.map s)) ≫
          (F i).map (DerivedCategory.Q.map g)) := by
        simpa only [Functor.map_comp] using hf i
      exact IsIso.of_isIso_comp_left ((F i).map (inv (DerivedCategory.Q.map s))) _
    have hn := (e i).hom.naturality g
    dsimp at hn
    have heq : DerivedCategory.Q.map ((G i).map g) =
        (e i).inv.app X' ≫ (F i).map (DerivedCategory.Q.map g) ≫ (e i).hom.app Y := by
      rw [hn, ← Category.assoc]
      simp
    have : IsIso (DerivedCategory.Q.map ((G i).map g)) := by
      rw [heq]
      infer_instance
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (B i) _).mp inferInstance
  have := hG g hg
  rw [hfg]
  infer_instance

include e hG in
private theorem derived_isIso_of_local
    {X Y : DerivedCategory A} (f : X ⟶ Y)
    (hf : ∀ i, IsIso ((F i).map f)) : IsIso f := by
  let eX := DerivedCategory.Q.objObjPreimageIso X
  let eY := DerivedCategory.Q.objObjPreimageIso Y
  let g := eX.hom ≫ f ≫ eY.inv
  have hg : ∀ i, IsIso ((F i).map g) := by
    intro i
    have := hf i
    dsimp only [g]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  have : IsIso g := derived_isIso_of_local_Q G F e hG g hg
  have he : f = eX.inv ≫ g ≫ eY.hom := by simp [g]
  rw [he]
  infer_instance

end DerivedDetection

set_option maxHeartbeats 800000 in
-- Comparing scalar restriction with the original functor uses independent universes.
/-- Canonical unsigned evaluation for a locally strictly perfect source model.
Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final paragraph.
Proof: a bounded finite-free-retract model on each member of the given covering
sieves satisfies the strict evaluation theorem. Source naturality transports
invertibility along its quasi-isomorphism to the restricted original complex.
The canonical tensor and Hom restriction comparisons then identify this map with
the restriction of the global evaluation. Exact restriction commutes with
homology, and the covering-sheaf criterion jointly detects isomorphisms of
homology sheaves. It therefore detects quasi-isomorphisms of complexes. A
right-fraction presentation of an arbitrary derived morphism reduces detection
of its invertibility to this criterion for complexes. Applied to evaluation,
this proves the global claim, including for arbitrary unbounded targets.
(blueprint: lem-sfb-perfect-evaluation-model). -/
theorem ringedSitePerfectEvaluation_model
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (K : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hK : SheafOfModules.IsLocallyStrictPerfectComplexOfUniverses.{c, v, r} R K)
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (N : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    : IsIso (ringedSiteDualEvaluation M.closed
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso (DerivedCategory.Q.obj K) N) := by
  classical
  let A := SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let AU (U : C) := SheafOfModules.{max c v r} ((sheafCompose (J.over U)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U))
  let : ∀ U, HasDerivedCategory (AU U) := fun U ↦ HasDerivedCategory.standard (AU U)
  let MU (U : C) := Classical.choice
    (ringedSiteDualityMaps_exists.{max c v, v, r} (J.over U) (R.over U))
  have hr (U : C) := ringedSiteDualityMaps_restriction.{c, v, r, w} J R M U (MU U)
  choose F e t h o he hb hd using hr
  let eF (U : C) := Classical.choice (e U)
  let G (U : C) := ringedSiteDualityRestrictionComplex.{c, v, r} J R U
  have hG_eq (U : C) : G U =
      (SheafOfModules.overFunctor.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U
          ).mapHomologicalComplex (.up ℤ) := by rfl
  let P (U : C) : Prop :=
    ∃ E : CochainComplex (AU U) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
      Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) ∧
      ∃ α : E ⟶ (G U).obj K, QuasiIso α
  have hcover : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
      ∀ ⦃U : C⦄ (f : U ⟶ V), S f → P U := by
    intro V
    obtain ⟨S, hS, hs⟩ := hK V
    refine ⟨S, hS, ?_⟩
    intro U f hf
    dsimp only [P]
    rw [hG_eq]
    exact hs U f hf
  let I := { U : C // P U }
  have hG : ∀ ⦃X Y : CochainComplex A ℤ⦄ (f : X ⟶ Y),
      (∀ U : I, QuasiIso ((G U.val).map f)) → QuasiIso f := by
    intro X Y f hf
    apply complex_quasiIso_of_local.{c, v, r} J P hcover R f
    intro U hU
    have hx := hf ⟨U, hU⟩
    rw [hG_eq] at hx
    exact hx
  apply derived_isIso_of_local (fun U : I ↦ G U.val) (fun U : I ↦ F U.val)
    (fun U : I ↦ eF U.val) hG
  intro U
  obtain ⟨E, hE, ⟨pkg⟩, α, hα⟩ := U.property
  have : IsIso (DerivedCategory.Q.map α) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hα
  let eK : DerivedCategory.Q.obj E ≅ (F U.val).obj (DerivedCategory.Q.obj K) :=
    asIso (DerivedCategory.Q.map α) ≪≫ ((eF U.val).app K).symm
  let HU := derivedInternalHomOfUniverses.{max c v, v, r} (J.over U.val) (R.over U.val)
  have hstrict := ringedSiteStrictPerfectEvaluation.{max c v, v, r}
    (J.over U.val) (R.over U.val) E hE pkg (MU U.val) ((F U.val).obj N)
  have hlocal : IsIso (ringedSiteDualEvaluation (MU U.val).closed
      (ringedSiteDualityUnit.{max c v, v, r} (J.over U.val) (R.over U.val))
      (MU U.val).unitIso ((F U.val).obj (DerivedCategory.Q.obj K)) ((F U.val).obj N)) :=
    evaluation_isIso_of_iso (MU U.val).closed _ (MU U.val).unitIso
      eK.symm ((F U.val).obj N) hstrict
  have hres := hd U.val (DerivedCategory.Q.obj K) N
  let d := HU.mapIso (Iso.prod (Iso.refl (op ((F U.val).obj (DerivedCategory.Q.obj K))))
    (o U.val))
  have : IsIso ((MU U.val).closed.tensor.map (Prod.mkHom (𝟙 ((F U.val).obj N))
      ((h U.val).hom.app
        (op (DerivedCategory.Q.obj K), ringedSiteDualityUnit.{c, v, r, w} J R)))) :=
    ((MU U.val).closed.tensor.mapIso (Iso.prod (Iso.refl ((F U.val).obj N))
      ((h U.val).app (op (DerivedCategory.Q.obj K),
        ringedSiteDualityUnit.{c, v, r, w} J R)))).isIso_hom
  have : IsIso ((MU U.val).closed.tensor.map (Prod.mkHom (𝟙 ((F U.val).obj N))
      (HU.map (Prod.mkHom (𝟙 (op ((F U.val).obj (DerivedCategory.Q.obj K))))
        (o U.val).hom)))) :=
    ((MU U.val).closed.tensor.mapIso (Iso.prod (Iso.refl ((F U.val).obj N)) d)).isIso_hom
  have : IsIso ((F U.val).map (ringedSiteDualEvaluation M.closed
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso (DerivedCategory.Q.obj K) N) ≫
      (h U.val).hom.app (op (DerivedCategory.Q.obj K), N)) := by
    rw [hres]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((h U.val).hom.app (op (DerivedCategory.Q.obj K), N))

end CategoryTheory
