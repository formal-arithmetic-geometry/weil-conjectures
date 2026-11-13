/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.AlternatingCechRestrictionHomotopy
import all WeilConjectures.AlgebraicGeometry.InjectiveAlternatingCechRowAugmentation
import WeilConjectures.Topology.Sheaves.CechFlasque

/-! # The increasing-tuple augmented Čech row of a flasque module

## References

* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem flasqueAlternatingRow_positive {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (_hU : iSup U = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M)]
    (p : ℕ) (hp : 0 < p) :
    (alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj M)).ExactAt p := by
  let P := (alternatingCechModulePresheaf (X := X)).obj M
  let F := P ⋙ forget₂ _ AddCommGrpCat
  let S := intersectionCech U
  let A := ((forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (alternatingCechComplex U P)
  let e : ∀ p : ℕ, A.X p ≅ AddCommGrpCat.of
      (∀ t : {t : Fin (p + 1) → Fin r // StrictMono t}, F.obj (op (S.W p t.1))) :=
    fun p ↦
      { hom := AddCommGrpCat.ofHom
          { toFun := fun s t ↦ s (OrderEmbedding.ofStrictMono t.1 t.2)
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        inv := AddCommGrpCat.ofHom
          { toFun := fun s t ↦ s ⟨t, t.strictMono⟩
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        hom_inv_id := by apply AddCommGrpCat.ext; intro s; funext t; rfl
        inv_hom_id := by apply AddCommGrpCat.ext; intro s; funext t; rfl }
  let q : S.complex F ⟶ A := CochainComplex.ofHom
    (fun p ↦ AddCommGrpCat.ofHom
      { toFun := fun s t ↦ s t
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }) (by
      intro p
      apply AddCommGrpCat.ext
      intro s
      funext t
      simp only [SiteCechComplex.complex, A, alternatingCechComplex,
        Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
      change (alternatingCechDifferential U P p).hom
        (fun t : Fin (p + 1) ↪o Fin r ↦ s t) t = (S.differentialValue F p s) t
      rw [alternatingRow_d_apply]
      rfl)
  have hq : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → Fin r // StrictMono t}),
      (e p).hom ((q.f p) s) t = s t.1 := by intros; rfl
  obtain ⟨i, ⟨hqi⟩, ⟨hiq⟩⟩ :=
    Scheme.alternatingCechRestrictionHomotopy X U F S A e q hq
  let E : HomotopyEquiv (S.complex F) A := ⟨q, i, hqi, hiq⟩
  let T := (TopCat.Presheaf.cechComplex U).obj F
  let j : S.complex F ≅ T := HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ Iso.refl _) (by
      rintro n m rfl
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      apply AddCommGrpCat.ext
      intro s
      funext t
      simp only [SiteCechComplex.complex, CochainComplex.of_d]
      change T.d n (n + 1) s t = (S.differentialValue F n s) t
      rw [TopCat.Presheaf.cechComplex_d_apply]
      rfl)
  have hfl : TopCat.Presheaf.IsFlasque F := by
    constructor
    intro V W i
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact (AddCommGrpCat.epi_iff_surjective
      (((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M).obj.map i)).mp
        inferInstance
  let Afl := (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M
  have heq : F = Afl.obj := rfl
  have hfull : T.ExactAt p := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
    change ((TopCat.Presheaf.cechComplex U).obj F).ExactAt (q + 1)
    rw [heq]
    exact TopCat.Sheaf.exactAt_cechComplex_of_isFlasque U q Afl
  have hz : IsZero ((S.complex F).homology p) :=
    hfull.isZero_homology.of_iso (HomologicalComplex.homologyMapIso j p)
  have hz' : IsZero (A.homology p) := hz.of_iso (E.toHomologyIso p).symm
  have he : A.ExactAt p := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hz'
  rw [HomologicalComplex.exactAt_iff' _ (p - 1) p (p + 1) (ComplexShape.prev_eq' (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel (p - 1) p from by change p - 1 + 1 = p; omega)) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rw [HomologicalComplex.exactAt_iff' _ (p - 1) p (p + 1) (ComplexShape.prev_eq' (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel (p - 1) p from by change p - 1 + 1 = p; omega)) (by simp),
    ShortComplex.ab_exact_iff] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- The actual increasing-tuple row augmentation is a quasi-isomorphism. Its degree-zero
component is specified, so the map is uniquely determined.
(Stacks, Tags 09SZ, 01EP and 01FM.) -/
theorem flasque_alternatingCech_row_augmentation
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M)] :
    ∃ f : (HomologicalComplex.single
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (ComplexShape.up ℤ) 0).obj
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M) ⟶
          (alternatingCechModuleFunctor U).obj M,
      f.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)).hom ≫
          alternatingCechZero U M ∧ QuasiIso f := by
  let P := (alternatingCechModulePresheaf (X := X)).obj M
  let C := alternatingCechComplex U P
  let V := (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M
  let e := ModuleCat.restrictScalarsId'App
    ((moduleRings X.toRingedSpace).obj.map (isTerminalTop.op.to (op ⊤))).hom
    (Scheme.Modules.moduleCech_top_restriction X) (M.val.obj (op ⊤))
  let z : V ⟶ C.X 0 := e.inv ≫ alternatingCechPresheafZero U P
  have hz : z ≫ C.d 0 1 = 0 := by
    rw [Category.assoc, alternatingRow_zero_d, comp_zero]
  let b := (CochainComplex.fromSingle₀Equiv C V).symm ⟨z, hz⟩
  have hb : b.f 0 = z := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero z hz
  have hmono : Mono (alternatingCechPresheafZero U P) := alternatingRow_mono U hU M
  have hbq : QuasiIso b := by
    rw [quasiIso_iff]
    intro p
    by_cases hp : p = 0
    · subst p
      rw [CochainComplex.quasiIsoAt₀_iff]
      rw [ShortComplex.quasiIso_iff_of_zeros _ rfl rfl (C.shape _ _ (by simp))]
      constructor
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro c hc
        obtain ⟨s, hs⟩ := alternatingRow_glue U hU M c hc
        refine ⟨e.hom s, ?_⟩
        change b.f 0 (e.hom s) = c
        rw [hb]
        change (e.inv ≫ alternatingCechPresheafZero U P) (e.hom s) = c
        rw [← ConcreteCategory.comp_apply, e.hom_inv_id_assoc]
        exact hs
      · change Mono (b.f 0)
        rw [hb]
        change Mono (e.inv ≫ alternatingCechPresheafZero U P)
        infer_instance
    · apply (quasiIsoAt_iff_exactAt b p ?_).mpr (flasqueAlternatingRow_positive U hU M p (by omega))
      exact HomologicalComplex.exactAt_single_obj (ComplexShape.up ℕ) 0 V p hp
  have := hbq
  let E := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat V 0 0 rfl
  let f := E.inv ≫ HomologicalComplex.extendMap b ComplexShape.embeddingUpNat
  refine ⟨f, ?_, by dsimp [f]; infer_instance⟩
  dsimp only [f, HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f b ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hb]
  dsimp only [z]
  simp [alternatingCechZero, P, C, V, e, Category.assoc,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

end AlgebraicGeometry
