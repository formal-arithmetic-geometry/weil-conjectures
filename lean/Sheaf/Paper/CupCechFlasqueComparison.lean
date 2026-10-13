/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import Sheaf.Paper.CupCechTotalComplex
import all Sheaf.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.Topology.Sheaves.CechFlasque
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation

/-! # Comparison through flasque resolution Cech total complexes

Source: Stacks Project, Tags 01EQ and 0FKV.
(blueprint: lem-sc-cup-cech-flasque-comparison)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem flasqueAugmentation_zero {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (J : X.Modules)
    (ht : (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom =
      RingHom.id Γ(X, ⊤))
    (b : (CochainComplex.single₀ (ModuleCat.{u} Γ(X, ⊤))).obj
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj J) ⟶
      (CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat)
    (hb : b.f 0 =
      (ModuleCat.restrictScalarsId'App
        (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom ht
        (J.val.obj (op ⊤))).inv ≫
      Pi.lift fun y : Fin 1 → ι =>
        J.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l => U (y l)))).op) :
    QuasiIsoAt b 0 := by
  let P := J.presheafModuleCat
  let K := (CategoryTheory.cechComplexFunctor U).obj P
  let e := ModuleCat.restrictScalarsId'App
    (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom ht (J.val.obj (op ⊤))
  let r : P.obj (op ⊤) ⟶ K.X 0 := Pi.lift fun y : Fin 1 → ι ↦
    P.map (homOfLE (le_top (a := ∏ᶜ fun l ↦ U (y l)))).op
  have hglue (c : K.X 0) (hc : K.d 0 1 c = 0) :
      ∃ s : P.obj (op ⊤), r s = c := by
    classical
    let π := TopCat.Presheaf.cechComplexFunctorπ (X := X.toTopCat) U P
    let sf (i : ι) : P.obj (op (U i)) :=
      P.map (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U i))).op (π 0 (fun _ ↦ i) c)
    let F := (SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf
      (op ⊤) isTerminalTop.op).obj J
    let G : TopCat.Sheaf (ModuleCat.{u} Γ(X, ⊤)) X.toTopCat := ⟨F.obj, F.property⟩
    have hcompat : TopCat.Presheaf.IsCompatible G.obj U sf := by
      intro i j
      let y : Fin 2 → ι := Fin.cons i (fun _ ↦ j)
      let q : U i ⊓ U j ⟶ ∏ᶜ (fun l ↦ U (y l)) :=
        Pi.lift (Fin.cases (Opens.infLELeft (U i) (U j))
          (fun _ ↦ Opens.infLERight (U i) (U j)))
      have he := congrArg (fun z ↦ P.map q.op (π 1 y z)) hc
      change P.map q.op (π 1 y (((cechComplexFunctor U).obj P).d 0 1 c)) = _ at he
      rw [TopCat.Presheaf.cechComplexFunctorπ_d_apply] at he
      change P.map q.op (∑ x : Fin 2, (-1 : ℤ) ^ x.val •
        P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (x.succAbove l)).op
          (π 0 (y ∘ x.succAbove) c)) = P.map q.op (π 1 y 0) at he
      simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul,
        Fin.val_one, pow_one, neg_smul, map_add, map_neg, map_zero] at he
      have ht0 : y ∘ (0 : Fin 2).succAbove = (fun _ ↦ j) := by
        funext k
        fin_cases k
        rfl
      have ht1 : y ∘ (1 : Fin 2).succAbove = (fun _ ↦ i) := by
        funext k
        fin_cases k
        rfl
      have transport {a b : Fin 1 → ι} (hab : a = b)
          (f : U i ⊓ U j ⟶ ∏ᶜ (fun l ↦ U (a l)))
          (g : U i ⊓ U j ⟶ ∏ᶜ (fun l ↦ U (b l))) :
          P.map f.op (π 0 a c) = P.map g.op (π 0 b c) := by
        subst b
        rw [Subsingleton.elim f g]
      have face0 : P.map q.op
          (P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l))
            ((0 : Fin 2).succAbove l)).op (π 0 (y ∘ (0 : Fin 2).succAbove) c)) =
          P.map (Opens.infLERight (U i) (U j)).op (sf j) := by
        let f : (∏ᶜ fun l ↦ U (y l)) ⟶
            ∏ᶜ (fun l ↦ U ((y ∘ (0 : Fin 2).succAbove) l)) :=
          Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) ((0 : Fin 2).succAbove l)
        let g : U i ⊓ U j ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U j) :=
          Opens.infLERight (U i) (U j) ≫ Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U j))
        exact (TopCat.Presheaf.map_map_apply P f.op q.op (q ≫ f).op
          (π 0 (y ∘ (0 : Fin 2).succAbove) c)).trans
            ((transport ht0 (q ≫ f) g).trans
              (TopCat.Presheaf.map_map_apply P
                (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U j))).op
                (Opens.infLERight (U i) (U j)).op g.op (π 0 (fun _ ↦ j) c)).symm)
      have face1 : P.map q.op
          (P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l))
            ((1 : Fin 2).succAbove l)).op (π 0 (y ∘ (1 : Fin 2).succAbove) c)) =
          P.map (Opens.infLELeft (U i) (U j)).op (sf i) := by
        let f : (∏ᶜ fun l ↦ U (y l)) ⟶
            ∏ᶜ (fun l ↦ U ((y ∘ (1 : Fin 2).succAbove) l)) :=
          Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) ((1 : Fin 2).succAbove l)
        let g : U i ⊓ U j ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) :=
          Opens.infLELeft (U i) (U j) ≫ Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U i))
        exact (TopCat.Presheaf.map_map_apply P f.op q.op (q ≫ f).op
          (π 0 (y ∘ (1 : Fin 2).succAbove) c)).trans
            ((transport ht1 (q ≫ f) g).trans
              (TopCat.Presheaf.map_map_apply P
                (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U i))).op
                (Opens.infLELeft (U i) (U j)).op g.op (π 0 (fun _ ↦ i) c)).symm)
      rw [face0, face1] at he
      exact (add_neg_eq_zero.mp he).symm
    obtain ⟨s, hs, _⟩ := G.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
      (by rw [hU]) sf hcompat
    refine ⟨s, ?_⟩
    apply TopCat.Presheaf.cechComplexFunctor_ext (X := X.toTopCat) U P
    intro y
    have hy : y = (fun _ ↦ y 0) := by
      funext k
      fin_cases k
      rfl
    obtain ⟨i, rfl⟩ : ∃ i, y = (fun _ ↦ i) := ⟨y 0, hy⟩
    have h := congrArg (fun z ↦ P.map (Pi.π (fun _ : Fin 1 ↦ U i) 0).op z) (hs i)
    change P.map (Pi.π (fun _ : Fin 1 ↦ U i) 0).op
      (P.map (homOfLE le_top).op s) = _ at h
    dsimp only [sf] at h
    rw [TopCat.Presheaf.map_map_apply P _ _ (𝟙 _),
      P.map_id, ConcreteCategory.id_apply] at h
    rw [TopCat.Presheaf.map_map_apply P _ _ (homOfLE le_top).op] at h
    have hr : (Pi.lift (fun y : Fin 1 → ι ↦ P.map (homOfLE le_top).op)) ≫
        Pi.π (fun y : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))) (fun _ ↦ i) =
        P.map (homOfLE le_top).op := Pi.lift_π _ _
    change (Pi.π (fun y : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))))
      (fun _ ↦ i) ((Pi.lift (fun y : Fin 1 → ι ↦ P.map (homOfLE le_top).op)) s) = _
    rw [← ConcreteCategory.comp_apply]
    change ((Pi.lift (fun y : Fin 1 → ι ↦ P.map (homOfLE le_top).op)) ≫
        Pi.π (fun y : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))) (fun _ ↦ i)) s = _
    rw [hr]
    exact h
  have hmono : Mono r := by
    apply (ModuleCat.mono_iff_injective r).mpr
    intro s t hst
    let F := (SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op ⊤) isTerminalTop.op).obj J
    have hF : TopCat.Presheaf.IsSheaf (X := X.toTopCat) F.obj := F.property
    let G : TopCat.Sheaf (ModuleCat.{u} Γ(X, ⊤)) X.toTopCat := ⟨F.obj, hF⟩
    apply G.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) (by rw [hU]) s t
    intro i
    have hi := congrArg
      (fun z ↦ (Pi.π (fun y : Fin 1 → ι ↦
        P.obj (op (∏ᶜ fun l ↦ U (y l))))) (fun _ ↦ i) z) hst
    have hi' : P.map (homOfLE (le_top (a := ∏ᶜ fun _ : Fin 1 ↦ U i))).op s =
        P.map (homOfLE (le_top (a := ∏ᶜ fun _ : Fin 1 ↦ U i))).op t := by
      have hr : r ≫ Pi.π (fun y : Fin 1 → ι ↦
          P.obj (op (∏ᶜ fun l ↦ U (y l)))) (fun _ ↦ i) =
          P.map (homOfLE le_top).op := Pi.lift_π _ _
      exact (ConcreteCategory.congr_hom hr s).symm.trans
        (hi.trans (ConcreteCategory.congr_hom hr t))
    have hq : U i ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) := Pi.lift fun _ ↦ 𝟙 _
    have he := congrArg (fun z ↦ P.map hq.op z) hi'
    change P.map (homOfLE le_top).op s = P.map (homOfLE le_top).op t
    simpa only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
      Subsingleton.elim (hq ≫ homOfLE le_top) (homOfLE le_top)] using he
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros _ rfl rfl (K.shape _ _ (by simp))]
  constructor
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    obtain ⟨s, hs⟩ := hglue c hc
    refine ⟨e.hom s, ?_⟩
    change b.f 0 (e.hom s) = c
    rw [hb]
    change (e.inv ≫ r) (e.hom s) = c
    rw [← ConcreteCategory.comp_apply, e.hom_inv_id_assoc]
    exact hs
  · change Mono (b.f 0)
    rw [hb]
    change Mono (e.inv ≫ r)
    infer_instance


private theorem flasqueAugmentation {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (J : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf
      (moduleRings X.toRingedSpace)).obj J)]
    (ht : (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom =
      RingHom.id Γ(X, ⊤))
    (b : (CochainComplex.single₀ (ModuleCat.{u} Γ(X, ⊤))).obj
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj J) ⟶
      (CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat)
    (hb : b.f 0 =
      (ModuleCat.restrictScalarsId'App
        (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom ht
        (J.val.obj (op ⊤))).inv ≫
      Pi.lift fun y : Fin 1 → ι ↦
        J.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l ↦ U (y l)))).op) :
    QuasiIso b := by
  rw [quasiIso_iff]
  intro n
  by_cases hn : n = 0
  · subst n
    exact flasqueAugmentation_zero U hU J ht b hb
  · apply (quasiIsoAt_iff_isIso_homologyMap _ _).2
    have hs := HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℕ) 0
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj J) n hn
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj J
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have he := TopCat.Sheaf.exactAt_cechComplex_of_isFlasque U q F
    have hz := he.isZero_homology
    have hz' : IsZero ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).obj
        (((CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat).homology
          (q + 1))) :=
      hz.of_iso (TopCat.Presheaf.cechComplexFunctorHomologyIso U J.presheafModuleCat
        (q + 1))
    have htgt : IsZero
        (((CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat).homology
          (q + 1)) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      exact (AddCommGrpCat.isZero_iff_subsingleton.mp hz')
    exact hs.isIso htgt _

private theorem flasqueAlpha_isIso {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) {F : X.Modules} (I : CupAcyclicResolution F)
    (hI : ∀ n : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (I.K.X n))) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cupCechAlpha U I) p) := by
  let symmetry : TotalComplexShapeSymmetry
      (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
    { symm := fun i j ↦ Nat.add_comm j i
      σ := fun i j ↦ (-1 : ℤˣ) ^ (i * j)
      σ_ε₁ := by
        rintro i _ rfl j
        dsimp
        rw [mul_one, Nat.add_mul, one_mul, pow_add, mul_left_comm,
          Int.units_mul_self, mul_one]
      σ_ε₂ := by
        rintro i j _ rfl
        dsimp
        rw [one_mul, Nat.mul_add, Nat.mul_one, pow_add] }
  let K := cupCechDouble U I.K
  let A := cupSections I
  let a : A ⟶ K.flip.X 0 :=
    { f := fun n ↦ moduleCechZero U (I.K.X n)
      comm' := fun n m _ ↦ by
        change moduleCechZero U (I.K.X n) ≫
            ((CategoryTheory.cechComplexFunctor U).map
              ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
                (I.K.d n m).val)).f 0 =
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).map
            (I.K.d n m) ≫ moduleCechZero U (I.K.X m)
        exact moduleCechZero_naturality U (I.K.d n m) }
  have ha : a ≫ K.flip.d 0 1 = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    change moduleCechZero U (I.K.X n) ≫
      ((CategoryTheory.cechComplexFunctor U).obj
        (I.K.X n).presheafModuleCat).d 0 1 = 0
    exact moduleCechZero_d U (I.K.X n)
  let b := cupCechAlpha U I ≫ (K.totalFlipIso (ComplexShape.up ℕ)).inv
  have hb : ∀ n : ℕ, b.f n = a.f n ≫
      K.flip.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) := by
    intro n
    dsimp only [b, HomologicalComplex.comp_f, cupCechAlpha,
      cupCechAlphaComponent, a]
    rw [Category.assoc, K.ιTotal_totalFlipIso_f_inv]
    change (1 : ℤˣ) • moduleCechZero U (I.K.X n) ≫
      K.flip.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) = _
    simp only [one_smul]
  have hcol : ∀ n : ℕ, QuasiIso
      ((CochainComplex.fromSingle₀Equiv (K.flip.flip.X n) (A.X n)).symm
        ⟨a.f n, by simpa using congrArg (fun f ↦ f.f n) ha⟩) := by
    intro n
    have := hI n
    apply flasqueAugmentation U hU (I.K.X n)
      (moduleCech_top_restriction X)
    dsimp [a, moduleCechZero, CochainComplex.fromSingle₀Equiv]
    rfl
  have : QuasiIso b :=
    HomologicalComplex₂.quasiIso_of_column_augmentation K.flip A a ha b hb hcol
  have : QuasiIso (cupCechAlpha U I) :=
    quasiIso_of_comp_right (cupCechAlpha U I)
      (K.totalFlipIso (ComplexShape.up ℕ)).inv
  infer_instance

private theorem cupCech_comparison_squares {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : CupAcyclicResolution F)
    (J : InjectiveResolution F) (ψ : I.K ⟶ J.cocomplex)
    (hψ : I.augmentation.f 0 ≫ ψ.f 0 = J.ι.f 0) :
    let T := HomologicalComplex₂.total.map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
          CategoryTheory.cechComplexFunctor U).mapHomologicalComplex
            (ComplexShape.up ℕ) |>.map ψ) (ComplexShape.up ℕ)
    cupCechAlpha U I ≫ T =
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ψ ≫ moduleCechAlpha U J ∧
    cupCechBeta U I ≫ T =
      moduleCechBeta U J := by
  dsimp only
  constructor
  · apply HomologicalComplex.Hom.ext
    funext n
    dsimp only [HomologicalComplex.comp_f, cupCechAlpha, cupCechAlphaComponent, moduleCechAlpha,
      moduleCechAlphaComponent]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    dsimp [moduleCechZero]
    apply Pi.hom_ext
    intro y
    simp only [CategoryTheory.cechComplexFunctor,
      FormalCoproduct.cochainComplexFunctor_map_f, Functor.rightOp_obj, homOfLE_leOfHom,
      Functor.mapHomologicalComplex_map_f, Functor.comp_map, SheafOfModules.forget_map,
      PresheafOfModules.forgetToPresheafModuleCat_map, Category.assoc, Pi.map_π]
    change _ ≫ (Pi.lift fun z : Fin 1 → ι =>
      (I.K.X n).presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l => U (z l)))).op) ≫
        Pi.π _ y ≫ _ =
      _ ≫ _ ≫ (Pi.lift fun z : Fin 1 → ι =>
        (J.cocomplex.X n).presheafModuleCat.map
          (homOfLE (le_top (a := ∏ᶜ fun l => U (z l)))).op) ≫ Pi.π _ y
    simp only [Pi.lift_π_assoc, Pi.lift_π]
    ext x
    exact PresheafOfModules.naturality_apply (ψ.f n).val
      (homOfLE (le_top (a := ∏ᶜ fun l => U (y l)))).op x
  · apply HomologicalComplex.Hom.ext
    funext n
    dsimp only [HomologicalComplex.comp_f, cupCechBeta, cupCechBetaComponent, moduleCechBeta,
      moduleCechBetaComponent]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
    let C := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U
    change (C.map (I.augmentation.f 0)).f n ≫ (C.map (ψ.f 0)).f n ≫ _ =
      (C.map (J.ι.f 0)).f n ≫ _
    rw [← Category.assoc, ← HomologicalComplex.comp_f, ← C.map_comp, hψ]
    rfl

/-- Alpha for a flasque resolution is invertible on homology, and equality of alpha
and beta classes is exactly the canonical Cech comparison equation.
Source: Stacks Project, Tags 01EQ, 0FKV (flasque-resolution diagram).
(blueprint: lem-sc-cup-cech-flasque-comparison)

Proof: each term of D.K is Cech-acyclic for a covering, and its zeroth Cech
cohomology is its global sections. The first-quadrant column augmentation
criterion makes cupCechAlpha a quasi-isomorphism. Apply the Cech functor to
D.comparison. Restrictions commute with its components, giving the alpha square;
D.over gives the beta square. On homology the global comparison is invertible
by D.computes, while the injective alpha is invertible by moduleCechAlpha_isIso.
The defining equation hc for D.I and these squares imply the stated class
identity, after cancelling the injective alpha and the resolution identification.
The argument works in degree zero and for empty schemes: it only cancels these
isomorphisms and never assumes the represented class is nonzero. -/
theorem cupCech_flasque_comparison {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) {F : X.Modules}
    (D : CupAcyclicResolution F)
    (hD : ∀ n : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (D.K.X n))) :
    QuasiIso (cupCechAlpha U D) ∧
    ∀ (n : ℕ)
      (c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology n ⟶
        (RingedSpace.moduleCohomology X.toRingedSpace n).obj F),
      IsModuleCechComparison U F n c →
      ∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc n).moduleCatLeftHomologyData.K)
        (b : ((cupSections D).sc n).moduleCatLeftHomologyData.K),
        HomologicalComplex.homologyMap (cupCechAlpha U D) n (cupCycleClass _ n b) =
          HomologicalComplex.homologyMap (cupCechBeta U D) n (cupCycleClass _ n a) →
        D.class n b = c (cupCycleClass _ n a)  := by
  constructor
  · rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).2 (flasqueAlpha_isIso U hU D hD n)
  · intro n c hc a b hab
    let : EnoughInjectives X.Modules :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
    let T := HomologicalComplex₂.total.map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
          CategoryTheory.cechComplexFunctor U).mapHomologicalComplex
            (ComplexShape.up ℕ) |>.map D.comparison) (ComplexShape.up ℕ)
    let g := ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).map D.comparison
    have hzero : D.augmentation.f 0 ≫ D.comparison.f 0 = D.I.ι.f 0 :=
      congrArg (fun f ↦ f.f 0) D.over
    obtain ⟨hα, hβ⟩ := cupCech_comparison_squares U D D.I D.comparison hzero
    have hα' := congrArg (fun f ↦ HomologicalComplex.homologyMap f n) hα
    have hβ' := congrArg (fun f ↦ HomologicalComplex.homologyMap f n) hβ
    simp only [HomologicalComplex.homologyMap_comp] at hα' hβ'
    have heq : HomologicalComplex.homologyMap (moduleCechAlpha U D.I) n
        (HomologicalComplex.homologyMap g n (cupCycleClass _ n b)) =
        HomologicalComplex.homologyMap (moduleCechBeta U D.I) n
          (cupCycleClass _ n a) := by
      calc
        _ = HomologicalComplex.homologyMap T n
            (HomologicalComplex.homologyMap (cupCechAlpha U D) n
              (cupCycleClass _ n b)) := (ConcreteCategory.congr_hom hα' _).symm
        _ = HomologicalComplex.homologyMap T n
            (HomologicalComplex.homologyMap (cupCechBeta U D) n
              (cupCycleClass _ n a)) := by rw [hab]
        _ = _ := ConcreteCategory.congr_hom hβ' _
    have hcan := ConcreteCategory.congr_hom (hc D.I) (cupCycleClass _ n a)
    have := moduleCechAlpha_isIso U hU D.I n
    have hinj := (ModuleCat.mono_iff_injective
      (HomologicalComplex.homologyMap (moduleCechAlpha U D.I) n)).mp inferInstance
    have hclass := hinj (heq.trans hcan.symm)
    change (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
      (HomologicalComplex.homologyMap g n (cupCycleClass _ n b)) = _
    rw [hclass]
    exact ConcreteCategory.congr_hom
      (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).hom_inv_id
      (c (cupCycleClass _ n a))

end
end AlgebraicGeometry.Scheme.Modules
