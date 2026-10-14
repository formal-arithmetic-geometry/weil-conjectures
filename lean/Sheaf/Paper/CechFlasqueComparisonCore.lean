/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module
public import Sheaf.Paper.CechCupResolutionComparisonData
public import Mathlib.Topology.Sheaves.Flasque
import Sheaf.Paper.CupCechTotalComplex
import all Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.Topology.Sheaves.CechFlasque
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # Core comparison maps for a flasque computing resolution

Source: Stacks Project, Cohomology of Sheaves, Tags 01EQ and 0FKV.
(blueprint: lem-sc-cech-flasque-resolution-comparison-core)

The existing alpha and beta constructions give the specified chain maps. Sheaf gluing
and flasque Cech exactness give quasi-isomorphisms for their augmented rows; the
first-quadrant column criterion, after flipping the two degrees, applies to alpha.
-/

@[expose] public section
universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-zero part of the augmented Čech quasi-isomorphism.

Source: Stacks Project, Cohomology of Sheaves, Tag 01EP.
(blueprint: lem-sc-cech-flasque-resolution-comparison-core)

Proof: identify categorical products of opens with their finite intersections
and products of modules with families of sections. The differential from degree
zero to degree one sends a family to the difference of its restrictions on each
pairwise intersection. Its kernel therefore consists precisely of compatible
families. The sheaf gluing axiom gives a unique section on the union for every
such family. The union is X by hU, so restriction from J(X) to this kernel is
bijective and linear. There are no incoming boundaries in either degree-zero
complex. The source's zero homology is its sole term; the target's zero homology
is the kernel just described. The equality ht identifies the global-section
scalar restriction with the identity, and hb identifies the induced homology
map with restriction. Thus it is an isomorphism. This argument does not need
injectivity. If the cover is empty, hU forces X to be empty; the empty-cover
sheaf axiom gives J(X) = 0, and the target is the empty product, also zero. -/
private theorem cechAugmentation_quasiIsoAt_zero {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (J : X.Modules)
    (ht : (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom =
      RingHom.id Γ(X, ⊤))
    (b : (CochainComplex.single₀ (ModuleCat.{v} Γ(X, ⊤))).obj
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
    let G : TopCat.Sheaf (ModuleCat.{v} Γ(X, ⊤)) X.toTopCat := ⟨F.obj, F.property⟩
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
    let G : TopCat.Sheaf (ModuleCat.{v} Γ(X, ⊤)) X.toTopCat := ⟨F.obj, hF⟩
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


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical core maps from a flasque computing resolution to its Cech total complex.
Source: Stacks Project, Tags 01EQ and 0FKV.
(blueprint: lem-sc-cech-flasque-resolution-comparison-core)

Proof: define `alpha` degreewise by restriction of global sections into Cech degree
zero and the total-complex inclusion. Define `beta` from the augmentation into the
resolution degree zero row and the corresponding total-complex inclusion. Restriction
naturality and the augmentation chain-map equation prove that both families are chain
maps. The augmented Cech complex of each flasque term is exact in positive degrees,
while sheaf gluing identifies degree-zero homology with global sections. The
first-quadrant column comparison for the resulting double complex therefore proves
that `alpha` is a quasi-isomorphism. The construction also works for degree zero and
for an empty cover of the empty scheme. -/
theorem cechFlasqueComparisonCore {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤) {F : X.Modules}
    (D : CupAcyclicResolution F)
    (hD : ∀ n : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (D.K.X n))) :
    ∃ alpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K ⟶ (cupCechDouble U D.K).total (ComplexShape.up ℕ),
      ∃ beta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
        (cupCechDouble U D.K).total (ComplexShape.up ℕ),
      (∀ n : ℕ, alpha.f n = moduleCechZero U (D.K.X n) ≫
        (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp)) ∧
      (∀ n : ℕ, beta.f n =
        ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) ∧
      QuasiIso alpha := by
  refine ⟨cupCechAlpha U D, cupCechBeta U D, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
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
  let K := cupCechDouble U D.K
  let A := cupSections D
  let a : A ⟶ K.flip.X 0 :=
    { f := fun n ↦ moduleCechZero U (D.K.X n)
      comm' := fun n m _ ↦ by
        change moduleCechZero U (D.K.X n) ≫
            ((CategoryTheory.cechComplexFunctor U).map
              ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
                (D.K.d n m).val)).f 0 =
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).map
            (D.K.d n m) ≫ moduleCechZero U (D.K.X m)
        exact moduleCechZero_naturality U (D.K.d n m) }
  have ha : a ≫ K.flip.d 0 1 = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    change moduleCechZero U (D.K.X n) ≫
      ((CategoryTheory.cechComplexFunctor U).obj
        (D.K.X n).presheafModuleCat).d 0 1 = 0
    exact moduleCechZero_d U (D.K.X n)
  let b := cupCechAlpha U D ≫ (K.totalFlipIso (ComplexShape.up ℕ)).inv
  have hb : ∀ n : ℕ, b.f n = a.f n ≫
      K.flip.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) := by
    intro n
    dsimp only [b, HomologicalComplex.comp_f, cupCechAlpha,
      cupCechAlphaComponent, a]
    rw [Category.assoc, K.ιTotal_totalFlipIso_f_inv]
    change (1 : ℤˣ) • moduleCechZero U (D.K.X n) ≫
      K.flip.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) = _
    simp only [one_smul]
  have hcol : ∀ n : ℕ, QuasiIso
      ((CochainComplex.fromSingle₀Equiv (K.flip.flip.X n) (A.X n)).symm
        ⟨a.f n, by simpa using congrArg (fun f ↦ f.f n) ha⟩) := by
    intro n
    let c := (CochainComplex.fromSingle₀Equiv (K.flip.flip.X n) (A.X n)).symm
      ⟨a.f n, by simpa using congrArg (fun f ↦ f.f n) ha⟩
    rw [quasiIso_iff]
    intro p
    by_cases hp : p = 0
    · subst p
      apply cechAugmentation_quasiIsoAt_zero U hU (D.K.X n)
        (moduleCech_top_restriction X)
      dsimp [c, a, moduleCechZero, CochainComplex.fromSingle₀Equiv]
      rfl
    · apply (quasiIsoAt_iff_isIso_homologyMap _ _).2
      have hs := HomologicalComplex.isZero_single_obj_homology
        (ComplexShape.up ℕ) 0
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (D.K.X n)) p hp
      let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj (D.K.X n)
      have : TopCat.Presheaf.IsFlasque F.obj := hD n
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
      have he := TopCat.Sheaf.exactAt_cechComplex_of_isFlasque U q F
      have hz := he.isZero_homology
      have hz' : IsZero ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).obj
          (((CategoryTheory.cechComplexFunctor U).obj (D.K.X n).presheafModuleCat).homology
            (q + 1))) :=
        hz.of_iso (TopCat.Presheaf.cechComplexFunctorHomologyIso U
          (D.K.X n).presheafModuleCat (q + 1))
      have htgt : IsZero
          (((CategoryTheory.cechComplexFunctor U).obj (D.K.X n).presheafModuleCat).homology
            (q + 1)) := by
        apply ModuleCat.isZero_iff_subsingleton.mpr
        exact (AddCommGrpCat.isZero_iff_subsingleton.mp hz')
      exact hs.isIso htgt _
  have : QuasiIso b :=
    HomologicalComplex₂.quasiIso_of_column_augmentation K.flip A a ha b hb hcol
  exact quasiIso_of_comp_right (cupCechAlpha U D)
    (K.totalFlipIso (ComplexShape.up ℕ)).inv

end
end AlgebraicGeometry.Scheme.Modules
