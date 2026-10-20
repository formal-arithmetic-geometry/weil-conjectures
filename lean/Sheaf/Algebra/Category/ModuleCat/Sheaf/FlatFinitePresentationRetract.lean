/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Finite relations in a flat module sheaf

Source: Stacks Project, Modules on Sites, Tag 08FC, induction on the relation matrix.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

section Helpers

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

private abbrev baseRing (R : Sheaf J CommRingCat.{r}) : Sheaf J RingCat.{r} :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem overMap_colimits [UnivLE.{max uC vC, r}] {U V : C} (f : V ⟶ U) :
    PreservesColimitsOfSize.{r, r} (overMap.{r} (baseRing R) f) := by
  have h (W : C) : PreservesColimitsOfSize.{r, r} (toSheaf.{r} ((baseRing R).over W)) := by
    constructor
    intro K _
    exact preservesColimitsOfShape_toSheaf _ K
  have := h U
  have := h V
  have : PreservesColimitsOfSize.{r, r}
      ((Over.map f).sheafPushforwardContinuous AddCommGrpCat.{r} (J.over V) (J.over U)) :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{r}
      (J.over V) (J.over U)).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{r, r}
      (overMap.{r} (baseRing R) f ⋙ toSheaf.{r} ((baseRing R).over V)) :=
    inferInstanceAs (PreservesColimitsOfSize.{r, r}
      (toSheaf.{r} ((baseRing R).over U) ⋙
        (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{r} (J.over V) (J.over U)))
  have : ReflectsColimitsOfSize.{r, r} (toSheaf.{r} ((baseRing R).over V)) :=
    reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves _ (toSheaf.{r} ((baseRing R).over V))

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
@[no_expose, irreducible] private def sectionHom (N : SheafOfModules.{r} (baseRing R)) (U : C)
    (s : N.val.obj (op U)) : unit ((baseRing R).over U) ⟶ N.over U :=
  (N.over U).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun W ↦ N.val.map W.unop.hom.op s) (by
      intro W W' f
      change N.val.map f.unop.left.op (N.val.map W.unop.hom.op s) = _
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]))

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem sectionHom_app (N : SheafOfModules.{r} (baseRing R)) (U : C)
    (s : N.val.obj (op U)) (W : (Over U)ᵒᵖ) (x : R.obj.obj (op W.unop.left)) :
    (sectionHom R N U s).val.app W x = x • N.val.map W.unop.hom.op s := by
  unfold sectionHom
  rfl

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem sectionHom_one (N : SheafOfModules.{r} (baseRing R)) (U : C)
    (s : N.val.obj (op U)) :
    (sectionHom R N U s).val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) = s := by
  rw [sectionHom_app, one_smul]
  change N.val.map (𝟙 U).op s = s
  rw [op_id, N.val.map_id]
  rfl

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
@[no_expose, irreducible] private def scalarHom (U : C) (b : R.obj.obj (op U)) :
    unit ((baseRing R).over U) ⟶ unit ((baseRing R).over U) :=
  sectionHom R (unit (baseRing R)) U b

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarHom_one (U : C) (b : R.obj.obj (op U)) :
    (scalarHom R U b).val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) = b := by
  unfold scalarHom
  exact sectionHom_one R (unit (baseRing R)) U b

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem slice_unit_ext (U : C)
    (M : SheafOfModules.{r} ((baseRing R).over U))
    (a b : unit ((baseRing R).over U) ⟶ M)
    (h : a.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) =
      b.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) : a = b := by
  apply M.unitHomEquiv.injective
  apply Subtype.ext
  funext W
  let f : W.unop ⟶ Over.mk (𝟙 U) := Over.homMk W.unop.hom
  have ha := PresheafOfModules.naturality_apply a.val f.op (1 : R.obj.obj (op U))
  have hb := PresheafOfModules.naturality_apply b.val f.op (1 : R.obj.obj (op U))
  change a.val.app W (1 : R.obj.obj (op W.unop.left)) =
    b.val.app W (1 : R.obj.obj (op W.unop.left))
  have hone : (unit ((baseRing R).over U)).val.map f.op
      (1 : R.obj.obj (op U)) = (1 : R.obj.obj (op W.unop.left)) := by
    change R.obj.map W.unop.hom.op 1 = 1
    exact map_one _
  rw [hone] at ha hb
  exact ha.trans ((congrArg (fun x ↦ M.val.map f.op x) h).trans hb.symm)

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem finite_relations
    (N : SheafOfModules.{r} (baseRing R)) (hN : IsFlatOnSite (R := R) N) (m : ℕ) :
    ∀ (U : C) (n : ℕ) (a : Fin m → Fin n → R.obj.obj (op U))
      (s : Fin n → N.val.obj (op U)),
      (∀ j, ∑ i, a j i • s i = 0) →
      ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
        ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op V))
          (t : Fin l → N.val.obj (op V)),
          (∀ i, N.val.map f.op (s i) = ∑ k, b i k • t k) ∧
          (∀ j k, ∑ i, R.obj.map f.op (a j i) * b i k = 0) := by
  classical
  induction m with
  | zero =>
    intro U n a s h
    refine ⟨⊤, J.top_mem U, ?_⟩
    intro V f hf
    refine ⟨n, fun i k ↦ if i = k then 1 else 0,
      fun i ↦ N.val.map f.op (s i), ?_, ?_⟩
    · intro i
      simp
    · intro j
      exact Fin.elim0 j
  | succ m ih =>
    intro U n a s h
    obtain ⟨S, hS, hloc⟩ := local_equationalCriterion_of_isFlatOnSite
      R N hN U n (a 0) s (h 0)
    have next : ∀ (V : C) (f : V ⟶ U) (hf : S f),
        ∃ T : Sieve V, T ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), T g →
          ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op W))
            (t : Fin l → N.val.obj (op W)),
            (∀ i, N.val.map (g ≫ f).op (s i) = ∑ k, b i k • t k) ∧
            (∀ j k, ∑ i, R.obj.map (g ≫ f).op (a j i) * b i k = 0) := by
      intro V f hf
      obtain ⟨l, b, t, hs, hb⟩ := hloc V f hf
      let c : Fin m → Fin l → R.obj.obj (op V) :=
        fun j k ↦ ∑ i, R.obj.map f.op (a j.succ i) * b i k
      have hc : ∀ j, ∑ k, c j k • t k = 0 := by
        intro j
        calc
          _ = ∑ i, R.obj.map f.op (a j.succ i) • (∑ k, b i k • t k) := by
            simp only [c, Finset.sum_smul, mul_smul, Finset.smul_sum]
            rw [Finset.sum_comm]
          _ = ∑ i, R.obj.map f.op (a j.succ i) • N.val.map f.op (s i) := by
            simp_rw [hs]
          _ = 0 := by
            have hh := congrArg (N.val.map f.op) (h j.succ)
            simp only [map_sum, N.val.map_smul, map_zero] at hh
            exact hh
      obtain ⟨T, hT, hTloc⟩ := ih V l c t hc
      refine ⟨T, hT, ?_⟩
      intro W g hg
      obtain ⟨q, d, z, ht, hd⟩ := hTloc W g hg
      refine ⟨q, fun i k ↦ ∑ p, R.obj.map g.op (b i p) * d p k, z, ?_, ?_⟩
      · intro i
        rw [op_comp, PresheafOfModules.map_comp_apply, hs, map_sum]
        simp only [N.val.map_smul, ht, Finset.smul_sum, mul_smul,
          Finset.sum_smul]
        rw [Finset.sum_comm]
        rfl
      · intro j k
        have calc_eq (a' : Fin n → R.obj.obj (op V)) :
            (∑ i, R.obj.map g.op (a' i) *
              (∑ p, R.obj.map g.op (b i p) * d p k)) =
            ∑ p, R.obj.map g.op (∑ i, a' i * b i p) * d p k := by
          simp only [Finset.mul_sum, map_sum, map_mul, Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]
        simp only [op_comp, Functor.map_comp, CommRingCat.comp_apply]
        rw [calc_eq]
        refine Fin.cases ?_ (fun j ↦ hd j k) j
        simp only [hb, map_zero, zero_mul, Finset.sum_const_zero]
    choose T hT hTloc using next
    refine ⟨Sieve.bind S (fun V f hf ↦ T V f hf),
      J.bind_covering hS (fun V f hf ↦ hT V f hf), ?_⟩
    rintro W h ⟨V, g, f, hf, hg, rfl⟩
    exact hTloc V f hf W g hg

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem finite_relations_fintype
    (N : SheafOfModules.{r} (baseRing R)) (hN : IsFlatOnSite (R := R) N)
    (U : C) {ι κ : Type r} [Fintype ι] [Finite κ]
    (a : κ → ι → R.obj.obj (op U)) (s : ι → N.val.obj (op U))
    (h : ∀ j, ∑ i, a j i • s i = 0) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ (l : ℕ) (b : ι → Fin l → R.obj.obj (op V))
        (t : Fin l → N.val.obj (op V)),
        (∀ i, N.val.map f.op (s i) = ∑ k, b i k • t k) ∧
        (∀ j k, ∑ i, R.obj.map f.op (a j i) * b i k = 0) := by
  classical
  let e := Fintype.equivFin ι
  let : Fintype κ := Fintype.ofFinite κ
  let d := Fintype.equivFin κ
  obtain ⟨S, hS, hloc⟩ := finite_relations R N hN (Fintype.card κ) U (Fintype.card ι)
    (fun j i ↦ a (d.symm j) (e.symm i)) (fun i ↦ s (e.symm i)) (by
      intro j
      exact (e.symm.sum_comp (fun i ↦ a (d.symm j) i • s i)).trans (h (d.symm j)))
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, t, hs, hb⟩ := hloc V f hf
  refine ⟨l, fun i k ↦ b (e i) k, t, ?_, ?_⟩
  · intro i
    simpa using hs (e i)
  · intro j k
    simpa only [← Equiv.sum_comp e, Equiv.symm_apply_apply] using hb (d j) k

section FiniteFree


variable {D : Type*} [Category D] {K : GrothendieckTopology D}
  {T : Sheaf K RingCat.{r}} [HasSheafify K AddCommGrpCat.{r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}]

@[no_expose, irreducible] private def coord {ι : Type r} (i : ι) :
    free (R := T) ι ⟶ unit T := by
  classical
  exact Cofan.IsColimit.desc (isColimitFreeCofan ι)
    (fun j ↦ if j = i then 𝟙 _ else 0)

open Classical in
private theorem inj_coord {ι : Type r} (i j : ι) :
    ιFree j ≫ coord (T := T) i = if j = i then 𝟙 _ else 0 := by
  classical
  unfold coord
  exact Cofan.IsColimit.fac (isColimitFreeCofan (R := T) ι)
    (fun j ↦ if j = i then 𝟙 _ else 0) j

omit [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem sum_app {ι : Type*} [Fintype ι] {M P : SheafOfModules.{r} T}
    (f : ι → (M ⟶ P)) (X : Dᵒᵖ) (x : M.val.obj X) :
    (∑ i, f i).val.app X x = ∑ i, (f i).val.app X x := by
  classical
  have hs (s : Finset ι) :
      (∑ i ∈ s, f i).val.app X x = ∑ i ∈ s, (f i).val.app X x := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      change (f i).val.app X x + (∑ i ∈ s, f i).val.app X x = _
      rw [ih]
  exact hs Finset.univ

omit [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem unit_comp_app (M : SheafOfModules.{r} T)
    (a : unit T ⟶ unit T) (b : unit T ⟶ M) (X : Dᵒᵖ) :
    (a ≫ b).val.app X (1 : T.obj.obj X) =
      a.val.app X (1 : T.obj.obj X) • b.val.app X (1 : T.obj.obj X) := by
  change b.val.app X (a.val.app X (1 : T.obj.obj X)) = _
  simpa only [smul_eq_mul, mul_one] using
    (b.val.app X).hom.map_smul (a.val.app X (1 : T.obj.obj X)) (1 : T.obj.obj X)

end FiniteFree

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem restrict_unit_eval {U V : C} (f : V ⟶ U)
    (M : SheafOfModules.{r} ((baseRing R).over U))
    (g : unit ((baseRing R).over U) ⟶ M) :
    ((overMap.{r} (baseRing R) f).map g).val.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V)) =
      M.val.map (Over.homMk ((𝟙 V) ≫ f) :
        (Over.map f).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U)).op
        (g.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) := by
  have h := PresheafOfModules.naturality_apply g.val
    (Over.homMk ((𝟙 V) ≫ f) :
        (Over.map f).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U)).op (1 : R.obj.obj (op U))
  have hone : (unit ((baseRing R).over U)).val.map
      (Over.homMk ((𝟙 V) ≫ f) :
        (Over.map f).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U)).op
        (1 : R.obj.obj (op U)) = (1 : R.obj.obj (op V)) := by
    change R.obj.map ((𝟙 V) ≫ f).op 1 = 1
    exact map_one _
  rw [hone] at h
  exact h

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem restrict_scalar_comp_app {U V : C} (f : V ⟶ U)
    (M : SheafOfModules.{r} ((baseRing R).over V))
    (a : unit ((baseRing R).over U) ⟶ unit ((baseRing R).over U))
    (b : R.obj.obj (op V)) (g : unit ((baseRing R).over V) ⟶ M) :
    ((overMap.{r} (baseRing R) f).map a ≫
        (overMapUnitIso (R := baseRing R) f).hom ≫ scalarHom R V b ≫ g).val.app
      (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V)) =
      (R.obj.map f.op (a.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) * b) •
        g.val.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V)) := by
  have hf := restrict_unit_eval R f (unit ((baseRing R).over U)) a
  change _ = R.obj.map ((𝟙 V) ≫ f).op
    (a.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) at hf
  rw [Category.id_comp] at hf
  rw [← Category.assoc, ← Category.assoc]
  erw [unit_comp_app, unit_comp_app]
  rw [scalarHom_one]
  change ((show R.obj.obj (op V) from
    ((overMap.{r} (baseRing R) f).map a).val.app (op (Over.mk (𝟙 V)))
      (1 : R.obj.obj (op V))) * b) • _ = _
  rw [hf]

attribute [local irreducible] free

set_option maxHeartbeats 600000 in
-- Checking the mapped finite-free cofan and its section evaluations needs extra heartbeats.
open Classical in
private theorem local_cokernel_retract [UnivLE.{max uC vC, r}]
    (N : SheafOfModules.{r} (baseRing R)) (hN : IsFlatOnSite (R := R) N)
    (U : C) {ι κ : Type r} [Finite ι] [Finite κ]
    (P Q : SheafOfModules.{r} ((baseRing R).over U))
    (gen : ι → (unit ((baseRing R).over U) ⟶ P))
    (rel : κ → (unit ((baseRing R).over U) ⟶ Q))
    (coord : ι → (P ⟶ unit ((baseRing R).over U)))
    (hgen : IsColimit (Cofan.mk P gen)) (hrel : IsColimit (Cofan.mk Q rel))
    (hcoord : ∀ i j, gen j ≫ coord i = if j = i then 𝟙 _ else 0)
    (q : P ⟶ N.over U) (a : Q ⟶ P) (haq : a ≫ q = 0)
    (hpres : IsColimit (CokernelCofork.ofπ q haq)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ (l : ℕ) (i : N.over V ⟶ free (R := (baseRing R).over V) (ULift.{r} (Fin l)))
        (p : free (R := (baseRing R).over V) (ULift.{r} (Fin l)) ⟶ N.over V),
        i ≫ p = 𝟙 _ := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype κ := Fintype.ofFinite κ
  have htotal : ∑ i, coord i ≫ gen i = 𝟙 P := by
    apply Cofan.IsColimit.hom_ext hgen
    intro j
    change gen j ≫ _ = gen j ≫ _
    simp only [Preadditive.comp_sum, ← Category.assoc,
      hcoord, ite_comp, Category.id_comp, zero_comp, Category.comp_id]
    simp
  let X := op (Over.mk (𝟙 U))
  let s (i : ι) : N.val.obj (op U) := (gen i ≫ q).val.app X (1 : R.obj.obj (op U))
  let c (j : κ) (i : ι) : R.obj.obj (op U) :=
    (rel j ≫ a ≫ coord i).val.app X (1 : R.obj.obj (op U))
  have hc (j : κ) : ∑ i, c j i • s i = 0 := by
    have he := congrArg (fun h : P ⟶ P ↦
      (rel j ≫ a ≫ h ≫ q).val.app X (1 : R.obj.obj (op U))) htotal
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, sum_app,
      Category.id_comp] at he
    have hterm (i : ι) :
        (rel j ≫ a ≫ (coord i ≫ gen i) ≫ q).val.app X (1 : R.obj.obj (op U)) =
          c j i • s i := by
      change ((rel j ≫ a ≫ coord i) ≫ (gen i ≫ q)).val.app X
        (1 : R.obj.obj (op U)) = _
      exact unit_comp_app (N.over U) (rel j ≫ a ≫ coord i) (gen i ≫ q) X
    simp_rw [hterm] at he
    have hz : (rel j ≫ a ≫ q).val.app X (1 : R.obj.obj (op U)) = 0 := by
      rw [haq, comp_zero]
      rfl
    exact he.trans hz
  obtain ⟨S, hS, hloc⟩ := finite_relations_fintype R N hN U c s hc
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, t, hs, hb⟩ := hloc V f hf
  let F := overMap.{r} (baseRing R) f
  have : F.Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  have : PreservesColimitsOfSize.{r, r} F := overMap_colimits R f
  have : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  let Z := free (R := (baseRing R).over V) (ULift.{r} (Fin l))
  let p : Z ⟶ N.over V := Cofan.IsColimit.desc
    (isColimitFreeCofan (ULift.{r} (Fin l))) (fun k ↦ sectionHom R N V (t k.down))
  let d (i : ι) (k : Fin l) : unit ((baseRing R).over V) ⟶
      unit ((baseRing R).over V) := scalarHom R V (b i k)
  have hp (k : Fin l) : ιFree (ULift.up k) ≫ p = sectionHom R N V (t k) := by
    exact Cofan.IsColimit.fac (isColimitFreeCofan (R := (baseRing R).over V)
      (ULift.{r} (Fin l))) _ _
  clear_value p
  let B : F.obj P ⟶ Z :=
    Cofan.IsColimit.desc
      (isColimitCofanMkObjOfIsColimit F (fun _ : ι ↦ unit ((baseRing R).over U))
        gen hgen)
      (fun i ↦ (overMapUnitIso (R := baseRing R) f).hom ≫
        ∑ k : Fin l, d i k ≫ ιFree (ULift.up k))
  have hBi (i : ι) : F.map (gen i) ≫ B =
      ∑ k : Fin l, d i k ≫ ιFree (ULift.up k) := by
    exact Cofan.IsColimit.fac
      (isColimitCofanMkObjOfIsColimit F (fun _ : ι ↦ unit ((baseRing R).over U))
        gen hgen) _ i
  clear_value B
  have hB : B = ∑ i, ∑ k : Fin l, F.map (coord i) ≫
      (overMapUnitIso (R := baseRing R) f).hom ≫
      scalarHom R V (b i k) ≫ ιFree (ULift.up k) := by
    have h := congrArg (fun z ↦ F.map z ≫ B) htotal
    simp only [F.map_sum, F.map_comp, Preadditive.sum_comp, Category.assoc,
      hBi, Preadditive.comp_sum, F.map_id, Category.id_comp] at h
    exact h.symm
  have hAB : F.map a ≫ B = 0 := by
    apply Cofan.IsColimit.hom_ext
      (isColimitCofanMkObjOfIsColimit F (fun _ : κ ↦ unit ((baseRing R).over U))
        rel hrel)
    intro j
    change F.map (rel j) ≫ _ = F.map (rel j) ≫ _
    apply slice_unit_ext R V Z
    let Y := op (Over.mk (𝟙 V))
    have hterm (i : ι) (k : Fin l) :
        (F.map (rel j ≫ a ≫ coord i) ≫
          (overMapUnitIso (R := baseRing R) f).hom ≫
          scalarHom R V (b i k) ≫
          ιFree (R := (baseRing R).over V) (ULift.up k)).val.app Y (1 : R.obj.obj (op V)) =
        (R.obj.map f.op (c j i) * b i k) •
          (ιFree (R := (baseRing R).over V) (ULift.up k)).val.app Y (1 : R.obj.obj (op V)) := by
      exact restrict_scalar_comp_app R f Z (rel j ≫ a ≫ coord i) (b i k)
        (ιFree (ULift.up k))
    rw [hB]
    simp only [Preadditive.comp_sum, ← Category.assoc, ← F.map_comp]
    rw [sum_app]
    simp only [sum_app]
    change (∑ i, ∑ k : Fin l,
      (F.map (rel j ≫ a ≫ coord i) ≫
        (overMapUnitIso (R := baseRing R) f).hom ≫
        scalarHom R V (b i k) ≫
        ιFree (ULift.up k)).val.app Y (1 : R.obj.obj (op V))) = 0
    simp_rw [hterm]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hb, zero_smul]
    simp
  let e : F.obj (N.over U) ≅ N.over V := Iso.refl _
  have hBp : B ≫ p = F.map q ≫ e.hom := by
    apply Cofan.IsColimit.hom_ext
      (isColimitCofanMkObjOfIsColimit F (fun _ : ι ↦ unit ((baseRing R).over U))
        gen hgen)
    intro i
    change F.map (gen i) ≫ _ = F.map (gen i) ≫ _
    calc
      _ = (F.map (gen i) ≫ B) ≫ p := (Category.assoc _ _ _).symm
      _ = (∑ k : Fin l, d i k ≫ ιFree (ULift.up k)) ≫ p :=
        congrArg (fun h ↦ h ≫ p) (hBi i)
      _ = ∑ k : Fin l, d i k ≫ sectionHom R N V (t k) := by
        rw [Preadditive.sum_comp]
        simp only [Category.assoc, hp]
      _ = F.map (gen i) ≫ (F.map q ≫ e.hom) := by
        apply slice_unit_ext R V (N.over V)
        rw [sum_app]
        have hi := restrict_unit_eval R f (N.over U) (gen i ≫ q)
        change _ = N.val.map ((𝟙 V) ≫ f).op (s i) at hi
        rw [Category.id_comp] at hi
        rw [← Category.assoc, ← F.map_comp]
        change _ = (F.map (gen i ≫ q)).val.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V))
        rw [hi, hs]
        apply Finset.sum_congr rfl
        intro k _
        change (scalarHom R V (b i k) ≫ sectionHom R N V (t k)).val.app
          (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V)) = _
        rw [unit_comp_app, scalarHom_one, sectionHom_one]
  have H := CokernelCofork.mapIsColimit _ hpres F
  obtain ⟨i, hi⟩ := CokernelCofork.IsColimit.desc' H B hAB
  change F.map q ≫ i = B at hi
  refine ⟨l, e.inv ≫ i, p, ?_⟩
  have hepi : Epi (F.map q) := epi_of_isColimit_cofork H
  have hip : i ≫ p = e.hom := by
    apply (cancel_epi (F.map q)).mp
    rw [← Category.assoc, hi]
    exact hBp
  rw [Category.assoc, hip, e.inv_hom_id]

private theorem local_presentation_retract [UnivLE.{max uC vC, r}]
    (N : SheafOfModules.{r} (baseRing R)) (hN : IsFlatOnSite (R := R) N)
    (U : C) (P : (N.over U).Presentation) [P.IsFinite] :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ (l : ℕ) (i : N.over V ⟶ free (R := (baseRing R).over V) (ULift.{r} (Fin l)))
        (p : free (R := (baseRing R).over V) (ULift.{r} (Fin l)) ⟶ N.over V),
        i ≫ p = 𝟙 _ := by
  classical
  let : Fintype P.generators.I := Fintype.ofFinite _
  let : Fintype P.relations.I := Fintype.ofFinite _
  exact local_cokernel_retract R N hN U _ _ ιFree ιFree coord
    (isColimitFreeCofan _) (isColimitFreeCofan _) inj_coord P.generators.π
    ((freeHomEquiv _).symm P.relations.s ≫ kernel.ι _) (by simp) P.isColimit

private theorem local_finiteFree_retract_data [UnivLE.{max uC vC, r}]
    (N : SheafOfModules.{r} (baseRing R)) (hN : IsFlatOnSite (R := R) N)
    (σ : N.QuasicoherentData) [σ.IsFinitePresentation] :
    ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ (n : ℕ) (i : N.over V ⟶ ∏ᶜ fun _ : Fin n ↦ unit ((baseRing R).over V))
        (p : (∏ᶜ fun _ : Fin n ↦ unit ((baseRing R).over V)) ⟶ N.over V),
        i ≫ p = 𝟙 _ := by
  classical
  choose S hS hret using fun α ↦ local_presentation_retract R N hN
    (σ.X α) (σ.presentation α)
  intro U
  have next : ∀ (W : C) (f : W ⟶ U) (hf : Sieve.ofObjects σ.X U f),
      ∃ T : Sieve W, T ∈ J W ∧ ∀ (V : C) (g : V ⟶ W), T g →
        ∃ (n : ℕ) (i : N.over V ⟶ ∏ᶜ fun _ : Fin n ↦ unit ((baseRing R).over V))
          (p : (∏ᶜ fun _ : Fin n ↦ unit ((baseRing R).over V)) ⟶ N.over V),
          i ≫ p = 𝟙 _ := by
    rintro W f ⟨α, ⟨a⟩⟩
    refine ⟨(S α).pullback a, J.pullback_stable a (hS α), ?_⟩
    intro V g hg
    obtain ⟨n, i, p, hip⟩ := hret α V (g ≫ a) hg
    have : HasFiniteBiproducts (SheafOfModules.{r} ((baseRing R).over V)) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    let e₁ : free (R := (baseRing R).over V) (ULift.{r} (Fin n)) ≅
        ∐ fun _ : Fin n ↦ unit ((baseRing R).over V) :=
      by
        unfold free
        exact Sigma.whiskerEquiv
          (f := fun _ : ULift.{r} (Fin n) ↦ unit ((baseRing R).over V))
          (g := fun _ : Fin n ↦ unit ((baseRing R).over V))
          Equiv.ulift (fun _ ↦ Iso.refl _)
    let e₂ := (biproduct.isoCoproduct (fun _ : Fin n ↦ unit ((baseRing R).over V))).symm ≪≫
      biproduct.isoProduct _
    let e := e₁ ≪≫ e₂
    refine ⟨n, i ≫ e.hom, e.inv ≫ p, ?_⟩
    simp [Category.assoc, hip]
  choose T hT hlocal using next
  refine ⟨Sieve.bind (Sieve.ofObjects σ.X U) (fun W f hf ↦ T W f hf),
    J.bind_covering (σ.coversTop U) (fun W f hf ↦ hT W f hf), ?_⟩
  rintro V f ⟨W, g, a, ha, hg, rfl⟩
  exact hlocal W a ha V g hg

end Helpers

/-- A flat module sheaf with local finite presentations is locally a retract of a
finite free module sheaf. Finite products of the structure module represent finite
free modules, since finite products and finite coproducts agree in this abelian category.
Source: Stacks Project, Modules on Sites, Tag 08FD
(blueprint: lem-sf-site-flat-fp-finite-retract).

Proof:
1. Fix U and choose its covering by finite presentations A : O^r → O^s and q : O^s → N.
   On the localized site, maps from finite free modules are specified by sections;
   thus A is a finite matrix and qA = 0 is its finite family of relations.
2. Induct on the number m of columns of any finite matrix A killed by g : O^n → N.
   The claim is that locally g = pB with B landing in a finite free module and BA = 0.
   For m = 0 take B = id and p = g, on the identity covering.
3. For m > 0 use lem-weil-pbc-flat-local-relations-universes on the first column.
   Its coefficients b_pq and sections t_q give B and p with pB = g, killing that column.
4. Apply the induction hypothesis to the other m - 1 columns of BA and p. Compose
   the matrices and the coverings; the resulting matrix kills every column of A.
   Relocalization identifies iterated restriction with direct restriction.
5. Apply the claim to the finite presentation. The cocontinuous sheaf adjunction and
   the module-sheaf forgetful colimit instance show that overMap preserves colimits.
   Thus the restricted q is still a cokernel of the restricted A.
6. Since BA = 0, descend B uniquely along q to i : N → O^l. Then (pi)q = pB = q.
   Cancel the cokernel epimorphism q to get pi = id.
7. Compose the coverings to obtain the conclusion over the original U. Zero ranks
   and empty covering families are included throughout. -/
theorem exists_local_finiteFree_retract_of_flat_of_finitePresentation
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J CommRingCat.{max uC vC r})
    (N : ringedSiteModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R))
    (hflat : IsFlatOnSite (J := J) (R := R) N)
    (hfp : N.IsFinitePresentation) :
    ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ (n : ℕ)
          (i : N.over V ⟶ (∏ᶜ fun _ : Fin n ↦ unit
            (((sheafCompose J
              (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over V)))
          (p : (∏ᶜ fun _ : Fin n ↦ unit
            (((sheafCompose J
              (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over V)) ⟶
            N.over V), i ≫ p = 𝟙 (N.over V) := by
  obtain ⟨σ, hσ⟩ := hfp.exists_quasicoherentData
  let : σ.IsFinitePresentation := hσ
  exact local_finiteFree_retract_data R N hflat σ

end SheafOfModules
