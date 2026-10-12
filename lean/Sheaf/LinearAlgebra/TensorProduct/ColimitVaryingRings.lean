/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Tensor products and directed colimits with varying coefficient rings

Source: Stacks Project, Sheaves, Tag 007K, algebraic content; Algebra, Tag 00DD,
second direct proof (blueprint: lem-weil-pbc-filtered-colimit-tensor-varying-rings).
-/

@[expose] public section

universe z u v w v' w'

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TensorProduct

private theorem colimit_ι_map_apply
    {I : Type z} [Preorder I] {i j : I}
    (D : I ⥤ AddCommGrpCat.{v}) [HasColimit D] (h : i ≤ j) (x : D.obj i) :
    colimit.ι D j (D.map (homOfLE h) x) = colimit.ι D i x :=
  ConcreteCategory.congr_hom (colimit.w D (homOfLE h)) x

private theorem group_colimit_rep
    {I : Type z} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : I ⥤ AddCommGrpCat.{v}) [HasColimit D] (x : ↥(colimit D)) :
    ∃ i y, colimit.ι D i y = x := by
  -- Lift the group universe so that the forgetful functor preserves this colimit.
  let U := AddCommGrpCat.uliftFunctor.{z, v}
  let : IsFiltered I := inferInstance
  let : PreservesFilteredColimitsOfSize.{z, z}
      (forget AddCommGrpCat.{max z v}) :=
    preservesFilteredColimitsOfSize_shrink _
  let : PreservesColimit (D ⋙ U) (forget AddCommGrpCat) := inferInstance
  let c := U.mapCocone (colimit.cocone D)
  have hc : IsColimit c := isColimitOfPreserves U (colimit.isColimit D)
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep (D ⋙ U) hc (ULift.up x)
  refine ⟨i, y.down, ?_⟩
  exact congrArg ULift.down hy

private theorem group_colimit_rep_after
    {I : Type z} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : I ⥤ AddCommGrpCat.{v}) [HasColimit D] (i : I) (x : ↥(colimit D)) :
    ∃ (j : I) (_h : i ≤ j) (y : D.obj j), colimit.ι D j y = x := by
  obtain ⟨k, y, hy⟩ := group_colimit_rep D x
  obtain ⟨j, hij, hkj⟩ := exists_ge_ge i k
  exact ⟨j, hij, D.map (homOfLE hkj) y, (colimit_ι_map_apply D hkj y).trans hy⟩

private theorem group_colimit_rep_eq
    {I : Type z} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : I ⥤ AddCommGrpCat.{v}) [HasColimit D] {i j : I}
    (x : D.obj i) (y : D.obj j) (h : colimit.ι D i x = colimit.ι D j y) :
    ∃ (k : I) (hi : i ≤ k) (hj : j ≤ k),
      D.map (homOfLE hi) x = D.map (homOfLE hj) y := by
  -- Lift the group universe so that the forgetful functor preserves this colimit.
  let U := AddCommGrpCat.uliftFunctor.{z, v}
  let : IsFiltered I := inferInstance
  let : PreservesFilteredColimitsOfSize.{z, z}
      (forget AddCommGrpCat.{max z v}) :=
    preservesFilteredColimitsOfSize_shrink _
  let : PreservesColimit (D ⋙ U) (forget AddCommGrpCat) := inferInstance
  let c := U.mapCocone (colimit.cocone D)
  have hc : IsColimit c := isColimitOfPreserves U (colimit.isColimit D)
  have he : c.ι.app i (ULift.up x) = c.ι.app j (ULift.up y) := congrArg ULift.up h
  obtain ⟨k, f, g, he⟩ :=
    Concrete.isColimit_exists_of_rep_eq (D ⋙ U) hc (ULift.up x) (ULift.up y) he
  refine ⟨k, leOfHom f, leOfHom g, ?_⟩
  exact congrArg ULift.down he

private theorem colimit_addHom_ext
    {J : Type*} [Category J] (D : J ⥤ AddCommGrpCat.{v}) [HasColimit D]
    {P : Type*} [AddCommMonoid P] (p q : ↥(colimit D) →+ P)
    (h : ∀ i x, p (colimit.ι D i x) = q (colimit.ι D i x)) : p = q := by
  classical
  let d := AddCommGrpCat.Colimits.Quot.desc D (colimit.cocone D)
  have hd : Function.Surjective d :=
    ((AddCommGrpCat.isColimit_iff_bijective_desc (colimit.cocone D)).mp
      ⟨colimit.isColimit D⟩).2
  have he : p.comp d = q.comp d :=
    AddCommGrpCat.Colimits.Quot.addMonoidHom_ext D (by
      intro i x
      change p (d (AddCommGrpCat.Colimits.Quot.ι D i x)) =
        q (d (AddCommGrpCat.Colimits.Quot.ι D i x))
      dsimp only [d]
      rw [AddCommGrpCat.Colimits.Quot.ι_desc, colimit.cocone_ι]
      exact h i x)
  exact AddMonoidHom.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := hd x
    exact DFunLike.congr_fun he y

private theorem colimit_tensor_addHom_ext
    {I : Type z} [Preorder I] (A : I ⥤ CommRingCat.{u})
    (M : I ⥤ AddCommGrpCat.{v}) (N : I ⥤ AddCommGrpCat.{w})
    (T : I ⥤ AddCommGrpCat.{max v w}) [HasColimit T]
    [∀ i : I, Module (A.obj i) (M.obj i)]
    [∀ i : I, Module (A.obj i) (N.obj i)]
    (e : ∀ i : I, (M.obj i ⊗[A.obj i] N.obj i) ≃+ T.obj i)
    {P : Type*} [AddCommMonoid P] (p q : ↥(colimit T) →+ P)
    (h : ∀ i m n, p (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))) =
      q (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n)))) : p = q := by
  apply colimit_addHom_ext T p q
  intro i x
  obtain ⟨t, rfl⟩ := (e i).surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => exact h i m n
  | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs

/-- Tensoring two semilinear directed systems commutes with their colimits, including
uniqueness and naturality of the comparison. Source: Stacks Project, Tags 007K and 00DD
(blueprint: lem-weil-pbc-filtered-colimit-tensor-varying-rings).

The additive equivalences `e` identify the objects of the tensor diagram with the actual
stage tensor products; `hT` specifies its transition maps. The three action equations
specify the induced actions on the colimits. The last clause states naturality for any
second pair of systems over the same ring diagram, with the induced colimit maps specified
by their equations on coprojections. Thus no choice of a presentation of a tensor diagram
or of its colimit affects the assertion.

Proof:
1. To define each colimit action, move the scalar and module representatives to a
   common stage and multiply there. Semilinearity and passage to a further common stage
   make this independent of representatives; the module laws hold at a common stage.
   This applies also to the tensor system. The balanced maps on pure tensors are
   additive and compatible with transitions by
   semilinearity. The colimit universal property (`def-weil-pbc-category-colimit`)
   gives the unique additive comparison; the prescribed actions make it linear.
2. For surjectivity, represent both factors at stages and move them to a common later
   stage. Each pure tensor is then the image of a tensor from that stage. Pure tensors
   generate, so the comparison is surjective.
3. For injectivity, move a finite sum representing an element to a common stage. If its
   image vanishes, only finitely many additivity and balancing relations are needed.
   Move all their coefficients and factors to a further common stage. There the relation
   vanishes already, so its class in the colimit is zero. This extends the direct
   tensor-colimit construction of Tag 00DD to varying rings using common stages.
4. Equivalently, the inverse sends tensors represented at a common stage to their stage
   tensor class; the preceding argument proves independence and balancing. Both inverse
   identities and the naturality square hold on the generating stage pure tensors. -/
theorem exists_unique_colimit_tensor_varying_rings
    {I : Type z} [Preorder I] [IsDirected I (· ≤ ·)]
    (A : I ⥤ CommRingCat.{u}) (M : I ⥤ AddCommGrpCat.{v})
    (N : I ⥤ AddCommGrpCat.{w}) (T : I ⥤ AddCommGrpCat.{max v w})
    [HasColimit A] [HasColimit M] [HasColimit N] [HasColimit T]
    [∀ i : I, Module (A.obj i) (M.obj i)]
    [∀ i : I, Module (A.obj i) (N.obj i)]
    [Module ↥(colimit A) (↥(colimit M))] [Module ↥(colimit A) (↥(colimit N))]
    [Module ↥(colimit A) (↥(colimit T))]
    (hM : ∀ {i j : I} (f : i ⟶ j) (a : A.obj i) (m : M.obj i),
      M.map f (a • m) = A.map f a • M.map f m)
    (hN : ∀ {i j : I} (f : i ⟶ j) (a : A.obj i) (n : N.obj i),
      N.map f (a • n) = A.map f a • N.map f n)
    (e : ∀ i : I, (M.obj i ⊗[A.obj i] N.obj i) ≃+ T.obj i)
    (hT : ∀ {i j : I} (f : i ⟶ j) (m : M.obj i) (n : N.obj i),
      T.map f (e i (m ⊗ₜ[A.obj i] n)) =
        e j (M.map f m ⊗ₜ[A.obj j] N.map f n))
    (hAM : ∀ (i : I) (a : A.obj i) (m : M.obj i),
      colimit.ι A i a • colimit.ι M i m = colimit.ι M i (a • m))
    (hAN : ∀ (i : I) (a : A.obj i) (n : N.obj i),
      colimit.ι A i a • colimit.ι N i n = colimit.ι N i (a • n))
    (hAT : ∀ (i : I) (a : A.obj i) (t : M.obj i ⊗[A.obj i] N.obj i),
      colimit.ι A i a • colimit.ι T i (e i t) = colimit.ι T i (e i (a • t))) :
    ∃ ψ : ↥(colimit T) →ₗ[↥(colimit A)] (↥(colimit M) ⊗[↥(colimit A)] ↥(colimit N)),
      (∀ (i : I) (m : M.obj i) (n : N.obj i),
        ψ (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))) =
          colimit.ι M i m ⊗ₜ[↥(colimit A)] colimit.ι N i n) ∧
      (∀ χ : ↥(colimit T) →+ (↥(colimit M) ⊗[↥(colimit A)] ↥(colimit N)),
        (∀ (i : I) (m : M.obj i) (n : N.obj i),
          χ (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))) =
            colimit.ι M i m ⊗ₜ[↥(colimit A)] colimit.ι N i n) →
        χ = ψ.toAddMonoidHom) ∧
      Function.Bijective ψ ∧
      (∀ (M' : I ⥤ AddCommGrpCat.{v'}) (N' : I ⥤ AddCommGrpCat.{w'})
        (T' : I ⥤ AddCommGrpCat.{max v' w'})
        [HasColimit M'] [HasColimit N'] [HasColimit T']
        [∀ i : I, Module (A.obj i) (M'.obj i)]
        [∀ i : I, Module (A.obj i) (N'.obj i)]
        [Module ↥(colimit A) (↥(colimit M'))] [Module ↥(colimit A) (↥(colimit N'))]
        [Module ↥(colimit A) (↥(colimit T'))]
        (e' : ∀ i : I, (M'.obj i ⊗[A.obj i] N'.obj i) ≃+ T'.obj i)
        (f : ∀ i : I, M.obj i →ₗ[A.obj i] M'.obj i)
        (g : ∀ i : I, N.obj i →ₗ[A.obj i] N'.obj i)
        (F : ↥(colimit M) →ₗ[↥(colimit A)] ↥(colimit M'))
        (G : ↥(colimit N) →ₗ[↥(colimit A)] ↥(colimit N'))
        (H : ↥(colimit T) →ₗ[↥(colimit A)] ↥(colimit T'))
        (ψ' : ↥(colimit T') →ₗ[↥(colimit A)] (↥(colimit M') ⊗[↥(colimit A)] ↥(colimit N'))),
        (∀ {i j : I} (a : i ⟶ j) (r : A.obj i) (m : M'.obj i),
          M'.map a (r • m) = A.map a r • M'.map a m) →
        (∀ {i j : I} (a : i ⟶ j) (r : A.obj i) (n : N'.obj i),
          N'.map a (r • n) = A.map a r • N'.map a n) →
        (∀ {i j : I} (a : i ⟶ j) (m : M'.obj i) (n : N'.obj i),
          T'.map a (e' i (m ⊗ₜ[A.obj i] n)) =
            e' j (M'.map a m ⊗ₜ[A.obj j] N'.map a n)) →
        (∀ (i : I) (r : A.obj i) (m : M'.obj i),
          colimit.ι A i r • colimit.ι M' i m = colimit.ι M' i (r • m)) →
        (∀ (i : I) (r : A.obj i) (n : N'.obj i),
          colimit.ι A i r • colimit.ι N' i n = colimit.ι N' i (r • n)) →
        (∀ (i : I) (r : A.obj i) (t : M'.obj i ⊗[A.obj i] N'.obj i),
          colimit.ι A i r • colimit.ι T' i (e' i t) =
            colimit.ι T' i (e' i (r • t))) →
        (∀ {i j : I} (a : i ⟶ j) (m : M.obj i),
          f j (M.map a m) = M'.map a (f i m)) →
        (∀ {i j : I} (a : i ⟶ j) (n : N.obj i),
          g j (N.map a n) = N'.map a (g i n)) →
        (∀ (i : I) (m : M.obj i), F (colimit.ι M i m) = colimit.ι M' i (f i m)) →
        (∀ (i : I) (n : N.obj i), G (colimit.ι N i n) = colimit.ι N' i (g i n)) →
        (∀ (i : I) (m : M.obj i) (n : N.obj i),
          H (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))) =
            colimit.ι T' i (e' i (f i m ⊗ₜ[A.obj i] g i n))) →
        (∀ (i : I) (m : M'.obj i) (n : N'.obj i),
          ψ' (colimit.ι T' i (e' i (m ⊗ₜ[A.obj i] n))) =
            colimit.ι M' i m ⊗ₜ[↥(colimit A)] colimit.ι N' i n) →
        ψ'.comp H = (TensorProduct.map F G).comp ψ) := by
  classical
  -- Compatibility of T and the prescribed colimit actions supply all transport identities.
  have _semilinearM := @hM
  have _semilinearN := @hN
  let R := ↥(colimit A)
  let P := ↥(colimit M) ⊗[R] ↥(colimit N)
  let b (i : I) : M.obj i →+ N.obj i →+ P :=
    { toFun := fun m ↦
        { toFun := fun n ↦ colimit.ι M i m ⊗ₜ[R] colimit.ι N i n
          map_zero' := by simp
          map_add' := by intro n n'; simp [tmul_add] }
      map_zero' := by ext n; simp
      map_add' := by intro m m'; ext n; simp [add_tmul] }
  have hb (i : I) (a : A.obj i) (m : M.obj i) (n : N.obj i) :
      b i (a • m) n = b i m (a • n) := by
    change colimit.ι M i (a • m) ⊗ₜ[R] colimit.ι N i n =
      colimit.ι M i m ⊗ₜ[R] colimit.ι N i (a • n)
    rw [← hAM, ← hAN, smul_tmul, tmul_smul]
  let s (i : I) : T.obj i →+ P :=
    (TensorProduct.liftAddHom (b i) (hb i)).comp (e i).symm.toAddMonoidHom
  have hs (i : I) (m : M.obj i) (n : N.obj i) :
      s i (e i (m ⊗ₜ[A.obj i] n)) =
        colimit.ι M i m ⊗ₜ[R] colimit.ι N i n := by
    simp [s, b]
  let c : Cocone T :=
    { pt := AddCommGrpCat.of P
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom (s i)
          naturality := by
            intro i j f
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro x
            obtain ⟨t, rfl⟩ := (e i).surjective x
            induction t using TensorProduct.induction_on with
            | zero =>
              change s j (T.map f (e i 0)) = s i (e i 0)
              simp only [map_zero]
            | tmul m n =>
              change s j (T.map f (e i (m ⊗ₜ[A.obj i] n))) = s i (e i (m ⊗ₜ n))
              rw [hT, hs, hs]
              have hmi := ConcreteCategory.congr_hom (colimit.w M f) m
              have hni := ConcreteCategory.congr_hom (colimit.w N f) n
              change colimit.ι M j (M.map f m) = colimit.ι M i m at hmi
              change colimit.ι N j (N.map f n) = colimit.ι N i n at hni
              rw [hmi, hni]
            | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs } }
  let p : ↥(colimit T) →+ P := (colimit.desc T c).hom
  have hp (i : I) (m : M.obj i) (n : N.obj i) :
      p (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))) =
        colimit.ι M i m ⊗ₜ[R] colimit.ι N i n := by
    change (colimit.ι T i ≫ colimit.desc T c) (e i (m ⊗ₜ[A.obj i] n)) = _
    rw [colimit.ι_desc]
    exact hs i m n
  have hpairing : ∃ β : ↥(colimit M) →ₗ[R] ↥(colimit N) →ₗ[R] ↥(colimit T),
      ∀ (i : I) (m : M.obj i) (n : N.obj i),
        β (colimit.ι M i m) (colimit.ι N i n) =
          colimit.ι T i (e i (m ⊗ₜ[A.obj i] n)) := by
    classical
    by_cases hI : Nonempty I
    · let : Nonempty I := hI
      have move {i j : I} (h : i ≤ j) (m : M.obj i) (n : N.obj i) :
          colimit.ι T j (e j (M.map (homOfLE h) m ⊗ₜ[A.obj j]
            N.map (homOfLE h) n)) = colimit.ι T i (e i (m ⊗ₜ[A.obj i] n)) := by
        rw [← hT]
        exact colimit_ι_map_apply T h _
      have uniq {i j : I} (mi : M.obj i) (ni : N.obj i)
          (mj : M.obj j) (nj : N.obj j)
          (hm : colimit.ι M i mi = colimit.ι M j mj)
          (hn : colimit.ι N i ni = colimit.ι N j nj) :
          colimit.ι T i (e i (mi ⊗ₜ[A.obj i] ni)) =
            colimit.ι T j (e j (mj ⊗ₜ[A.obj j] nj)) := by
        obtain ⟨k, hik, hjk, hm⟩ := group_colimit_rep_eq M mi mj hm
        obtain ⟨l, hil, hjl, hn⟩ := group_colimit_rep_eq N ni nj hn
        obtain ⟨r, hkr, hlr⟩ := exists_ge_ge k l
        have hm' : M.map (homOfLE (hik.trans hkr)) mi =
            M.map (homOfLE (hjk.trans hkr)) mj := by
          convert congrArg (M.map (homOfLE hkr)) hm using 1 <;>
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> congr 1
        have hn' : N.map (homOfLE (hil.trans hlr)) ni =
            N.map (homOfLE (hjl.trans hlr)) nj := by
          convert congrArg (N.map (homOfLE hlr)) hn using 1 <;>
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> congr 1
        rw [← move (hik.trans hkr), ← move (hjk.trans hkr), hm']
        have hn'' : N.map (homOfLE (hik.trans hkr)) ni =
            N.map (homOfLE (hjk.trans hkr)) nj := by
          convert hn' using 1
        rw [hn'']
      have rep (m : ↥(colimit M)) (n : ↥(colimit N)) :
          ∃ (i : I) (mi : M.obj i) (ni : N.obj i),
            colimit.ι M i mi = m ∧ colimit.ι N i ni = n := by
        obtain ⟨i, mi, rfl⟩ := group_colimit_rep M m
        obtain ⟨j, nj, rfl⟩ := group_colimit_rep N n
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        exact ⟨k, M.map (homOfLE hik) mi, N.map (homOfLE hjk) nj,
          colimit_ι_map_apply M hik mi, colimit_ι_map_apply N hjk nj⟩
      have ex (m : ↥(colimit M)) (n : ↥(colimit N)) :
          ∃ t : ↥(colimit T), ∃ (i : I) (mi : M.obj i) (ni : N.obj i),
            colimit.ι M i mi = m ∧ colimit.ι N i ni = n ∧
            colimit.ι T i (e i (mi ⊗ₜ[A.obj i] ni)) = t := by
        obtain ⟨i, mi, ni, hm, hn⟩ := rep m n
        exact ⟨_, i, mi, ni, hm, hn, rfl⟩
      let b (m : ↥(colimit M)) (n : ↥(colimit N)) := (ex m n).choose
      have hb (i : I) (mi : M.obj i) (ni : N.obj i) :
          b (colimit.ι M i mi) (colimit.ι N i ni) =
            colimit.ι T i (e i (mi ⊗ₜ[A.obj i] ni)) := by
        obtain ⟨j, mj, nj, hm, hn, ht⟩ := (ex (colimit.ι M i mi)
          (colimit.ι N i ni)).choose_spec
        exact ht.symm.trans (uniq mj nj mi ni hm hn)
      have repAfter (i : I) (m : ↥(colimit M)) (n : ↥(colimit N)) :
          ∃ (j : I) (hij : i ≤ j) (mj : M.obj j) (nj : N.obj j),
            colimit.ι M j mj = m ∧ colimit.ι N j nj = n := by
        obtain ⟨j, hij, mj, hm⟩ := group_colimit_rep_after M i m
        obtain ⟨k, hjk, nk, hn⟩ := group_colimit_rep_after N j n
        exact ⟨k, hij.trans hjk, M.map (homOfLE hjk) mj, nk,
          (colimit_ι_map_apply M hjk mj).trans hm, hn⟩
      have baddM (m₁ m₂ : ↥(colimit M)) (n : ↥(colimit N)) :
          b (m₁ + m₂) n = b m₁ n + b m₂ n := by
        obtain ⟨i, mi, rfl⟩ := group_colimit_rep M m₁
        obtain ⟨j, hij, mj, nj, hm, hn⟩ := repAfter i m₂ n
        have hmi := colimit_ι_map_apply M hij mi
        rw [← hmi, ← hm, ← hn, ← (colimit.ι M j).hom.map_add, hb, hb, hb]
        simp only [add_tmul, map_add]
      have baddN (m : ↥(colimit M)) (n₁ n₂ : ↥(colimit N)) :
          b m (n₁ + n₂) = b m n₁ + b m n₂ := by
        obtain ⟨i, ni, rfl⟩ := group_colimit_rep N n₁
        obtain ⟨j, hij, mj, nj, hm, hn⟩ := repAfter i m n₂
        have hni := colimit_ι_map_apply N hij ni
        rw [← hni, ← hm, ← hn, ← (colimit.ι N j).hom.map_add, hb, hb, hb]
        simp only [tmul_add, map_add]
      have bzeroM (n : ↥(colimit N)) : b 0 n = 0 := by
        obtain ⟨i, ni, rfl⟩ := group_colimit_rep N n
        rw [← (colimit.ι M i).hom.map_zero, hb]
        simp only [zero_tmul, map_zero]
      have bzeroN (m : ↥(colimit M)) : b m 0 = 0 := by
        obtain ⟨i, mi, rfl⟩ := group_colimit_rep M m
        rw [← (colimit.ι N i).hom.map_zero, hb]
        simp only [tmul_zero, map_zero]
      have bsmulMstage (i : I) (a : A.obj i) (m : ↥(colimit M))
          (n : ↥(colimit N)) :
          b (colimit.ι A i a • m) n = colimit.ι A i a • b m n := by
        obtain ⟨j, hij, mj, nj, hm, hn⟩ := repAfter i m n
        have ha := ConcreteCategory.congr_hom (colimit.w A (homOfLE hij)) a
        change colimit.ι A j (A.map (homOfLE hij) a) = colimit.ι A i a at ha
        rw [← hm, ← hn, ← ha, hAM, hb, hb, hAT]
        rw [smul_tmul, ← tmul_smul]
      have bsmulNstage (i : I) (a : A.obj i) (m : ↥(colimit M))
          (n : ↥(colimit N)) :
          b m (colimit.ι A i a • n) = colimit.ι A i a • b m n := by
        obtain ⟨j, hij, mj, nj, hm, hn⟩ := repAfter i m n
        have ha := ConcreteCategory.congr_hom (colimit.w A (homOfLE hij)) a
        change colimit.ι A j (A.map (homOfLE hij) a) = colimit.ι A i a at ha
        rw [← hm, ← hn, ← ha, hAN, hb, hb, hAT]
        rw [tmul_smul]
      let bb : ↥(colimit M) →+ ↥(colimit N) →+ ↥(colimit T) :=
        { toFun := fun m ↦
            { toFun := b m
              map_zero' := bzeroN m
              map_add' := baddN m }
          map_zero' := by ext n; exact bzeroM n
          map_add' := by intro m m'; ext n; exact baddM m m' n }
      -- Stage coefficients generate the ring colimit; bilinearity is a subring condition.
      let S : Subring ↥(colimit A) :=
        { carrier := {a | ∀ m n, bb (a • m) n = a • bb m n ∧
            bb m (a • n) = a • bb m n}
          zero_mem' := by intro m n; simp
          one_mem' := by intro m n; simp
          add_mem' := by
            intro a a' ha ha' m n
            constructor
            · simp only [add_smul, map_add, AddMonoidHom.add_apply,
                (ha m n).1, (ha' m n).1]
            · simp only [add_smul, map_add, (ha m n).2, (ha' m n).2]
          neg_mem' := by
            intro a ha m n
            constructor
            · simp only [neg_smul, map_neg, AddMonoidHom.neg_apply, (ha m n).1]
            · simp only [neg_smul, map_neg, (ha m n).2]
          mul_mem' := by
            intro a a' ha ha' m n
            constructor
            · rw [mul_smul, (ha (a' • m) n).1, (ha' m n).1, mul_smul]
            · rw [mul_smul, (ha m (a' • n)).2, (ha' m n).2, mul_smul] }
      have hS (i : I) (a : A.obj i) : colimit.ι A i a ∈ S := by
        intro m n
        exact ⟨bsmulMstage i a m n, bsmulNstage i a m n⟩
      let c : Cocone A :=
        { pt := CommRingCat.of S
          ι :=
            { app := fun i ↦ CommRingCat.ofHom
                { toFun := fun a ↦ ⟨colimit.ι A i a, hS i a⟩
                  map_zero' := by apply Subtype.ext; exact map_zero _
                  map_one' := by apply Subtype.ext; exact map_one _
                  map_add' := by intro a a'; apply Subtype.ext; exact map_add _ _ _
                  map_mul' := by intro a a'; apply Subtype.ext; exact map_mul _ _ _ }
              naturality := by
                intro i j f
                ext a
                apply Subtype.ext
                exact ConcreteCategory.congr_hom (colimit.w A f) a } }
      have hc : colimit.desc A c ≫ CommRingCat.ofHom S.subtype = 𝟙 (colimit A) := by
        apply colimit.hom_ext
        intro i
        rw [← Category.assoc, colimit.ι_desc]
        ext a
        rfl
      have hgood (a : ↥(colimit A)) : a ∈ S := by
        have he := ConcreteCategory.congr_hom hc a
        change (colimit.desc A c a).val = a at he
        exact he ▸ (colimit.desc A c a).property
      refine ⟨{
        toFun := fun m ↦
          { toFun := bb m
            map_add' := (bb m).map_add
            map_smul' := fun a n ↦ (hgood a m n).2 }
        map_add' := by intro m m'; ext n; exact baddM m m' n
        map_smul' := by intro a m; ext n; exact (hgood a m n).1 }, ?_⟩
      exact hb
    · exact ⟨0, fun i ↦ False.elim (hI ⟨i⟩)⟩
  obtain ⟨β, hβ⟩ := hpairing
  let q : P →ₗ[R] ↥(colimit T) := TensorProduct.lift β
  have hqp : q.toAddMonoidHom.comp p = AddMonoidHom.id _ := by
    apply colimit_tensor_addHom_ext A M N T e
    intro i m n
    change q (p (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n)))) = _
    rw [hp]
    exact hβ i m n
  have hqp' : Function.LeftInverse q p := DFunLike.congr_fun hqp
  have hpq : p.comp q.toAddMonoidHom = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      change p (β m n) = m ⊗ₜ[R] n
      have hh (n : ↥(colimit N)) :
          p.comp (β.flip n).toAddMonoidHom =
            ((TensorProduct.mk R ↥(colimit M) ↥(colimit N)).flip n).toAddMonoidHom := by
        apply colimit_addHom_ext M
        intro i mi
        have hi : p.comp (β (colimit.ι M i mi)).toAddMonoidHom =
            (TensorProduct.mk R ↥(colimit M) ↥(colimit N)
              (colimit.ι M i mi)).toAddMonoidHom := by
          apply colimit_addHom_ext N
          intro j nj
          obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
          have hmi := ConcreteCategory.congr_hom (colimit.w M (homOfLE hik)) mi
          have hnj := ConcreteCategory.congr_hom (colimit.w N (homOfLE hjk)) nj
          change colimit.ι M k (M.map (homOfLE hik) mi) = colimit.ι M i mi at hmi
          change colimit.ι N k (N.map (homOfLE hjk) nj) = colimit.ι N j nj at hnj
          change p (β (colimit.ι M i mi) (colimit.ι N j nj)) =
            colimit.ι M i mi ⊗ₜ[R] colimit.ι N j nj
          rw [← hmi, ← hnj, hβ, hp]
        exact DFunLike.congr_fun hi n
      exact DFunLike.congr_fun (hh n) m
    | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs
  have hpq' : Function.LeftInverse p q := DFunLike.congr_fun hpq
  let ψ : ↥(colimit T) →ₗ[R] P :=
    { p with
      map_smul' := by
        intro a t
        apply hpq'.injective
        change q (p (a • t)) = q (a • p t)
        rw [hqp' (a • t), q.map_smul, hqp' t] }
  refine ⟨ψ, hp, ?_, ⟨hqp'.injective, hpq'.surjective⟩, ?_⟩
  · intro χ hχ
    exact colimit_tensor_addHom_ext A M N T e χ p (fun i m n ↦ (hχ i m n).trans
      (hp i m n).symm)
  · intro M' N' T' _ _ _ _ _ _ _ _ e' f g F G H ψ'
      _ _ _ _ _ _ _ _ hF hG hH hψ'
    apply LinearMap.toAddMonoidHom_injective
    apply colimit_tensor_addHom_ext A M N T e
    intro i m n
    change ψ' (H (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n)))) =
      TensorProduct.map F G (p (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))))
    rw [hH, hψ', hp, TensorProduct.map_tmul, hF, hG]

end TensorProduct
