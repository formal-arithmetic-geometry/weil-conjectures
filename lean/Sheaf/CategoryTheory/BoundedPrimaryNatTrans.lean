/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Cyclic detection of natural isomorphisms on bounded primary groups

Source: the coefficient devissage in the proof of
`lem-sfb-torsion-open-test-devissage`, steps 4--5.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An additive natural transformation preserving filtered colimits is invertible on
bounded primary groups if it is invertible on the nontrivial cyclic primary groups.
Source: finite abelian group decomposition and the directed union of finitely generated
subgroups, as used in Stacks, Tag 0GJR.
(blueprint: lem-sfb-bounded-primary-natural-transformation).

Proof: decompose each finite subgroup into a finite direct sum of nontrivial cyclic
summands. Each cyclic order divides the given prime power, hence is a positive power
of that prime. Additivity and naturality pass invertibility to the finite direct sum.
Every finitely generated subgroup is finite, since it is finitely generated torsion.
The diagram of these subgroups is directed and its colimit is the whole group.
Preservation of this colimit and naturality give invertibility at the whole group. -/
theorem boundedPrimary_isIso_natTrans
    (F G : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) [F.Additive] [G.Additive]
    (η : F ⟶ G) (ℓ : ℕ) [Fact ℓ.Prime]
    (hcolim : ∀ (I : Type u) [SmallCategory I] [IsFiltered I],
      PreservesColimitsOfShape I F ∧ PreservesColimitsOfShape I G)
    (hcyclic : ∀ s : ℕ, 1 ≤ s →
      IsIso (η.app (AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ s))))))
    (n : ℕ) (M : AddCommGrpCat.{u}) (hM : ∀ m : M, (ℓ ^ n) • m = 0) :
    IsIso (η.app M) := by
  classical
  have hfinite (A : AddCommGrpCat.{u}) [Finite A]
      (hA : ∀ a : A, (ℓ ^ n) • a = 0) : IsIso (η.app A) := by
    obtain ⟨ι, _, d, hd, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A
    let N (i : ι) := AddCommGrpCat.of (ULift.{u} (ZMod (d i)))
    have hN (i : ι) : IsIso (η.app (N i)) := by
      let k := e.symm.toAddMonoidHom.comp (DirectSum.of (fun i ↦ ZMod (d i)) i)
      have hk : Function.Injective k := e.symm.injective.comp (DirectSum.of_injective i)
      have ho : addOrderOf (k 1) = d i :=
        (addOrderOf_injective k hk 1).trans (ZMod.addOrderOf_one _)
      have hdiv : d i ∣ ℓ ^ n := by
        rw [← ho]
        exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (hA (k 1))
      obtain ⟨s, _, hs⟩ := (Nat.dvd_prime_pow (Fact.out : ℓ.Prime)).mp hdiv
      have hpos : 1 ≤ s := by
        by_contra h
        have : s = 0 := by omega
        simp [this] at hs
        have := hd i
        omega
      dsimp only [N]
      rw [hs]
      exact hcyclic s hpos
    let a : A ≅ ⨁ N :=
      ((e.trans (DirectSum.addEquivProd _)).trans
        (AddEquiv.piCongrRight (fun i ↦
          (AddEquiv.ulift (α := ZMod (d i))).symm))).toAddCommGrpIso ≪≫
      (AddCommGrpCat.biproductIsoPi N).symm
    have : IsIso (Functor.whiskerLeft (Discrete.functor N) η) :=
      (NatTrans.isIso_iff_isIso_app _).2 (fun i ↦ hN i.as)
    have : IsIso (η.app (⨁ N)) :=
      isIso_app_coconePt_of_preservesColimit (Discrete.functor N) η
        (biproduct.bicone N).toCocone (biproduct.isColimit N)
    have heq : η.app A = F.map a.hom ≫ η.app (⨁ N) ≫ G.map a.inv := by
      rw [← η.naturality a.inv]
      simp
    rw [heq]
    infer_instance
  let I := {A : AddSubgroup M // A.FG}
  have : Nonempty I := ⟨⟨⊥, AddSubgroup.FG.bot⟩⟩
  have : IsDirectedOrder I := ⟨fun i j ↦
    ⟨⟨i.val ⊔ j.val, i.property.sup j.property⟩,
      (show i.val ≤ i.val ⊔ j.val from le_sup_left),
      (show j.val ≤ i.val ⊔ j.val from le_sup_right)⟩⟩
  let D : I ⥤ AddCommGrpCat.{u} :=
    { obj := fun i ↦ AddCommGrpCat.of i.val
      map := fun {i j} h ↦ AddCommGrpCat.ofHom (AddSubgroup.inclusion (leOfHom h))
      map_id := by intros; rfl
      map_comp := by intros; rfl }
  let c : Cocone D :=
    { pt := M
      ι := { app := fun i ↦ AddCommGrpCat.ofHom i.val.subtype
             naturality := by intros; rfl } }
  have : ReflectsColimit D (forget AddCommGrpCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms D _
  have hc : IsColimit c := by
    apply isColimitOfReflects (forget AddCommGrpCat.{u})
    refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
    · intro m
      let A := AddSubgroup.closure ({m} : Set M)
      have hA : A.FG := ⟨{m}, by simp [A]⟩
      exact ⟨⟨A, hA⟩, ⟨m, AddSubgroup.subset_closure (by simp)⟩, rfl⟩
    · intro i a b hab
      exact ⟨i, 𝟙 i, Subtype.ext hab⟩
  have hD (i : I) : IsIso (η.app (D.obj i)) := by
    have : AddGroup.FG i.val := (AddGroup.fg_iff_addSubgroup_fg _).2 i.property
    have ht : IsAddTorsion i.val := fun a ↦ by
      apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      exact ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos n, Subtype.ext (hM a.val)⟩
    have : Finite i.val := AddCommGroup.finite_of_fg_isAddTorsion i.val ht
    apply hfinite
    intro a
    exact Subtype.ext (hM a.val)
  obtain ⟨hF, hG⟩ := hcolim I
  let := hF
  let := hG
  have : IsIso (Functor.whiskerLeft D η) :=
    (NatTrans.isIso_iff_isIso_app _).2 hD
  exact isIso_app_coconePt_of_preservesColimit D η c hc

end CategoryTheory
