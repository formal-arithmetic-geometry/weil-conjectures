/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.ModuleUnitLocalSupport
import WeilConjectures.AlgebraicGeometry.ModuleSupportRestrictionEnlargement

/-! # Finite support of finite free maps

## References

* Stacks Project, Modules, Tags 01BB and 01AH.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def direct_restrict_map
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V U W : X.Opens) (hUV : U ≤ V) (hWU : W ≤ U)
    {A : SheafOfModules.{u} (R.over U)} {B : SheafOfModules.{u} (R.over V)}
    (l : A ⟶ (overMap R (homOfLE hUV)).obj B) :
    (overMap R (homOfLE hWU)).obj A ⟶
      (overMap R (homOfLE (hWU.trans hUV))).obj B :=
  (overMap R (homOfLE hWU)).map l

private theorem factor_restricted_coproduct
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : X.Opens) (J : Type u) {D : Type*} [Category D]
    (F : SheafOfModules.{u} (R.over U) ⥤ D)
    [CategoryTheory.Limits.PreservesColimit
      (Discrete.functor (fun _ : J ↦ unit (R.over U))) F]
    {N P : D} (p : N ⟶ P) (l : F.obj (free (R := R.over U) J) ⟶ P)
    (a : J → (F.obj (unit (R.over U)) ⟶ N))
    (ha : ∀ i : J, a i ≫ p = F.map (ιFree (R := R.over U) i) ≫ l) :
    ∃ A : F.obj (free (R := R.over U) J) ⟶ N, A ≫ p = l := by
  let hc := CategoryTheory.Limits.Cofan.isColimitMapCoconeEquiv F
    (fun _ : J ↦ unit (R.over U)) (freeCofan (R := R.over U) J)
    (CategoryTheory.Limits.isColimitOfPreserves F (isColimitFreeCofan (R := R.over U) J))
  refine ⟨CategoryTheory.Limits.Cofan.IsColimit.desc hc a,
    CategoryTheory.Limits.Cofan.IsColimit.hom_ext hc _ _ ?_⟩
  intro i
  rw [← Category.assoc, CategoryTheory.Limits.Cofan.IsColimit.fac]
  exact ha i

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 350000 in
-- Dependent finite choices and comparison of restriction functors exceed the default budget.
private theorem exists_finite_support_of_unit_support
    (X : Scheme.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V U : X.Opens) (hUV : U ≤ V)
    (I : Type u) (n : ℕ)
    (l : free (R := R.over U) (ULift.{u} (Fin n)) ⟶
      (overMap R (homOfLE hUV)).obj
        (free (R := R.over V) I)) (x : U)
    (hunit : ∀ b : unit (R.over U) ⟶
        (overMap R (homOfLE hUV)).obj (free (R := R.over V) I),
      ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
        (a : unit (R.over W) ⟶
          (overMap R (homOfLE (hWU.trans hUV))).obj (free (R := R.over V) S)),
        a ≫ (overMap R (homOfLE (hWU.trans hUV))).map
          (freeMap (R := R.over V) ((↑) : S → I)) =
        (overMap R (homOfLE hWU)).map b) :
    ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
      (a : (overMap R (homOfLE hWU)).obj
          (free (R := R.over U) (ULift.{u} (Fin n))) ⟶
        (overMap R (homOfLE (hWU.trans hUV))).obj
          (free (R := R.over V) S)),
      a ≫ (overMap R (homOfLE (hWU.trans hUV))).map
        (freeMap (R := R.over V) ((↑) : S → I)) =
      (overMap R (homOfLE hWU)).map l := by
  classical
  let J := ULift.{u} (Fin n)
  let b (i : J) := ιFree (R := R.over U) i ≫ l
  choose W hWU hx S a ha using fun i : J ↦
    hunit (b i)
  obtain ⟨W', hW'U, hW', hx'⟩ : ∃ (W' : X.Opens), W' ≤ U ∧
      (∀ i : J, W' ≤ W i) ∧ (x : X) ∈ W' := by
    refine ⟨U ⊓ ⨅ i : J, W i, inf_le_left,
      fun i ↦ inf_le_right.trans (iInf_le W i), x.property, ?_⟩
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  obtain ⟨S', hS⟩ : ∃ S' : Finset I, ∀ i : J, S i ⊆ S' := by
    refine ⟨Finset.univ.biUnion S, ?_⟩
    intro i j hj
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hj⟩
  let inc (i : J) : S i → S' := fun j ↦ ⟨j.val, hS i j.property⟩
  let F := overMap R (homOfLE hW'U)
  let G := overMap R (homOfLE (hW'U.trans hUV))
  let L : F.obj (free (R := R.over U) J) ⟶ G.obj (free (R := R.over V) I) :=
    direct_restrict_map X R V U W' hUV hW'U l
  let a₀ (i : J) : F.obj (unit (R.over U)) ⟶ G.obj (free (R := R.over V) (S i)) :=
    (overMap R (homOfLE (hW' i))).map (a i)
  let a' (i : J) : F.obj (unit (R.over U)) ⟶ G.obj (free (R := R.over V) S') :=
    a₀ i ≫
      G.map (freeMap (R := R.over V) (inc i))
  have ha' (i : J) :
      a' i ≫ G.map (freeMap (R := R.over V) ((↑) : S' → I)) =
      F.map (ιFree (R := R.over U) i) ≫ L := by
    have h : a' i ≫ G.map (freeMap (R := R.over V) ((↑) : S' → I)) = F.map (b i) :=
      enlarge_restricted_unit_support X R V U (W i) W' hUV (hWU i) hW'U (hW' i)
        I (S i) S' (hS i) (b i) (a i) (ha i)
    apply h.trans
    exact F.map_comp (ιFree (R := R.over U) i) l
  obtain ⟨A, hA⟩ := factor_restricted_coproduct X R U J F
    (G.map (freeMap (R := R.over V) ((↑) : S' → I))) L a' ha'
  exact ⟨W', hW'U, hx', S', A, hA⟩

set_option backward.isDefEq.respectTransparency false in
/-- A map from a finite free sheaf into a restricted free sheaf has finite basis
support on a neighbourhood of any given point (Stacks, Tags 01BB and 01AH). -/
theorem exists_finite_free_local_support
    (X : Scheme.{u}) (V U : X.Opens) (hUV : U ≤ V)
    (I : Type u) (n : ℕ)
    (l : free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin n)) ⟶
      (overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).obj
        (free (R := (moduleRings X.toRingedSpace).over V) I)) (x : U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
      (a : (overMap (moduleRings X.toRingedSpace) (homOfLE hWU)).obj
          (free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin n))) ⟶
        (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).obj
          (free (R := (moduleRings X.toRingedSpace).over V) S)),
      a ≫ (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).map
        (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → I)) =
      (overMap (moduleRings X.toRingedSpace) (homOfLE hWU)).map l := by
  exact exists_finite_support_of_unit_support X (moduleRings X.toRingedSpace)
    V U hUV I n l x (fun b ↦ exists_unit_local_support X V U hUV I b x)

end AlgebraicGeometry.Scheme.Modules
