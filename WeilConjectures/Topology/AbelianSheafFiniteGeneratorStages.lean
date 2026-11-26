/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.AbelianSheafLocalIntegerGenerator
import Mathlib.Data.Fintype.EquivFin

/-! # Finite-generator stages covering every stalk

## References

* Stacks Project, Tags 02UX, 01AQ and 01AR.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace TopCat

/-- The images of finite sums of local integer generators form a directed subsheaf
system covering every stalk, with finite generating maps from integer extensions by zero. -/
theorem abelianSheaf_finiteGenerator_stages
    (X : TopCat.{u})
    (hbas : ∀ (U : Set X), IsOpen U → ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧
      IsCompact V ∧ x ∈ V ∧ V ⊆ U)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    let S := Σ U : {U : Opens X // IsCompact (U : Set X)}, F.obj.obj (op U.val)
    ∃ (D : Finset S ⥤ X.Sheaf AddCommGrpCat.{u})
      (c : D ⟶ (Functor.const (Finset S)).obj F),
      (∀ (x : X) (t : Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x),
        ∃ (i : Finset S) (s : Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj i).obj x),
          (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (c.app i).hom s = t) ∧
      ∀ i : Finset S, Mono (c.app i) ∧
      (∃ (n : ℕ) (U : Fin n → Opens X)
        (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
        ∃ g : (∐ fun i ↦
          (TopCat.Sheaf.abelianOpenExtensionByZero (U i)).obj
          ((constantSheaf
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ (D.obj i), Epi g) := by
  classical
  let S := Σ U : {U : Opens X // IsCompact (U : Set X)}, F.obj.obj (op U.val)
  let E (s : S) : X.Sheaf AddCommGrpCat.{u} :=
    (TopCat.Sheaf.abelianOpenExtensionByZero s.1.val).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj s.1.val))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  have hlocal (s : S) := abelianSheaf_local_integer_generator X F s.1.val s.2
  choose φ hφ using hlocal
  let a (i : Finset S) (j : Fin i.card) : S := (i.equivFin.symm j).val
  let P (i : Finset S) := ∐ fun j : Fin i.card ↦ E (a i j)
  let p (i : Finset S) : P i ⟶ F := Sigma.desc (fun j ↦ φ (a i j))
  let q {i k : Finset S} (h : i ⟶ k) : P i ⟶ P k :=
    Sigma.desc fun j ↦
      eqToHom (by simp [a]) ≫ Sigma.ι (fun l : Fin k.card ↦ E (a k l))
        (k.equivFin ⟨a i j, h.le (i.equivFin.symm j).property⟩)
  have transport {s t : S} (h : s = t) : eqToHom (congrArg E h) ≫ φ t = φ s := by
    subst t
    simp
  have hq {i k : Finset S} (h : i ⟶ k) : q h ≫ p k = p i := by
    apply Sigma.hom_ext
    intro j
    simp only [q, p, Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc]
    exact transport (by simp [a])
  let dmap {i k : Finset S} (h : i ⟶ k) : image (p i) ⟶ image (p k) :=
    image.lift
      { I := image (p k)
        m := image.ι (p k)
        e := q h ≫ factorThruImage (p k)
        fac := by simpa using hq h }
  have hdmap {i k : Finset S} (h : i ⟶ k) :
      dmap h ≫ image.ι (p k) = image.ι (p i) := image.lift_fac _
  let D : Finset S ⥤ X.Sheaf AddCommGrpCat.{u} :=
    { obj := fun i ↦ image (p i)
      map := fun h ↦ dmap h
      map_id := fun i ↦ by
        apply (cancel_mono (image.ι (p i))).mp
        simp only [hdmap, Category.id_comp]
      map_comp := fun h h' ↦ by
        apply (cancel_mono (image.ι _)).mp
        simp only [hdmap, Category.assoc] }
  let c : D ⟶ (Functor.const (Finset S)).obj F :=
    { app := fun i ↦ image.ι (p i)
      naturality := fun i k h ↦ by
        change dmap h ≫ image.ι (p k) = image.ι (p i) ≫ 𝟙 F
        simpa using hdmap h }
  refine ⟨D, c, ?_, ?_⟩
  · intro x t
    obtain ⟨U, hxU, s, rfl⟩ := Presheaf.exists_germ_eq F.obj t
    obtain ⟨V, hVo, hVc, hxV, hVU⟩ := hbas U U.isOpen x hxU
    let W : Opens X := ⟨V, hVo⟩
    let r := F.obj.map (homOfLE hVU : W ⟶ U).op s
    let b : S := ⟨⟨W, hVc⟩, r⟩
    obtain ⟨z, hz⟩ := hφ b x hxV
    let i : Finset S := {b}
    let j : Fin i.card := i.equivFin ⟨b, by simp [i]⟩
    have hj : a i j = b := by simp [a, j]
    let l : E b ⟶ image (p i) :=
      eqToHom (congrArg E hj.symm) ≫ Sigma.ι (fun j : Fin i.card ↦ E (a i j)) j ≫
        factorThruImage (p i)
    have hl : l ≫ c.app i = φ b := by
      dsimp only [l, c]
      simp only [Category.assoc, image.fac, p, Sigma.ι_comp_desc]
      exact transport hj.symm
    refine ⟨i, (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map l.hom z, ?_⟩
    have hh := congrArg (fun f ↦ (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom z) hl
    change (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (l.hom ≫ (c.app i).hom) z = _ at hh
    rw [Functor.map_comp, AddCommGrpCat.comp_apply] at hh
    rw [hh]
    erw [hz]
    exact Presheaf.germ_res_apply F.obj (homOfLE hVU : W ⟶ U) x hxV s
  · intro i
    refine ⟨inferInstance, i.card, fun j ↦ (a i j).1.val,
      fun j ↦ (a i j).1.property, factorThruImage (p i), inferInstance⟩

end TopCat
