/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.AbelianOpenExtensionIntegerGermCoordinates
import WeilConjectures.Topology.ConstantSubsheafQuotientGermCoordinates
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Stalk isomorphisms for the top-layer quotient

## References

* Stacks Project, Tag 0A38.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

private theorem isIso_of_integer_coordinates {G H : AddCommGrpCat.{u}}
    (f : G ⟶ H) (a : G) (t : H)
    (ha : ∀ v : G, ∃! z : ℤ, z • a = v)
    (ht : ∀ v : H, ∃! z : ℤ, z • t = v) (hfa : f a = t) : IsIso f := by
  apply (ConcreteCategory.isIso_iff_bijective f).mpr
  constructor
  · intro v w hvw
    obtain ⟨z, hz, _⟩ := ha v
    obtain ⟨k, hk, _⟩ := ha w
    obtain ⟨r, hr, hu⟩ := ht (f v)
    have hz' : z • t = f v := by rw [← hfa, ← map_zsmul f.hom, hz]
    have hk' : k • t = f v := by rw [← hfa, ← map_zsmul f.hom, hk, hvw]
    have hzk : z = k := (hu z hz').trans (hu k hk').symm
    rw [← hz, ← hk, hzk]
  · intro v
    obtain ⟨z, hz, _⟩ := ht v
    refine ⟨z • a, ?_⟩
    rw [map_zsmul f.hom, hfa, hz]

/-- If `L` vanishes off the lower-label union `V`, any morphism from the extension by zero of
the constant integer sheaf on `U` to the cokernel of `l : L ⟶ K` sending each top-label unit
section to the image of `s i` is an isomorphism on stalks at points of `U` outside `V`. -/
theorem constantSubsheaf_quotient_stalk_iso
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (n : ℕ) (A : Fin n → Opens X) (c : Fin n → ℕ)
    (g : (∐ fun i => (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K) [Epi g]
    (s : ∀ i, K.obj.obj (op (A i)))
    (hsection : ∀ i,
      (Sigma.ι (fun j => (abelianOpenExtensionByZero (A j)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) i ≫ g).hom.app
        (op (A i))
        (abelianOpenExtensionSection (A i)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
          ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1))) = s i)
    (hvalue : ∀ i, (ι ≫ isoC.hom).hom.app (op (A i)) (s i) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op (A i)) (ULift.up (c i : ℤ)))
    (b : ℕ) (hc : ∀ i, 0 < c i ∧ c i ≤ b + 1) :
    let D := fun i => (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    let f : (∐ D) ⟶ K := Sigma.desc (fun i ↦
      if c i ≤ b then Sigma.ι D i ≫ g else 0)
    let L := image f
    let l : L ⟶ K := image.ι f
    let U := iSup A
    let V := ⨆ i : Fin n, if c i ≤ b then A i else ⊥
    (∀ x : X, x ∉ V → IsZero (TopCat.Presheaf.stalk L.obj x)) →
    ∀ q : (abelianOpenExtensionByZero (iSup A)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ cokernel l,
      (∀ i, c i = b + 1 → q.hom.app (op (A i))
        (abelianOpenExtensionSection (iSup A)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
          (A i) (le_iSup A i)
          ((toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (iSup A)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (iSup A).inclusion').obj (A i))) (ULift.up 1))) =
          (cokernel.π l).hom.app (op (A i)) (s i)) →
      ∀ x : X, x ∈ U → x ∉ V →
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map q.hom) := by
  classical
  intro D f L l U V hLzero q hq x hxu hxv
  obtain ⟨i, hxi⟩ := (Opens.mem_iSup.mp hxu)
  have hci : c i = b + 1 := by
    have hn : ¬ c i ≤ b := by
      intro h
      apply hxv
      exact (le_iSup (fun j : Fin n ↦ if c j ≤ b then A j else ⊥) i)
        (by simpa [h] using hxi)
    have hi := (hc i).2
    omega
  let E := (abelianOpenExtensionByZero (iSup A)).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  let a := TopCat.Presheaf.germ E.obj (A i) x hxi
    (abelianOpenExtensionSection (iSup A)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
      (A i) (le_iSup A i)
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (iSup A)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (iSup A).inclusion').obj (A i))) (ULift.up 1)))
  let t := TopCat.Presheaf.germ (cokernel l).obj (A i) x hxi
    ((cokernel.π l).hom.app (op (A i)) (s i))
  let Q := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map q.hom
  have ha : ∀ v : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.obj x),
      ∃! z : ℤ, z • a = v :=
    abelianOpenExtension_integer_germ_coordinates X (iSup A) (A i) (le_iSup A i) x hxi
  have ht : ∀ v : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (cokernel l).obj x),
      ∃! z : ℤ, z • t = v :=
    constantSubsheaf_quotient_germ_coordinates X K C ι isoC n A c g s hsection hvalue b hc
      L l x (hLzero x hxv) hxv i hxi
  have hQa : Q a = t := by
    dsimp only [Q, a, t]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hq i hci]
  exact isIso_of_integer_coordinates Q a t ha ht hQa

end TopCat.Sheaf
