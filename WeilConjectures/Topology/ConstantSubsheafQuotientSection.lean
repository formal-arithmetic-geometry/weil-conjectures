/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.ConstantSubsheafQuotientGluing
import WeilConjectures.Topology.ConstantSubsheafQuotientStalkIso

/-! # The top-layer quotient section

## References

* Stacks Project, Tag 0A38.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- If the cokernel of `l : L ⟶ K` vanishes on the lower-label union `V` and `L` vanishes off
`V`, there is a morphism from the extension by zero of the constant integer sheaf on `U` to the
cokernel which is an isomorphism on stalks at points of `U` outside `V`. -/
theorem constantSubsheaf_quotient_section
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
    (∀ x : X, x ∈ V → IsZero (TopCat.Presheaf.stalk (cokernel l).obj x)) →
    (∀ x : X, x ∉ V → IsZero (TopCat.Presheaf.stalk L.obj x)) →
    ∃ q : (abelianOpenExtensionByZero U).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ cokernel l,
      ∀ x : X, x ∈ U → x ∉ V →
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map q.hom) := by
  classical
  dsimp only
  intro hzero hLzero
  obtain ⟨q, hq⟩ := constantSubsheaf_quotient_gluing X K C ι isoC n A c s hvalue b hc
    _ (cokernel.π _) hzero
  refine ⟨q, ?_⟩
  exact constantSubsheaf_quotient_stalk_iso X K C ι isoC n A c g s hsection hvalue b hc
    hLzero q hq

end TopCat.Sheaf
