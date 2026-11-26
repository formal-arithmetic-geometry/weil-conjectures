/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero

import WeilConjectures.Topology.ConstantSubsheafNormalizedPresentation
import WeilConjectures.Topology.ConstantSubsheafLowerImageStalks
import WeilConjectures.Topology.ConstantSubsheafQuotientSection

/-! # The lower integer layer and its quotient generator

## References

* Stacks Project, Tag 0A38.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Construct the lower layer and the quotient generator, without asserting exactness. -/
theorem constantSubsheaf_lower_layer_generator
    (X : TopCat.{u})
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (K C : Sheaf AddCommGrpCat X)
    (ι : K ⟶ C)
    [Mono ι]
    (hC : Nonempty (C ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g)
    (e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ))
    (b : ℕ)
    (hb : ∀ x : X, ∃ a : ℕ, a ≤ b + 1 ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) :
    ∃ (L : Sheaf AddCommGrpCat X) (l : L ⟶ K), Mono l ∧
      (∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ L, Epi g) ∧
      (∀ x : X, ∃ a : ℕ, a ≤ b ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk L.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (l ≫ ι).hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) ∧
      ∃ (U V : Opens X), IsCompact (U : Set X) ∧ IsCompact (V : Set X) ∧ V ≤ U ∧
        ∃ q : (abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ cokernel l,
          (∀ x : X, x ∈ V ∨ x ∉ U →
            IsZero (TopCat.Presheaf.stalk (cokernel l).obj x)) ∧
          (∀ x : X, x ∈ U → x ∉ V →
            IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map q.hom)) := by
  classical
  obtain ⟨isoC⟩ := hC
  obtain ⟨n, A, hA, c, hc, g, hg, s, hsection, hvalue, hgcd⟩ :=
    constantSubsheaf_normalized_presentation X K C ι isoC hqc hgen e b hb
  let := hg
  let D := fun i => (abelianOpenExtensionByZero (A i)).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  let f : (∐ D) ⟶ K := Sigma.desc (fun i ↦
    if c i ≤ b then Sigma.ι D i ≫ g else 0)
  let L := image f
  let l : L ⟶ K := image.ι f
  let U := iSup A
  let V := ⨆ i : Fin n, if c i ≤ b then A i else ⊥
  obtain ⟨hbound, hzero, hLzero⟩ :=
    constantSubsheaf_lower_image_stalks X K C ι isoC n A c g s hsection hvalue b hc hgcd e
  obtain ⟨q, hq⟩ :=
    constantSubsheaf_quotient_section X K C ι isoC n A c g s hsection hvalue b hc
      (fun x hx ↦ hzero x (Or.inl hx)) hLzero
  have hU : IsCompact (U : Set X) := by
    change IsCompact ((iSup A : Opens X) : Set X)
    simpa only [Opens.coe_iSup] using isCompact_iUnion hA
  have hV : IsCompact (V : Set X) := by
    change IsCompact ((⨆ i : Fin n, if c i ≤ b then A i else ⊥ : Opens X) : Set X)
    rw [Opens.coe_iSup]
    apply isCompact_iUnion
    intro i
    split_ifs
    · exact hA i
    · exact isCompact_empty
  have hVU : V ≤ U := by
    apply iSup_le
    intro i
    split_ifs
    · exact le_iSup A i
    · exact bot_le
  refine ⟨L, l, inferInstance, ?_, hbound, U, V, hU, hV, hVU, q, hzero, hq⟩
  exact ⟨n, A, hA, factorThruImage f, inferInstance⟩

end TopCat.Sheaf
