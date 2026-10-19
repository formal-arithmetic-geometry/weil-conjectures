/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.CategoryTheory.YonedaExtensionClass
import Sheaf.CategoryTheory.YonedaClassNaturality

/-! # Signed class of a splice

Source: Stacks Project, Tags 06XU and 06XV, Yoneda composition.
(blueprint: lem-coef-yoneda-class-splice)
-/

@[expose] public section

universe u v w

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

set_option backward.isDefEq.respectTransparency false in
/-- Splicing a short exact sequence on the left has the positive-projection
sign prescribed by the extension-complex roof.
Source: Stacks Project, Tags 06XU and 06XV, Yoneda composition.
Proof: compare the specified splice with the canonical cut at the cokernel of
its first injection. The short exact sequence identifies its third object with
that cokernel, using the endpoint and first-middle isomorphisms in Splice.
The splice square induces a morphism between the remaining tails; its last
component respects the endpoint by right_comm. Naturality of the short exact
connecting class and of the smaller-degree extension class identifies the two
composites. By the defining recursion the canonical cut contributes (-1)^n,
so the displayed signed formula follows. Equivalently, shifting a short exact
complex by n+1 contributes (-1)^(n+1), and replacing its positive projection by
Mathlib's negative connecting class contributes the remaining minus sign.
(blueprint: lem-coef-yoneda-class-splice) -/
theorem derivedClass_splice (U : A) (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact)
    (F : YonedaExtension A S.X₃ U (n + 1))
    (E : YonedaExtension A S.X₁ U (n + 2)) (s : Splice S F E) :
    E.derivedClass (n + 1) =
      (-1 : ℤ) ^ n • ((F.derivedClass n).comp hS.extClass (by omega))  := by
  have : Epi S.g := hS.epi_g
  let a := E.sequence.map' 0 1
  have hz : S.f ≫ s.firstIso.hom ≫ cokernel.π a = 0 := by
    rw [← Category.assoc, s.first_comm]
    simp [a]
  let q : S.X₃ ⟶ cokernel a :=
    hS.exact.desc (s.firstIso.hom ≫ cokernel.π a) hz
  have hq : S.g ≫ q = s.firstIso.hom ≫ cokernel.π a :=
    hS.exact.g_desc _ hz
  let h : S ⟶ E.head :=
    { τ₁ := E.leftIso.inv
      τ₂ := s.firstIso.hom
      τ₃ := q
      comm₁₂ := s.first_comm.symm
      comm₂₃ := hq.symm }
  let φ : F.sequence ⟶ E.tail.sequence :=
    ComposableArrows.homMkSucc (F.leftIso.hom ≫ q) s.tailIso.hom (by
      apply (cancel_epi (S.g ≫ F.leftIso.inv)).1
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc S.g q, hq]
      change S.g ≫ F.leftIso.inv ≫ F.sequence.map' 0 1 ≫ s.tailIso.hom.app 0 =
        (s.firstIso.hom ≫ cokernel.π a) ≫ cokernel.desc a _ _
      simpa only [cokernel.π_desc, Category.assoc] using s.splice_comm)
  have hl : F.leftMap E.tail φ = q := by
    change F.leftIso.inv ≫ (F.leftIso.hom ≫ q) ≫ 𝟙 (cokernel a) = q
    simp
  have hr : F.rightMap E.tail φ = 𝟙 U := by
    change F.rightIso.inv ≫ s.tailIso.hom.app (Fin.last (n + 1)) ≫
      E.rightIso.hom = 𝟙 U
    rw [s.right_comm, F.rightIso.inv_hom_id]
  have ht := derivedClass_naturality _ _ _ _ n F E.tail φ
  rw [hl, hr, Ext.mk₀_id_comp] at ht
  have hh := hS.extClass_naturality E.head_shortExact h
  dsimp [h] at hh
  change (-1 : ℤ) ^ n •
    (((E.tail.derivedClass n).comp E.head_shortExact.extClass (by omega)).comp
      (Ext.mk₀ E.leftIso.hom) (add_zero _)) = _
  congr 1
  rw [← ht, Ext.comp_assoc_of_second_deg_zero, ← hh,
    ← Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.comp_mk₀_id]

end CategoryTheory.YonedaExtension
