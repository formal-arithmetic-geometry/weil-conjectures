/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Sheaf.AlgebraicGeometry.Modules.ExtPushoutPostcompose

/-!
# Associativity and the pushout description of Yoneda Ext composition

Source: Stacks Project, Homology, Tag 010I, and Derived Categories, Tag 06XP
(blueprint: lem-sc-p1-ext-yoneda-associativity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Yoneda composition of `Ext` classes of `𝒪_X`-modules on a scheme is associative in all
degrees; the pushout `0 → W → B ⊔_A W → C → 0` of a short exact sequence
`0 → A → B → C → 0` with class `δ` along `φ : A ⟶ W` is short exact with class `φ[1] ∘ δ`;
and consequently `(φ[1] ∘ δ) ∘ s = φ[1] ∘ (δ ∘ s)` for every `s : 𝒪_X ⟶ C`. Mathlib's
`Ext.comp` is written in diagrammatic order, so `φ[1] ∘ δ` is `δ.comp (Ext.mk₀ φ)` and
`δ ∘ s` is `(Ext.mk₀ s).comp δ`.
Source: Stacks Project, Homology, Tag 010I, and Derived Categories, Tag 06XP
(blueprint: lem-sc-p1-ext-yoneda-associativity).

Proof: (1) Represent each Ext class by a derived-category morphism; composition of shifted
morphisms is associative (`lem-sc-p1-ext-yoneda-splicing-associative`, Tag 06XP).
(2) The pushout of the short exact sequence along `φ` is the coefficient-change image of its
extension class, so the pushed-out sequence represents `φ[1] ∘ δ`
(`lem-sc-p1-ext-pushout-postcompose`, Tag 010I).
(3) Apply (1) to `e = s`, `f = δ`, `g = φ[1]` in degrees `0, 1, 0`. -/
theorem ext_yoneda_assoc_pushout {X : Scheme.{u}} [HasExt.{u} X.Modules] :
    (∀ {A B C D : X.Modules} {i j k ij jk n : ℕ} (e : Ext A B i) (f : Ext B C j)
        (g : Ext C D k) (hij : i + j = ij) (hjk : j + k = jk) (h : i + j + k = n),
        (e.comp f hij).comp g (show ij + k = n by omega) =
          e.comp (f.comp g hjk) (show i + jk = n by omega)) ∧
    (∀ (S : ShortComplex X.Modules) (hS : S.ShortExact) {W : X.Modules} (φ : S.X₁ ⟶ W),
      ∃ hT : (ShortComplex.mk (pushout.inr S.f φ)
          (pushout.desc S.g 0 (by rw [S.zero, comp_zero])) (pushout.inr_desc _ _ _)).ShortExact,
        (hT.extClass : Ext S.X₃ W 1) =
          (hS.extClass : Ext S.X₃ S.X₁ 1).comp (Abelian.Ext.mk₀ φ : Ext S.X₁ W 0) (add_zero 1)) ∧
    (∀ (S : ShortComplex X.Modules) (hS : S.ShortExact) {W : X.Modules} (φ : S.X₁ ⟶ W)
        (s : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₃),
      let δ : Ext S.X₃ S.X₁ 1 := hS.extClass
      let φ₀ : Ext S.X₁ W 0 := Abelian.Ext.mk₀ φ
      let s₀ : Ext (SheafOfModules.unit X.ringCatSheaf) S.X₃ 0 := Abelian.Ext.mk₀ s
      s₀.comp (δ.comp φ₀ (add_zero 1)) (zero_add 1) =
        (s₀.comp δ (zero_add 1)).comp φ₀ (add_zero 1)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
