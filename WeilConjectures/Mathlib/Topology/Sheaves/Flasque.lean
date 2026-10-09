/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Abelian.DimensionShifting
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Injective and flasque sheaves of abelian groups

Let `X` be a topological space.

* An injective sheaf of abelian groups on `X` is flasque. For opens `V ≤ U`, the sheafified free
  abelian sheaves `ℤ_V ⟶ ℤ_U` on the representable presheaves form a monomorphism, and a
  morphism `ℤ_W ⟶ F` is a section of `F` over `W`; injectivity of `F` extends a section over `V`
  to one over `U`.
* A flasque sheaf of abelian groups has vanishing higher cohomology: `H¹` vanishes since every
  short exact sequence starting at a flasque sheaf is surjective on global sections, and the
  higher cohomology is reduced to `H¹` by embedding into an injective, hence flasque, sheaf.

## Main statements

- `TopCat.Sheaf.isFlasque_of_injective`: injective abelian sheaves are flasque.
- `TopCat.Sheaf.IsFlasque.subsingleton_H`: `H^{n+1}(X, F) = 0` for a flasque abelian sheaf `F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- The sheafified free abelian sheaf `ℤ_W` on the representable presheaf of an open `W`. -/
noncomputable abbrev freeYoneda : Opens X ⥤ Sheaf AddCommGrpCat.{u} X :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- Morphisms `ℤ_W ⟶ F` are the sections of `F` over `W`. -/
noncomputable def freeYonedaHomEquiv (F : Sheaf AddCommGrpCat.{u} X) (W : Opens X) :
    (freeYoneda.obj W ⟶ F) ≃ F.obj.obj (op W) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _).trans yonedaEquiv)

lemma freeYonedaHomEquiv_naturality (F : Sheaf AddCommGrpCat.{u} X) {V W : Opens X}
    (i : V ⟶ W) (b : freeYoneda.obj W ⟶ F) :
    freeYonedaHomEquiv F V (freeYoneda.map i ≫ b) = F.obj.map i.op (freeYonedaHomEquiv F W b) := by
  have h₁ : (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ _
      (freeYoneda.map i ≫ b) = ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
        (yoneda.map i) ≫ (sheafificationAdjunction (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).homEquiv _ _ b :=
    Adjunction.homEquiv_naturality_left _ _ _
  have h₂ := Adjunction.homEquiv_naturality_left (AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ)
    (yoneda.map i) ((sheafificationAdjunction (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).homEquiv _ _ b)
  change yonedaEquiv (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _)
      ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ _
        (freeYoneda.map i ≫ b))) = F.obj.map i.op (yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _)
      ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ _ b)))
  rw [h₁, h₂]
  exact (yonedaEquiv_naturality _ _).symm

instance (V W : Opens X) (i : V ⟶ W) : Mono (freeYoneda.map i) := by
  have (T : (Opens X)ᵒᵖ) : Mono ((((Functor.whiskeringRight _ _ _).obj
      AddCommGrpCat.free).map (yoneda.map i)).app T) := by
    rw [AddCommGrpCat.mono_iff_injective]
    by_cases h : Nonempty (T.unop ⟶ V)
    · obtain ⟨g⟩ := h
      have hb : Function.Bijective ((yoneda.map i).app T) :=
        ⟨fun _ _ _ ↦ Subsingleton.elim (α := T.unop ⟶ V) _ _,
          fun _ ↦ ⟨g, Subsingleton.elim (α := T.unop ⟶ W) _ _⟩⟩
      have : IsIso ((yoneda.map i).app T) := (isIso_iff_bijective _).2 hb
      exact (ConcreteCategory.bijective_of_isIso
        (AddCommGrpCat.free.map ((yoneda.map i).app T))).1
    · have : IsEmpty (T.unop ⟶ V) := not_nonempty_iff.1 h
      intro a b _
      exact Subsingleton.elim (α := FreeAbelianGroup (T.unop ⟶ V)) a b
  have : Mono (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
      (yoneda.map i)) := NatTrans.mono_of_mono_app _
  exact (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_mono _

/-- **Injective abelian sheaves are flasque.** -/
theorem isFlasque_of_injective (F : Sheaf AddCommGrpCat.{u} X) [Injective F] : F.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    refine ⟨freeYonedaHomEquiv F U.unop (Injective.factorThru
      ((freeYonedaHomEquiv F V.unop).symm x) (freeYoneda.map i.unop)), ?_⟩
    change F.obj.map i.unop.op _ = x
    rw [← freeYonedaHomEquiv_naturality, Injective.comp_factorThru, Equiv.apply_symm_apply]

/-- **Flasque abelian sheaves have vanishing higher cohomology.** -/
theorem IsFlasque.subsingleton_H (F : Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero =>
    refine Sheaf.subsingleton_H_one_of_surjective F isTerminalTop fun E Q ι π w hS ↦ ?_
    have : IsFlasque (ShortComplex.mk ι π w).X₁ := ‹F.IsFlasque›
    exact (AddCommGrpCat.epi_iff_surjective _).1 (IsFlasque.epi_of_shortExact hS)
  | succ n ih =>
    let S := ObjectProperty.injectiveShortComplex F
    have hS : S.ShortExact := ObjectProperty.shortExact_injectiveShortComplex F
    have hI : Injective S.X₂ := Injective.injective_under F
    have : IsFlasque S.X₁ := ‹F.IsFlasque›
    have : IsFlasque S.X₂ := isFlasque_of_injective _
    have : IsFlasque S.X₃ := IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    have := ih S.X₃
    have : Subsingleton (Sheaf.H S.X₂ (n + 1 + 1)) :=
      @Abelian.Ext.subsingleton_of_injective _ _ _ _ _ _ hI _
    exact (Sheaf.H.δSucc_surjective hS (n + 1)).subsingleton

end TopCat.Sheaf
