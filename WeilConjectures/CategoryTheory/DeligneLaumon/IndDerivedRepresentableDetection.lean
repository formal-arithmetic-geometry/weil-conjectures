/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Detection by single representable ind-objects

Source: Categories and Sheaves, §15.3; the bounded-below truncation argument in
lem-zl-barrett-ind-realization, step 3.
(blueprint: lem-zl-ind-derived-representable-detection).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

open CategoryTheory.Pretriangulated

/-- The terms of an ind-presentation jointly detect the identity. -/
private theorem ind_zero_of_representables
    {C : Type u} [SmallCategory C] [Abelian C] (Z : Ind C)
    (h : ∀ (A : C) (f : Ind.yoneda.obj A ⟶ Z), f = 0) : IsZero Z := by
  let e := Ind.colimitPresentationCompYoneda Z
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi e.hom).1
  apply colimit.hom_ext
  intro j
  simpa only [Category.assoc, Category.comp_id, comp_zero] using h _
    (colimit.ι (Z.presentation.F ⋙ Ind.yoneda) j ≫ e.hom)

/-- Generation of a pure derived object reduces to generation in the heart. -/
private theorem pure_zero_of_representables
    {C : Type u} [SmallCategory C] [Abelian C] [HasDerivedCategory.{w} (Ind C)]
    (Z : DerivedCategory.Plus (Ind C)) (n : ℤ) [Z.IsLE n] [Z.IsGE n]
    (h : ∀ (A : C) (f : (DerivedCategory.Plus.singleFunctor (Ind C) n).obj
      (Ind.yoneda.obj A) ⟶ Z), f = 0) : IsZero Z := by
  obtain ⟨A, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Plus.ι.obj Z) n
  let e' : Z ≅ (DerivedCategory.Plus.singleFunctor (Ind C) n).obj A :=
    DerivedCategory.Plus.ι.preimageIso e
  have hA : IsZero A := ind_zero_of_representables A (fun B g ↦ by
    apply (DerivedCategory.Plus.singleFunctor (Ind C) n).map_injective
    apply (cancel_mono e'.inv).1
    simpa only [Functor.map_zero, zero_comp] using
      h B ((DerivedCategory.Plus.singleFunctor (Ind C) n).map g ≫ e'.inv))
  exact ((DerivedCategory.Plus.singleFunctor (Ind C) n).map_isZero hA).of_iso e'

/-- Vanishing maps from single representables let us raise a lower bound. -/
private theorem raise_lower_bound
    {C : Type u} [SmallCategory C] [Abelian C] [HasDerivedCategory.{w} (Ind C)]
    (Z : DerivedCategory.Plus (Ind C)) (n : ℤ) [Z.IsGE n]
    (h : ∀ (A : C) (f : (DerivedCategory.Plus.singleFunctor (Ind C) n).obj
      (Ind.yoneda.obj A) ⟶ Z), f = 0) : Z.IsGE (n + 1) := by
  let t := DerivedCategory.Plus.TStructure.t (C := Ind C)
  change t.IsGE Z (n + 1)
  rw [t.isGE_iff_isZero_truncLE_obj n (n + 1) rfl Z]
  have : IsIso ((t.truncGEπ n).app Z) := inferInstance
  let e : (t.truncGE n).obj ((t.truncLE n).obj Z) ≅ (t.truncLE n).obj Z :=
    (t.truncGELEIsoLEGE n n).app Z ≪≫
      ((t.truncLE n).mapIso (asIso ((t.truncGEπ n).app Z))).symm
  have : ((t.truncLE n).obj Z).IsGE n := t.isGE_of_iso e n
  apply pure_zero_of_representables ((t.truncLE n).obj Z) n
  intro A f
  apply t.to_truncLE_obj_ext
  rw [h A (f ≫ (t.truncLEι n).app Z), zero_comp]

/-- Bounded-below orthogonality to all single representables forces vanishing. -/
private theorem zero_of_representables
    {C : Type u} [SmallCategory C] [Abelian C] [HasDerivedCategory.{w} (Ind C)]
    (Z : DerivedCategory.Plus (Ind C))
    (h : ∀ (A : C) (n : ℤ) (f : (DerivedCategory.Plus.singleFunctor (Ind C) n).obj
      (Ind.yoneda.obj A) ⟶ Z), f = 0) : IsZero Z := by
  obtain ⟨q, hq⟩ := Z.property
  have hq' : Z.IsGE q := (DerivedCategory.Plus.isGE_ι_obj_iff Z q).1 hq
  have bounds : ∀ k : ℕ, Z.IsGE (q + k) := by
    intro k
    induction k with
    | zero => simpa using hq'
    | succ k hk =>
      let := hk
      simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using
        raise_lower_bound Z (q + k) (h · _)
  have hcoh (n : ℤ) : IsZero ((DerivedCategory.Plus.homologyFunctor (Ind C) n).obj Z) := by
    by_cases hn : n < q
    · let := hq'
      exact DerivedCategory.Plus.isZero_homology_of_isGE Z q n hn
    · have hbound : Z.IsGE (n + 1) := by
        convert bounds (n + 1 - q).toNat using 1; omega
      let := hbound
      exact DerivedCategory.Plus.isZero_homology_of_isGE Z (n + 1) n (by omega)
  have : IsIso (0 : Z ⟶ 0) := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro n
    exact (hcoh n).isIso
      ((DerivedCategory.Plus.homologyFunctor (Ind C) n).map_isZero (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : Z ⟶ 0))

/-- Single representable objects in all degrees jointly detect isomorphisms.
Source: Categories and Sheaves, §15.3; lem-zl-barrett-ind-realization, step 3.
(blueprint: lem-zl-ind-derived-representable-detection).

Proof: representables generate Ind C, since the arrows from the terms of a filtered
presentation jointly detect zero morphisms. Let Z be a bounded-below derived object
right orthogonal to single representables in every integer degree. Starting at a
lower cohomological bound, the bottom truncation identifies maps from a single
representable in that degree with maps to the bottom cohomology of Z. Generation
forces this cohomology to vanish. Increase the bound by one and repeat. Every
cohomology object vanishes, so Z is zero. For g as in the statement, complete g to
a distinguished triangle. Apply Hom from each single representable, using also
its shifts. Bijectivity for g makes the adjacent cone Hom groups zero by the long
exact sequence. The preceding argument makes the cone zero, hence g invertible.
This also covers the zero abelian category and zero objects; no projectivity of
representables and no common bound on all test objects is assumed. -/
theorem CategoryTheory.indDerived_singleYoneda_detects_iso
    (C : Type u) [SmallCategory C] [Abelian C]
    [HasDerivedCategory.{w} (Ind C)]
    {M N : DerivedCategory.Plus (Ind C)} (g : M ⟶ N)
    (hg : ∀ (A : C) (n : ℤ), Function.Bijective
      (fun h : (DerivedCategory.Plus.singleFunctor (Ind C) n).obj
        (Ind.yoneda.obj A) ⟶ M ↦ h ≫ g)) : IsIso g := by
  let D := DerivedCategory.Plus (Ind C)
  have hinj (A : C) (n : ℤ)
      {a b : (DerivedCategory.Plus.singleFunctor (Ind C) n).obj (Ind.yoneda.obj A) ⟶
        M⟦(1 : ℤ)⟧}
      (hab : a ≫ g⟦1⟧' = b ≫ g⟦1⟧') : a = b := by
    let e := ((DerivedCategory.Plus.singleFunctors (Ind C)).shiftIso
      1 n (n + 1) (by omega)).app (Ind.yoneda.obj A)
    obtain ⟨a', ha⟩ := (shiftFunctor D (1 : ℤ)).map_surjective (e.hom ≫ a)
    obtain ⟨b', hb⟩ := (shiftFunctor D (1 : ℤ)).map_surjective (e.hom ≫ b)
    apply (cancel_epi e.hom).1
    rw [← ha, ← hb]
    apply congrArg (shiftFunctor D (1 : ℤ)).map
    apply (hg A (n + 1)).injective
    apply (shiftFunctor D (1 : ℤ)).map_injective
    change (shiftFunctor D (1 : ℤ)).map (a' ≫ g) =
      (shiftFunctor D (1 : ℤ)).map (b' ≫ g)
    rw [Functor.map_comp, Functor.map_comp, ha, hb, Category.assoc, Category.assoc, hab]
  obtain ⟨Z, u, v, ht⟩ := distinguished_cocone_triangle g
  let T := Triangle.mk g u v
  apply (Triangle.isZero₃_iff_isIso₁ T ht).1
  apply zero_of_representables Z
  intro A n a
  have hav : a ≫ v = 0 := by
    apply hinj A n
    change (a ≫ v) ≫ g⟦1⟧' = 0 ≫ g⟦1⟧'
    rw [Category.assoc, show v ≫ g⟦1⟧' = 0 from comp_distTriang_mor_zero₃₁ T ht,
      comp_zero, zero_comp]
  obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃ T ht a hav
  obtain ⟨c, hc⟩ := (hg A n).surjective b
  change c ≫ g = b at hc
  change a = b ≫ u at hb
  rw [hb, ← hc, Category.assoc,
    show g ≫ u = 0 from comp_distTriang_mor_zero₁₂ T ht, comp_zero]
