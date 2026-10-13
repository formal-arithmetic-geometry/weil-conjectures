/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Object cohomology equivalences normalized on cocycles

Source: Stacks Project, Section 01FT and Tag 06XR (1).
(blueprint: lem-weil-pbc-object-resolution-cocycle-equivalence)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

/-- The section complex of a complex of abelian sheaves. -/
abbrev sheafSectionComplex
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (V : C) :=
  ((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)).mapHomologicalComplex
      (.up ℕ)).obj K

/-- Evaluate a morphism from the free representable sheaf at the identity generator. -/
noncomputable def sheafCocycleSection
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) (V : C)
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ K.X q) : (sheafSectionComplex J K V).X q :=
  (a.hom.app (op V)).hom
    (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
      (FreeAbelianGroup.of (𝟙 V)))

/-- A sheaf cocycle evaluates to a section cocycle. -/
theorem sheafCocycleSection_closed
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) (V : C)
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ K.X q)
    (ha : a ≫ K.d q (q + 1) = 0) :
    ((sheafSectionComplex J K V).d q (q + 1)).hom
      (sheafCocycleSection J K q V a) = 0 := by
  have h := congrArg (fun f ↦ (f.hom.app (op V)).hom
    (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
      (FreeAbelianGroup.of (𝟙 V)))) ha
  exact h

/-- A cycle in degree q belongs to the kernel used by the short-complex homology API. -/
theorem sectionCycle_mem_kernel (K : CochainComplex AddCommGrpCat.{v} ℕ)
    (q : ℕ) (x : K.X q) (hx : (K.d q (q + 1)).hom x = 0) :
    x ∈ (K.sc q).g.hom.ker := by
  change (K.d q ((ComplexShape.up ℕ).next q)).hom x = 0
  rw [CochainComplex.next ℕ q]
  exact hx

/-- The homology class of a cycle in a complex of abelian groups. -/
noncomputable def sectionCycleClass (K : CochainComplex AddCommGrpCat.{v} ℕ)
    (q : ℕ) (x : K.X q) (hx : (K.d q (q + 1)).hom x = 0) : K.homology q :=
  (K.homologyπ q).hom ((K.sc q).abCyclesIso.inv
    ⟨x, sectionCycle_mem_kernel K q x hx⟩)

/-- The homology class of a section cocycle, constructed from the actual section. -/
noncomputable def sheafCocycleSectionClass
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) (V : C)
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ K.X q)
    (ha : a ≫ K.d q (q + 1) = 0) : (sheafSectionComplex J K V).homology q :=
  sectionCycleClass (sheafSectionComplex J K V) q (sheafCocycleSection J K q V a)
    (sheafCocycleSection_closed J K q V a ha)

/-- Object cohomology admits an equivalence carrying every Ext cocycle to its section class.

Source: Stacks Project, Section 01FT, equation-cohomology-object-site;
Tag 06XR (1), lemma-compute-ext-resolutions.
(blueprint: lem-weil-pbc-object-resolution-cocycle-equivalence)

Proof: Put P(V) equal to the sheafification of the free abelian presheaf on yoneda(V).
The sheafification adjunction, the free abelian adjunction, and Yoneda identify
Hom(P(V), A) additively with A(V), by evaluation at the image of the identity generator.
Naturality in A identifies the Hom cochain complex from P(V) to I with the section
complex of I. Compute Ext with the supplied injective resolution using
InjectiveResolution.extAddEquivCohomologyClass. Its formula on extMk identifies
extMk(a) with the class of a. Pass through the degreewise evaluation identification
and its homology isomorphism: this sends that class to sheafCocycleSectionClass(a).
For the integer extension of I, terms in negative degrees are zero, so restriction
to nonnegative degrees preserves degree-q homology, including q=0. If the Ext
universe differs from the sheaf morphism universe, first apply the canonical Ext
universe equivalence, whose formula on extMk preserves this calculation. The
composite is additive and invertible and gives the stated equivalence and formula.
Empty sites (no V), zero sheaves, and degree zero require no extra hypotheses. -/
theorem objectCohomology_resolution_cocycle_equivalence
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (I : InjectiveResolution F) (q : ℕ) (V : C) :
    ∃ (e : Sheaf.H' F q V ≃+ (sheafSectionComplex J I.cocomplex V).homology q),
      ∀ (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
        (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X q)
        (ha : a ≫ I.cocomplex.d q (q + 1) = 0),
        e (I.extMk a (q + 1) rfl ha) =
          sheafCocycleSectionClass J I.cocomplex q V a ha := by sorry
