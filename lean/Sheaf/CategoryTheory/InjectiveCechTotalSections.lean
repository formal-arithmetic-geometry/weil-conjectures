/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.CategoryTheory.CechResolutionDoubleComplex
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.CategoryTheory.SiteInjectiveCechAcyclic
import Sheaf.CategoryTheory.SiteCechMathlibComparison
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Total Čech cohomology of a complex of injective sheaves

Source: blueprint sk-thm-picard-cech, Step 3; Stacks Project Tags 03AW and 03F6.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Row augmentation before extension by zero.
Source: blueprint lem-sc-injective-cech-total-sections, proof Steps 1--3.
(blueprint: lem-sc-injective-cech-total-sections-nat)
Proof: Apply injective Čech acyclicity and the chosen-product comparison to each
row, then apply the first-quadrant column augmentation criterion. -/
theorem injective_cech_total_sections_nat
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)
    (hK : ∀ q : ℕ, Injective (K.X q)) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X) (n : ℕ) :
    Nonempty
      (((HomologicalComplex₂.flip
        (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget X).op ⋙
          cechComplexFunctor (fun i ↦ Over.mk (π i))).mapHomologicalComplex
            (.up ℕ)).obj K)).total (.up ℕ)).homology n ≅
        (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex
            (.up ℕ)).obj K).homology n) := by
  sorry

/-- Row augmentation identifies total Čech cohomology with section-complex cohomology.
This is a statement about any nonnegative complex of injective sheaves, with no
resolution, Ext, or sheaf-cohomology hypothesis.

Source: blueprint sk-thm-picard-cech, Step 3; lem-sc-cech-resolution-total, Steps 1--2;
Stacks Project Tags 03AW and 03F6.
(blueprint: lem-sc-injective-cech-total-sections)

Proof: Regard J as its associated precoverage. Choose iterated fibre products of the
covering; the comparison with Mathlib's Čech complex intertwines the alternating
coface maps. In resolution degree q augment the Čech row by K^q(X), mapping a
section to its restrictions to the covering members. The sheaf condition identifies
row cohomology in degree zero with K^q(X); injective Čech acyclicity gives zero in
all positive degrees. The Hom-set, covering-index and group-value universes are v,
so the free abelian representables used for injective acyclicity have the required
size. The augmentations are natural in K^q, and consequently commute with K's
differential. They define a map from the section complex to the total complex;
its degree-q component is the restriction map into the (0,q) summand. The horizontal
differential annihilates this restriction map, and the vertical sign on this
summand is (-1)^0 = 1. Filter the mapping cone by resolution degree. Its associated
rows are the augmented Čech rows, which are exact. The augmented Čech index starts
at -1 and the resolution index starts at 0, so in each total degree the filtration
is finite. The row spectral sequence therefore has zero first page and zero
abutment; the cone is acyclic, and the section-to-total map is a quasi-isomorphism.
Invert its homology isomorphism and identify nonnegative section cohomology with
that of the extension of K by zero to integer degrees. At n = 0 this extension
has zero incoming differential, as does the original section complex. If the
covering family is empty, the covering sheaf condition forces all K^q(X) to be
zero; both complexes are then acyclic, so the same argument still applies. -/
theorem injective_cech_total_sections
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)
    (hK : ∀ q : ℕ, Injective (K.X q)) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X) (n : ℕ) :
    Nonempty
      (((HomologicalComplex₂.flip
        (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget X).op ⋙
          cechComplexFunctor (fun i ↦ Over.mk (π i))).mapHomologicalComplex
            (.up ℕ)).obj K)).total (.up ℕ)).homology n ≅
        (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex
            (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).homology (n : ℤ)) := by
  obtain ⟨e⟩ := injective_cech_total_sections_nat K hK X π hπ n
  let S := ((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex
      (.up ℕ)).obj K
  let G := sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)
  let m := HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat G
  exact ⟨e ≪≫ (S.extendHomologyIso ComplexShape.embeddingUpNat (by rfl)).symm ≪≫
    (asIso (HomologicalComplex.homologyMap m.hom (n : ℤ))).symm⟩

end CategoryTheory
