/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Cohomology and tensor product over a constant field sheaf

Source: the blueprint, `lem-exc-residue-tor-test.proof.md`, second paragraph;
Stacks Project, Tags 03CY, 03ET, 0GMW, 00WJ and 010N
(blueprint: lem-exc-constant-field-sheaf-tensor-cohomology).
-/

@[expose] public section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Tensoring with any module sheaf over the constant field sheaf commutes with cohomology,
naturally in both variables, and sends `[z] ⊗ y` to `[z ⊗ y]` on local sections.
Source: blueprint `lem-exc-residue-tor-test.proof.md`, second paragraph, expanded by Stacks
Tags 03CY, 03ET, 0GMW, 00WJ and 010N
(blueprint: lem-exc-constant-field-sheaf-tensor-cohomology).

Proof:
1. Restrict a module sheaf N along the map from the constant presheaf field to its
sheafification. Its sections are vector spaces over the field; its associated module
sheaf is N, by the module-sheafification interface [lem-pc-sites-module-sheafification-interface].
This does not identify sections of the constant sheaf with the field itself.
2. Vector spaces are free, hence projective [lem-weil-pbc-vector-space-projective] and flat
[lem-weil-pbc-projective-module-flat]. Tensoring sections preserves kernels by
[lem-weil-pbc-flat-tensor-exact], and preserves finite products by the usual two-factor
sum of pure tensors. Equalizers are kernels of differences, so the presheaf tensor functor
preserves finite limits, which are computed objectwise.
3. By [lem-pc-sites-modules-sheafification-flat], sheafification gives flatness of N.
Thus the sheaf tensor functor is exact [def-pc-flat-sheaf-modules] in the abelian module
sheaf category [def-weil-sheaf-of-modules-category].
4. Apply [lem-sp-exact-functor-preserves-homology] to the three terms in degrees i-1,i,i+1.
Its kernel and image comparisons, compatible with the cycle and quotient maps, give
the displayed isomorphisms and naturality in chain maps. No boundedness is required.
5. The tensor of a cycle section with y is a cycle; changing the cycle by a boundary
changes this tensor by a boundary. The quotient compatibility therefore sends `[z] ⊗ y`
to `[z ⊗ y]`. Both composites for a morphism N → N' send this to `[z ⊗ g(y)]`.
Pure tensors and cycle classes locally generate the sheafified tensor and quotient,
so these equalities give naturality in N and the required local formula. -/
theorem exists_constantFieldTensorCohomology
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{m} C] [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
    (κ : Type r) [Field κ] (i : ℤ) :
    ∃ e : ∀
      (N : ringedSiteModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ))))
      (K : CochainComplex
        (ringedSiteModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ)))) ℤ),
      (siteSheafTensorRight N).obj (K.homology i) ≅
        (((siteSheafTensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i,
      (∀ N K L (f : K ⟶ L),
        (e N K).hom ≫ HomologicalComplex.homologyMap
            (((siteSheafTensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i =
          (siteSheafTensorRight N).map (HomologicalComplex.homologyMap f i) ≫ (e N L).hom) ∧
      (∀ N N' (g : N ⟶ N') K,
        (e N K).hom ≫ HomologicalComplex.homologyMap
            (((siteSheafTensorRightMap g).mapHomologicalComplex (ComplexShape.up ℤ)).app K) i =
          (siteSheafTensorRightMap g).app (K.homology i) ≫ (e N' K).hom) ∧
      (∀ N (K : CochainComplex
          (ringedSiteModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
            ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ)))) ℤ)
          (U : Cᵒᵖ) (z : (K.cycles i).val.obj U) (y : N.val.obj U),
        ∃ w : ((((siteSheafTensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).cycles i).val.obj U,
          (((((siteSheafTensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).iCycles i).val.app U) w =
              siteSheafTensorTmul (K.X i) N U (((K.iCycles i).val.app U) z) y ∧
          (((e N K).hom.val.app U)
            (siteSheafTensorTmul (K.homology i) N U (((K.homologyπ i).val.app U) z) y)) =
              (((((siteSheafTensorRight N).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K).homologyπ i).val.app U) w) := by
  sorry

end SheafOfModules
