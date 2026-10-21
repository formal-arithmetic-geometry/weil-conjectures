/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.CategoryTheory.Monoidal.Functor
/-! # Strong monoidality of derived scalar extension.

Source: Stacks Project, Tags 06YS, 07A4 and Categories 04VK.
(blueprint: lem-fix-ringed-scalar-tensor-monoidal). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

/-- The canonical normalized scalar tensor comparison is strong monoidal.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, lemma-pullback-tensor-product,
and Tag 0FPT, lemma-symmetric-monoidal-derived
(blueprint: lem-fix-ringed-scalar-tensor-monoidal).

Proof: use the supplied canonical scalar total-tensor comparison and its
normalization. The generator formula uniquely fixes the chain comparison;
the K-flat counit square uniquely fixes its derived comparison. The coefficient unit
is K-flat in degree zero; scalar multiplication identifies its scalar extension with
the target unit.
Localize this map using D's invertible K-flat counit and the recorded unit
identifications to obtain an invertible derived unit comparison. On three
K-flat representatives, the associativity diagram sends every generator
s tensor ((x tensor y) tensor z) to
(s tensor x) tensor ((1 tensor y) tensor (1 tensor z)) on both routes.
The two unit diagrams are the scalar action laws. Sheafification and the
total coproduct summands detect these equalities. The normalization squares, recorded associator
and unitors, and coefficient unit
identifications descend them to derived objects. K-flat resolutions and
naturality give the equations for arbitrary objects. Package the inverse
unit map and inverse tensor comparison with CoreMonoidal.mk'. This gives m
with precisely the displayed tensorator. Neither flatness of the coefficient map
nor boundedness of complexes is required.
-/
theorem ringedScalarTensorMonoidal
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (AR : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (AS : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
    (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS)
    (βR : @SymmetricCategory _ _ AR.monoidal)
    (βS : @SymmetricCategory _ _ AS.monoidal)
    (hR : RingedDerivedTensorCoherence.{c, v, r, w} J R AR MR βR)
    (hS : RingedDerivedTensorCoherence.{c, v, r, w} J S AS MS βS)
    (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          D.E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (D.E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (D.E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
    (μ : AR.tensor ⋙ D.T ≅ D.T.prod D.T ⋙ AS.tensor)
    (hκ : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y))
    (hμ : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          D.T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (D.ε.app P) (D.ε.app Q)) =
            D.ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom) :
    ∃ (m : @Functor.CoreMonoidal _ _ AR.monoidal _ _ AS.monoidal D.T),
      ∀ P Q, (@Functor.CoreMonoidal.μIso _ _ AR.monoidal _ _ AS.monoidal
        D.T m P Q).hom = μ.inv.app (P, Q) := by
  sorry

end Site
end CategoryTheory
