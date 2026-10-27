/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Algebra.Homology.RingedForgetTensorTranspositionData

/-! # Normalized unit comparison for ringed tensor functors
Source: Stacks 0FPT (blueprint: lem-sf-ringed-forget-tensor-unit-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s wb wa
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
-- Keep fixed derived-category constructions behind their APIs during elaboration.
attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

namespace CategoryTheory.RingedForgetTensorTransposition

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

include u SB TB βB cB SA TA βA cA
/--
The representative unit calculation for the left unitor is reduced to the
componentwise model equation for the normalized tensor comparison.
(blueprint: lem-sf-ringed-forget-tensor-left-representatives)
Proof in words: apply the representative model equation to the unit complex and
`P`. Naturality of the tensor-model comparisons, together with the exact-functor
localization factor, reduces the assertion to the unit square on total complexes.
In degree `n`, restrict to the only nonzero unit summand: `(0,n)` on the left
and `(n,0)` on the right. Use the summand formula and the single-complex comparison
in the displayed composite to obtain `u.coherence.left_unit`.
The corresponding unitor model equations of `cB` and `cA` transport this equality
back to the derived category. Local pure tensors and sheafification detect the
component maps, so no hypothesis of generation by global sections is needed.
Source: Stacks Project, sites-cohomology.tex, Tags 0FPT and 06YU.
-/
theorem ringed_forget_tensor_left_representatives
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p)))
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (μ : SB.tensor ⋙ U.mapDerivedCategory ≅
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor)
    (hμ : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain μ.hom)
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) :
    (μ.hom.app (SB.monoidal.tensorUnit, DerivedCategory.Q.obj P) ≫
        SA.tensor.map
          (X := (U.mapDerivedCategory.obj SB.monoidal.tensorUnit,
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
          (Y := (SA.monoidal.tensorUnit, U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
          ((U.mapDerivedCategory.mapIso cB.unitIso ≪≫
              U.mapDerivedCategoryFactors.app (ringedTensorUnitComplex.{c, v, r} J R) ≪≫
              DerivedCategory.Q.mapIso
                ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
                  (SheafOfModules.unit ((sheafCompose J
                    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≪≫
              DerivedCategory.Q.mapIso
                ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit) ≪≫
              cA.unitIso.symm).hom, 𝟙 _) ≫
        (SA.monoidal.leftUnitor (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).hom =
      U.mapDerivedCategory.map (SB.monoidal.leftUnitor (DerivedCategory.Q.obj P)).hom) := by sorry

end CategoryTheory.RingedForgetTensorTransposition
