/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Paper.StrictPerfectRingedPullbackModel

/-! # Perfect tensor direct image with proper support on algebraic spaces

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 0A1P, perfectness assertion;
Tags 08G5 and 08JL (blueprint: lem-sfb-proper-support-tensor-perfect).
-/

@[expose] public section

set_option autoImplicit false

attribute [instance] CategoryTheory.module_overFunctor_preservesZero

universe c v r u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Local bounded strict-perfect models at the actual section universe.
The rank and both bounds may vary with the covering member.
Source: Stacks 08G5 (blueprint: lem-sfb-proper-support-tensor-perfect). -/
def IsLocallyStrictPerfectAtCoefficientSize (R : Sheaf J RingCat.{r})
    (K : CochainComplex (SheafOfModules.{r} R) ℤ) : Prop :=
  ∀ V : C, ∃ A : Sieve V, A ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), A f →
      ∃ F : CochainComplex (SheafOfModules.{r} (R.over U)) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
        Nonempty (StrictPerfectCoefficientPackageOnSite _ F) ∧
        ∃ α : F ⟶ ((overFunctor R U).mapHomologicalComplex (.up ℤ)).obj K,
          QuasiIso α

/-- Perfect means represented by a complex with local bounded finite-free-retract models.
Source: Stacks 08G5 (blueprint: lem-sfb-proper-support-tensor-perfect). -/
def IsPerfectAtCoefficientSize (R : Sheaf J RingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r} R)]
    (E : DerivedCategory (SheafOfModules.{r} R)) : Prop :=
  ∃ K : CochainComplex (SheafOfModules.{r} R) ℤ,
    IsLocallyStrictPerfectAtCoefficientSize R K ∧ Nonempty (E ≅ DerivedCategory.Q.obj K)

end SheafOfModules

namespace AlgebraicGeometry.AlgebraicSpace

/-- Perfect tensor direct image with a bounded, relatively flat, finitely presented
coefficient complex of proper annihilator support is perfect and has quasi-coherent
cohomology. Source: Stacks 0A1P, 08G5 and 08JL
(blueprint: lem-sfb-proper-support-tensor-perfect).

Proof:
1. A perfect object has quasi-coherent cohomology: on strict-perfect charts, each
term is a finite-free retract and hence the kernel of one minus an idempotent.
Kernels, images and cokernels are quasi-coherent by lem-sfb-space-qcoh-kernels-colimits;
restriction is exact by lem-sfb-ringed-site-restriction-kflat and quasi-coherence is local.
2. Apply lem-sfb-space-perfect-flat-proper-model to descend f, E and the coefficient
complex to Noetherian models on an affine étale cover of Y. Apply
lem-sfb-space-noetherian-tensor-perfect to each model to obtain a perfect direct image.
3. Apply lem-sfb-space-flat-complex-base-change to the cover and to each approximation
map. Its ordinary coefficient-complex pullback is exactly the model identification,
so the restriction of the desired direct image is the pullback of the model direct image.
4. The strict-perfect pullback construction of
lem-weil-pbc-strict-perfect-ringed-pullback-model preserves bounded finite-free splittings.
Thus these pullbacks are perfect; compose their covering sieves to get perfectness
on Y. Step 1 gives quasi-coherence of every cohomology sheaf. -/
theorem properSupport_tensor_perfect
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (f : X ⟶ Y)
    (_hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (E : X.DerivedModules)
    (_hE : SheafOfModules.IsPerfectAtCoefficientSize X.smallStructureRings E)
    (G : CochainComplex X.Modules ℤ)
    (_hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (_hqc : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (_hfinite : ∀ n : ℤ, (G.X n).IsFinitePresentation)
    (_hflat : ∀ n : ℤ, ModuleIsFlatOver f (G.X n))
    (_hproper : ∀ n : ℤ, HasProperAnnihilatorSupport f (G.X n)) :
    SheafOfModules.IsPerfectAtCoefficientSize Y.smallStructureRings
      ((derivedDirectImage f).obj (moduleDerivedTensorComplex X E G)) ∧
    Y.derivedQCohProperty
      ((derivedDirectImage f).obj (moduleDerivedTensorComplex X E G)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
