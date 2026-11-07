/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.AlgebraicGeometry.AdicLisseModule
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! # Data for completed constant realization

Source: Stacks Tags 093J--093M and 06YU.
(auxiliary; not a blueprint node).

The constructions and interfaces are moved verbatim from
`CompletedConstantFiniteComplexRealization` so that the module and complex calculations
can be stated independently without an import cycle.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u v w vD vE
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
/-- Abelian sheafification at the specified coefficient size, transported through the
small site model. Source: Stacks Tag 03DA
(auxiliary; not a blueprint node). -/
instance completedConstantAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
/-- The locally bijective description at exactly the same coefficient size.
Source: Stacks Tag 03DA
(auxiliary; not a blueprint node). -/
instance completedConstantAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1}
    _
/-- The standard localization, used uniformly for the representative calculations.
Source: Stacks Tag 05RU
(auxiliary; not a blueprint node). -/
abbrev completedConstantDerived (D : Type v) [Category.{w} D] [Abelian D] :=
  @DerivedCategory D _ _ (HasDerivedCategory.standard D)
/-- Termwise application of an additive functor, with its actual differentials.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
def completedConstantMapComplex {D : Type v} {E : Type w} [Category.{vD} D] [Category.{vE} E]
    [Preadditive D] [Preadditive E] (F : D ⥤ E) (hF : F.Additive) :
    CochainComplex D ℤ ⥤ CochainComplex E ℤ :=
  letI := hF
  F.mapHomologicalComplex (ComplexShape.up ℤ)
/-- Module sheaves on the original small site; its object and Hom universes are unequal.
Source: Stacks Tags 09A5 and 03D1
(auxiliary; not a blueprint node). -/
abbrev completedConstantModules (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((adicLisseForget X).obj R)
/-- Ordinary scalar extension, selected with its specified objects and morphisms from
`derivedChangeOfRingsIndependentCoefficients`. Those specifications determine the functor.
Source: Stacks Tags 03EK and 06YY
(auxiliary; not a blueprint node). -/
def completedConstantExtension (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    completedConstantModules X R ⥤ completedConstantModules X S :=
  letI := HasDerivedCategory.standard (completedConstantModules X R)
  letI := HasDerivedCategory.standard (completedConstantModules X S)
  (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u} φ).choose
/-- The scalar extension witness is additive, as specified by the existing derived
change-of-rings theorem. Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
instance completedConstantExtension_additive (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (completedConstantExtension X φ).Additive :=
  letI := HasDerivedCategory.standard (completedConstantModules X R)
  letI := HasDerivedCategory.standard (completedConstantModules X S)
  Exists.choose (Exists.choose_spec (Exists.choose_spec (Exists.choose_spec
    (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u} φ))))
/-- The constant-module sheafification generator, the image of an actual module element.
Source: Stacks Tag 093J, constant sheafification
(auxiliary; not a blueprint node). -/
def completedConstantGenerator (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (N : ModuleCat.{u + 1} B) (U : X.ProEtᵒᵖ) (x : N) :
    ((adicLisseConstantModules X B).obj N).val.obj U :=
  (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of N))).app U x
end AlgebraicGeometry.Scheme
