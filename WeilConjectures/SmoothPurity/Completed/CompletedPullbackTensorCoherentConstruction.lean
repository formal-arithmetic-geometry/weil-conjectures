/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorUnitRepresentatives
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorAssociativityRepresentatives
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorUnitFromAssociativity
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorSignedRepresentatives
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationRepresentatives
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorProofImplementations
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorComparison
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Coherent pullback/tensor evaluation and coherence

Source: Stacks 07A4, 0941 and 03D2. These existing proved declarations are
extracted verbatim from the completed construction to keep file compilation
within the project limit. The parent publicly re-exports them.
(blueprint: lem-pur-completed-pullback-tensor-coherent-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] pullbackTensorDerivedEvaluationNormalization

section CoherentEvaluation
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] pullbackTensorSystemComparison pullbackTensorDerivedEvaluation
  pullbackTensorSequenceDerived pullbackTensorSequenceInverse
  finitePullbackTensorConstructionIso canonicalFinitePullbackTensor

end CoherentEvaluation

section CoherentAssociativity
attribute [local irreducible] pullbackTensorCalculus pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorSequenceInverse

end CoherentAssociativity

section CoherentBraiding
attribute [local irreducible] pullbackTensorCalculus pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorBraiding pullbackTensorSequenceInverse

end CoherentBraiding

section CoherentUnit
universe a b c d
open MonoidalCategory

end CoherentUnit

end CoherentSystems

end WeilConjectures
