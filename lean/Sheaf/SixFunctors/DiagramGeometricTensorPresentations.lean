/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.SixFunctors.DiagramPullbackShiftData

/-! # DiagramGeometricTensorPresentations

Resolving-model step for the simultaneous diagram-site comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  SheafOfModules.KFlatFixedTensor.representativeIso
  CategoryTheory.Functor.mapDerivedCategory
  HomologicalComplex₂.total

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open SheafOfModules.DerivedTensorConstraints

namespace WeilConjectures.DiagramPullbackShift

variable (A : ℕ → CommRingCat.{u + 1}) (δ : ∀ n : ℕ, A (n + 1) ⟶ A n)

/-- The geometric inverse images, their section-normalized compositors and their
resolving tensor comparisons can be chosen over any prescribed normalized tensor
constraints. This statement imposes no derived shift coherence.
Source: Stacks sites.tex, morphisms of sites and composition; sites-modules.tex,
lemma-tensor-product-pullback (03EL); sites-cohomology.tex,
lemma-pullback-K-flat (0G7E) and lemma-pullback-tensor-product (07A4).
(blueprint: lem-pur-diagram-geometric-tensor-presentations).

Proof: on the entire sequence site use integralComparisonSequenceBaseChange v.
The adjoint of its direct image defines the set inverse image. Pullback of the
constant ring at each index identifies the inverse image of the system ring
with the target system ring, naturally in every adjacent coefficient map.
Use this identification for the algebraic inverse-image presentation and the
canonical scalar-extension comparison. The resulting module adjunction has
right adjoint the specified module pushforward; its unit is the set-adjunction
unit followed by the module-underlying and generator comparison. Exactness
follows from the left exact geometric inverse image and the constant-ring
identification; the left adjoint also preserves finite colimits. The right
compositors are precomposition with the scheme pullbackComp isomorphism, giving
the displayed section formula. Conjugate these through the set and module
adjunctions; on generators both units insert 1, proving scalarAssociation.
Flat-term K-flat preservation and the unique representative-normalized tensor
comparison are supplied by ringedTopoiCanonicalDerivedTensorPullback. These
give TensorPullback, with its normalization in the orientation specified by
comparison. Set the constraints field to the given family T. No flatness of
coefficient transition maps or boundedness of complexes is used. -/
theorem diagramGeometricTensorPresentations
    (T : ∀ W : Scheme.{u}, TensorConstraints A δ W) :
    ∃ S : Models A δ, S.constraints = T := by sorry

end WeilConjectures.DiagramPullbackShift
