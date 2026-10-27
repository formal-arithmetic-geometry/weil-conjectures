/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D6
-/
module

public import Sheaf.Paper.EtaleBrownProjectionRealization

/-! # Data for a normalized Brown level realization

This module isolates the construction of the realization functors and their
factorization, restriction, and scalar comparison data. The coherence equations
are stated separately so that the categorical construction and its normalization
can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The realization data can be constructed from a supplied strict evaluation package.

Source: Zheng, Construction 4.1 and Constructions 5.14--5.15, together with the
constant-ring module equivalence of Stacks 03CY. The construction first transports
modules along the constant-ring sheafification equivalence, then localizes the exact
transport at every level. The ordinary restriction maps are the sectionwise scalar
restriction maps; their derived maps are obtained by localization. Scalar extension
is the mate of these restriction maps under the supplied scalar adjunctions. This
statement deliberately omits all coherence equations, which are the subject of the
next theorem.
(blueprint: lem-pur-etale-brown-level-realization-data).
-/
theorem etaleBrownLevelRealizationData_exists
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) :
    Nonempty (StrictEtaleBrownRealizationData O t W P) := by sorry

end AlgebraicGeometry
