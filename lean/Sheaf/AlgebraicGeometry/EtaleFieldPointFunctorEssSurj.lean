/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFieldPointFunctor
import Sheaf.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields
import Sheaf.FieldTheory.EtaleFieldGaloisClassification
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Essential surjectivity of the geometric-point functor

Source: Stacks Project, Tag 03QR.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] etaleFieldDiscreteForget₂ etaleFieldActionForget₂

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

/-- Every discrete continuous Galois set is the geometric points of an étale scheme.
Source: Stacks Project, Tag 03QR, construction of an inverse
(blueprint: lem-exc-etale-field-point-functor-ess-surj).

Proof: Decompose the Galois set into orbits and choose one point in each orbit.
Continuity and discreteness make its stabilizer open. Compactness of the Galois group
makes the quotient by this open stabilizer finite. The finite Galois classification
identifies this orbit with the embeddings into Ksep of the stabilizer's fixed field.
That field is finite separable over K. Take the coproduct of these field spectra.
Each component is étale over K, and etaleness is local on the source, so the coproduct
is étale. A morphism from Spec Ksep to a coproduct factors through a unique component,
since Spec Ksep is a one-point scheme. Thus the geometric points of the coproduct are
the disjoint union of the embedding sets, equivariantly isomorphic to the given set.
For the empty set the construction is the empty coproduct, hence the empty scheme. -/
theorem etaleFieldPointFunctor_essSurj :
    (etaleFieldPointFunctor K Ksep).EssSurj := by sorry

end AlgebraicGeometry
