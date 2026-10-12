/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Quasi-coherent closure for the canonical derived tensor

Source: Stacks Project, perfect.tex, Tag 08DX.
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The canonical derived tensor preserves quasi-coherent cohomology.
Source: Stacks Project, perfect.tex, Tag 08DX
(blueprint: lem-pc-canonical-derived-tensor-qcoh).
Proof: choose a K-flat resolution P of E and a complex N representing F. The canonical
K-flat derived tensor is isomorphic to Q(Tot(P tensor N)). Apply the second clause of
`derivedPullback_tensor_preserve_QCoh` with the identity morphism of X. Transport its
quasi-coherence conclusion along the canonical tensor comparison isomorphism, using
that homology functors preserve isomorphisms and quasi-coherence is invariant under
isomorphism of sheaves. This argument works for unbounded E and F and the zero objects. -/
theorem canonical_derivedTensor_preserve_QCoh (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E F : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty X E) (hF : schemeDerivedQCohProperty X F) :
    schemeDerivedQCohProperty X (E ⊗ F) := by sorry

end AlgebraicGeometry
