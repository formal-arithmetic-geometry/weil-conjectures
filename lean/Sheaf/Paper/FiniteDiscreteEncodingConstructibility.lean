/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding

/-! # Finite discrete coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Finite local models and bounded constructibility under coefficient encoding.
Source: blueprint coefficient-identification proof, steps 8--9; Stacks Tags 03DA and 099R.
(blueprint: lem-sf-finite-discrete-encoding-constructibility).

Proof: the coefficient-sections equation identifies the canonical ring maps after every
scheme inverse image. The section-action equivalence thus commutes with these inverse
images. A finite module over the finite ring is finitely presented. Present it by a
finite scalar matrix: the encodings carry the matrix to exactly the same matrix, and
preserve its cokernel. Hence they identify the corresponding constant sheaves. Apply
these comparisons on each member of the same pro-etale covering; the inverse equivalence
gives the converse. Applying this argument to every immersion in the same finite
constructible stratification proves stratified constructibility in both directions.
On schemes that are not qcqs use the same comparison on every affine open, as required
by both definitions. Finally the termwise derived equivalence is t-exact and commutes
with every homology functor; its inverse has the same properties. This identifies both
boundedness and constructibility of every homology sheaf. -/
theorem encoding_constructibility [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) :
    (∀ M : Internal A T,
      HasFiniteConstantLocalModel (coefficient A) T M ↔
        ordinaryLocalModel A T ((e.ordinary.functor ⋙ e.fixed.functor).obj M)) ∧
    (∀ K : DerivedCategory (Internal A T),
      constantModelBoundedConstructible (coefficient A) T K ↔
        ordinaryBoundedConstructible A T (e.fixedDerived.functor.obj K)) := by sorry

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
