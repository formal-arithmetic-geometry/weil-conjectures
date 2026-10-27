/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.AlgebraicGeometry.StackVersalRing
import Sheaf.RingTheory.ArtinianFiniteTypeResidueCriterion
import Sheaf.AlgebraicGeometry.AlgebraicStackRimSchlessinger
import Sheaf.AlgebraicGeometry.AlgebraicStackTangentFinite

/-! # Existence of versal rings at finite-residue-field stack points

Source: Stacks Project, stacks-geometry.tex, Tag 0DQX (lemma-versal-ring), existence,
with Tag 0DQV (definition-versal-ring-at-x) and situation-versal
(blueprint: lem-sfb-stack-versal-ring-existence).

The complete local algebra, marked tower and prescribed-isomorphism lifting condition
are the existing `CategoryTheory.StackVersal` definitions. Level n means C/m^(n+1),
so every positive infinitesimal level is included.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.StackVersal

/-- A locally finite type algebraic stack over a Noetherian local ring has a versal
complete local ring, together with its marked formal object, at a point with residue
field finite over the closed residue field of the base.

Source: Stacks Project, stacks-geometry.tex, Tag 0DQX, lemma-versal-ring (existence),
and Tag 0DQV, definition-versal-ring-at-x
(blueprint: lem-sfb-stack-versal-ring-existence).

Proof:
1. A finite basis of k over the residue field of R also generates k as an R-algebra:
every coefficient lifts from R/m_R to R. Apply
lem-sfb-artinian-finite-type-residue-criterion to see that every Artinian local test
algebra with this residue field is finite type over R.
2. Apply lem-sfb-algebraic-stack-rim-schlessinger to the algebraic stack over Spec R.
It supplies the restriction equivalence on Artinian finite-type pushouts required
by the general versal-formal-object theorem. No separation hypothesis is needed.
3. The locally finite type smooth atlas and finite-type field k satisfy
lem-sfb-algebraic-stack-tangent-finite. The marked tangent space is finite-dimensional.
Together with step 2, this permits lem-sfb-artin-rs-versal-formal-object to produce a
complete Noetherian local R-algebra C with residue k, a compatible formal tower, and
a specified identification of its first level with x. Its lifting clause retains
every prescribed isomorphism across every surjection of test algebras.
4. Mark every level by its transition to the first level followed by that specified
identification with x. Transition coherence gives compatibility with the markings.
The general lifting theorem supplies local maps inducing the identity on k, and its
isomorphisms respect the markings and extend the prescribed one. Thus the resulting
marked tower satisfies exactly `FormalObject.IsVersal`.
-/
theorem exists_versal_ring
    (R k : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field k] [Algebra R k] [Algebra (IsLocalRing.ResidueField R) k]
    [IsScalarTower R (IsLocalRing.ResidueField R) k]
    [Module.Finite (IsLocalRing.ResidueField R) k]
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (hF : IsAlgebraicModuliStack F)
    (hft : ∃ (U : Over (Spec (.of R)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom)
    (x : Object F k) :
    ∃ (C : CompleteLocalAlgebra R k) (eta : FormalObject F x C), eta.IsVersal := by
  sorry

end CategoryTheory.StackVersal
