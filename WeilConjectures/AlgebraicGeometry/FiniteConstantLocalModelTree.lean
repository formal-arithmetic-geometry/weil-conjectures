/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QcqsOpenClosedTree
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement

/-!
# A common open-closed tree for finitely many constant-model constructible modules

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph; geometric step 2 of
lem-sfb-finite-constructible-complex-heart-cd.
(blueprint: lem-sfb-finite-constant-local-model-tree)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A finite family of constructible modules admits one finite open-closed tree on
whose leaves every restricted module has a finite constant scalar local model.
This assertion concerns the terms, with no condition on any maps between them.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first
paragraph; step 2 of lem-sfb-finite-constructible-complex-heart-cd; Stacks Tag 09Y4.
(blueprint: lem-sfb-finite-constant-local-model-tree)

Proof: choose each module's finite constructible stratification, using qcqs of X
in the definition of constructibility. Apply the finite open-closed refinement
theorem to these finitely many partitions. Its actual factoring maps from each
nonempty leaf to a stratum allow pullback of that stratum's finite constant local
model, retaining the same finitely presented condensed module on the point.
The pullback compositor identifies this with restriction from X. Convert the
finite numbered tree to its recursive tree by recursion from the leaves; child
indices strictly increase, so reverse finite induction terminates. Its root
isomorphism identifies the root with X. Empty leaves satisfy the local-model
condition using the empty covering family. This also treats an empty family or
an empty root. No coefficient admissibility or cohomological bound is used. -/
theorem exists_finite_constant_local_model_tree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (m : ℕ)
    (M : Fin m →
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ a, IsConstantModelConstructible Λ X (M a)) :
    ∃ tree : QcqsOpenClosedTree X,
      ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf → ∀ a : Fin m,
        HasFiniteConstantLocalModel Λ S ((CondensedRing.upperStar Λ p.toRoot).obj (M a)) := by sorry

end AlgebraicGeometry.ProEtale
