/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.Paper.QcqsLatticeTreeReconstruction

/-! # Integral leaf models for constructible rational modules

Source: the finite open/closed refinement and lattice argument of
lem-sfb-qcqs-rational-integral-localizing-generators, proof steps 2--3.
-/

@[expose] public section

set_option autoImplicit false


universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale


/-- A constructible rational module has integral lisse models on the leaves of an
actual finite qcqs open/closed tree. The field can vary between leaves in the closure
case. This assertion concerns sheaves and their underived scalar extensions only.

Source: blueprint sk-lem-stratified-lattice, finite refinement before and after the
lattice construction; Stacks 09Y4 and 03S0; parent proof steps 2--3.
(blueprint: lem-sfb-qcqs-constructible-integral-leaf-models).

Proof: Apply `qcqs_constructible_integral_lattice_tree` to obtain the finite
SchemeRefinementTree whose leaves have lisse restrictions. At every nonempty leaf,
apply `qcqs_lisse_stratified_integral_lattices`, choosing E itself in the finite-field
case and the supplied finite field F in the closure case. Regard each finite locally
closed partition as a Scheme.Stratification, retaining constructibility. The lattice
inclusions induce the required scalar-extension isomorphisms; in the closure case
use the final composite in the lisse-lattice theorem, including its pullback comparison.
Refine each partition by its finite open/closed refinement tree and pull the integral
models back along its actual factoring scheme maps. Graft the
replacement trees into the original tree. Recursively forget the root immersions and
the trivial allowed predicate to produce QcqsOpenClosedTree; complementary open/closed
children, quasi-compactness and qcqs vertices are already fields of each split.
Induction on the resulting tree identifies each leaf path's toRoot with the original
composite immersion. Transport the supplied scalar isomorphisms by this equality and
pullback composition. These are precisely the fields of LatticeTree.LeafModels.
For an empty leaf use the zero integral module over E, whose scalar extension and
restriction of M are both zero on the empty site. The one-leaf tree handles empty V;
no ranks or nonempty strata are assumed. No derived complex or connecting map descends.
-/
theorem qcqs_constructible_integral_leaf_models
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V] :
    (∀ M : LatticeTree.Modules (Profinite.continuousMapRingObj E) V,
      IsConstantModelConstructible (Profinite.continuousMapRingObj E) V M →
      ∃ t : QcqsOpenClosedTree V,
        Nonempty (LatticeTree.LeafModels ℓ Unit (fun _ ↦ E)
          (Profinite.continuousMapRingObj E)
          (fun _ ↦ padicIntegersRingObjToContinuousMapRingObj ℓ E) t M)) ∧
    (∀ M : LatticeTree.Modules (Profinite.padicAlgClRingObj ℓ) V,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) V M →
      ∃ t : QcqsOpenClosedTree V,
        Nonempty (LatticeTree.LeafModels ℓ (PadicAlgCl.FiniteIntermediateField ℓ)
          (fun F ↦ F) (Profinite.padicAlgClRingObj ℓ)
          (fun F ↦ padicIntegersRingObjToContinuousMapRingObj ℓ F ≫
            Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) t M)) := by sorry

end AlgebraicGeometry.ProEtale
