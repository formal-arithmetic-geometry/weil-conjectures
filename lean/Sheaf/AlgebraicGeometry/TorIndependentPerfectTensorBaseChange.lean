/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh
import Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition
import Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction
import Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison

/-! # Tor-independent base change for a perfect tensor factor

Source: Stacks Project, perfect.tex, single-complex base change (Tags 0DJ9, 0DJA)
and the Tor-independent comparison (Tag 08IB)
(blueprint: lem-pc-tor-independent-perfect-tensor-base-change).
-/

@[expose] public section

set_option autoImplicit false
universe uPT wPT
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Tor-independent qcqs base change over affine bases for a perfect tensor factor.
The target is written as Rf'_* Lg_X^*(P ⊗ K). Under the canonical tensor-pullback
isomorphism of lem-pc-derived-pullback-tensor-product (Stacks, 079U), this is exactly
Rf'_*(Lg_X^*P ⊗ Lg_X^*K). Postcomposing the fixed base-change map with that
isomorphism does not change IsIso.
Source: Stacks, perfect.tex, Tags 08IB, 0DJA and 0DJ9
(blueprint: lem-pc-tor-independent-perfect-tensor-base-change).
Proof (the node's four steps):
1. Apply lem-pc-tor-independent-perfect-pullback-comparison to P: Tor independence
   gives the stalkwise condition for the identity of Lg_X^*P.
2. Apply lem-pc-rf-single-complex-inherited-tensor-condition, with K=P,
   K'=Lg_X^*P, the identity comparison, and E=K, to inherit the condition for the
   tensor product. The two factors can be exchanged by tensor symmetry.
3. Perfect objects have quasi-coherent cohomology (08DB). By
   lem-pc-derived-pullback-tensor-qcoh all tensor products and pullbacks concerned
   have quasi-coherent cohomology. Apply lem-pc-rf-single-complex-qcqs-induction
   to this comparison; qcqs of f gives invertibility of the base-change composite.
4. Use lem-pc-derived-pullback-tensor-product (079U) and tensor symmetry to
   identify it with the displayed map. -/
theorem torIndependent_perfect_tensor_baseChange
    [∀ Y : Scheme.{uPT},
      HasDerivedCategory.{wPT} (SheafOfModules.{uPT} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{uPT}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (g : S' ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [∀ U : X.Opens,
      HasDerivedCategory.{wPT} (SheafOfModules.{uPT} ((moduleRings X.toRingedSpace).over U))]
    (hTor : PullbackStalkTensor.IsTorIndependent f g)
    (P K : schemeDerivedCategory X) (hP : Scheme.IsPerfect X P)
    (hK : schemeDerivedQCohProperty X K) :
    IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition (P ⊗ K)) := by
  sorry

end AlgebraicGeometry
