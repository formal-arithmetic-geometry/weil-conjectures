/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.AlgebraicGeometry.RigidifiedQuotientTowerComparison
public import Sheaf.AlgebraicGeometry.CharacteristicZeroLogResolutionIndependence
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Limits

import Sheaf.AlgebraicGeometry.SimultaneousCohenRigidificationLift
import Sheaf.AlgebraicGeometry.LogBlowupNormalization

/-! # Complete-local independence of rigidification

Source: ILO, Travaux de Gabber, VIII Lemma 5.5.2 and proof, pp.127--128;
Theorem 3.4.15, pp.113--114
(blueprint: lem-per-complete-local-rigidification-comparison).

The two rigidified pairs have the same underlying scheme, action and original
boundary. Their enlarged boundaries and divisorial log structures may differ.
Equality of the resulting centered towers means a synchronized scheme isomorphism
over this same scheme, preserving every arrow and actual ideal, with no contraction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
namespace RigidifiedQuotient.Construction

/-- Equality of the underlying centered towers of two rigidified constructions.
The order equivalences are bijections of the complete index sets, including both
endpoints. The base equation fixes the isomorphism over the original scheme;
`centers` equates ideal sheaves, not merely their supports or radicals.
This witness only unpacks the equality asserted by Lemma 5.5.2.
Source: ILO VIII 5.5.2, pp.127--128 and 2.2.3--2.2.5
(blueprint: lem-per-complete-local-rigidification-comparison). -/
structure UnderlyingIso {P : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u}}
    {G : Type v} [Group G] [Finite G] {X Y : RigidifiedQuotient.Pair.{u, v} G}
    (A : RigidifiedQuotient.Construction P X) (B : RigidifiedQuotient.Construction P Y)
    (φ : X.logScheme.scheme ≅ Y.logScheme.scheme) where
  index : Fin (A.tower.tower.length + 1) ≃o Fin (B.tower.tower.length + 1)
  stage : Fin A.tower.tower.length ≃o Fin B.tower.tower.length
  first : index 0 = 0
  before : ∀ i, index i.castSucc = (stage i).castSucc
  after : ∀ i, index i.succ = (stage i).succ
  iso : ∀ i, (A.tower.tower.level i).scheme ≅ (B.tower.tower.level (index i)).scheme
  base : (iso 0).hom ≫
      eqToHom (congrArg (fun i ↦ (B.tower.tower.level i).scheme) first) ≫
      eqToHom (congrArg FineSaturatedLogScheme.scheme B.tower.initial) =
    eqToHom (congrArg FineSaturatedLogScheme.scheme A.tower.initial) ≫ φ.hom
  arrows : ∀ i,
    (A.tower.tower.arrow i).base ≫ (iso i.castSucc).hom ≫
        eqToHom (congrArg (fun j ↦ (B.tower.tower.level j).scheme) (before i)) =
      (iso i.succ).hom ≫
        eqToHom (congrArg (fun j ↦ (B.tower.tower.level j).scheme) (after i)) ≫
        (B.tower.tower.arrow (stage i)).base
  centers : ∀ i, A.center i = (B.center (stage i)).comap
    ((iso i.castSucc).hom ≫
      eqToHom (congrArg (fun j ↦ (B.tower.tower.level j).scheme) (before i)))

end RigidifiedQuotient.Construction

/-- The two very-tame rigidifications give the same full ordered normalized tower
on a finite disjoint union of complete strictly local regular schemes. The action
may permute components. No componentwise contraction is made, and the empty union
is allowed. `sameScheme`, `sameAction` and `sameBoundary` identify the underlying
pair while allowing the enlarged boundary and its log structure to vary.

Source: ILO VIII Lemma 5.5.2 and proof, pp.127--128; the fixed rule is induced by
one regular-functorial characteristic-zero algorithm as in Theorem 3.4.15
(blueprint: lem-per-complete-local-rigidification-comparison).

Proof, following the four steps of the DAG node:
1. Apply lem-per-simultaneous-cohen-rigidification-lift to both boundaries together.
It gives X <- U -> Y, strict and inert for both rigidifications, where U -> X is a
surjective finite union of component isomorphisms. The ambient scheme and its one
underlying quotient Q are finite disjoint unions of integral affine schemes. The
quotient log structures are fs log regular and their generic stratum points have
characteristic zero. The construction treats all permuted components together.
2. Apply lem-per-characteristic-zero-log-resolution-independence on Q, using the
identity of its underlying scheme and the SAME characteristic-zero algorithm F.
The resulting quotient towers agree with their full ordered center ideals. There
is no finite-type or quasi-excellence assumption on Q.
3. Pull both quotient log towers back to Y. By def-trf-fs-log-blowup, fs base change
is the log blowup of the pulled-back log ideal. At each integral component apply
lem-trf-log-blowup-normalization. If the quotient log center is I and its generated
ring ideal is J, compatibility of structural maps makes the pulled-back ring ideal
exactly J O_Y. Induction from the common map Y -> Q identifies all normalized
blowup stages, arrows and ordered ideals, despite the different log structures.
4. Apply lem-per-rigidified-quotient-tower-comparison to U -> Y for each boundary.
Their contractions on U agree because the pulled-back center ideals agree. Apply
it also to U -> X. No global center on X is a unit: quotient centers have nonempty
zero loci, and the stage maps from X to the quotient are surjective. Indeed these
maps are universally closed (finite quotient and normalized blowups), and their
images contain the dense complement of the exceptional locus. The surjective
split-copy cover U -> X consequently loses no stage. On each component of X choose
one isomorphic copy in U; equality there descends equality of each center ideal.
Induction with this ONE common indexing yields the displayed synchronized
isomorphism. On the empty scheme both proper-center towers have length zero. -/
theorem completeLocal_rigidification_comparison
    (F : RegularFunctorialNormalizedResolution.{u}) (D : InducedNormalizedLogResolution F)
    (P : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u})
    (hP : RigidifiedQuotient.IsFanInduced D.fanRule P)
    (G : Type v) [Group G] [Finite G]
    (m : ℕ) (A : Fin m → Type u) [∀ i, CommRing (A i)]
    [∀ i, IsRegularLocalRing (A i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i)]
    [∀ i, IsSepClosed (IsLocalRing.ResidueField (A i))]
    (X Y : RigidifiedQuotient.Pair.{u, v} G)
    (components : X.logScheme.scheme ≅ ∐ fun i ↦ Spec (.of (A i)))
    (sameScheme : X.logScheme.scheme = Y.logScheme.scheme)
    (sameAction : HEq X.action.baseAction Y.action.baseAction)
    (sameBoundary : HEq X.boundary Y.boundary)
    (C₁ : RigidifiedQuotient.Construction P X) (C₂ : RigidifiedQuotient.Construction P Y) :
    Nonempty (RigidifiedQuotient.Construction.UnderlyingIso C₁ C₂ (eqToIso sameScheme)) := by
  sorry

end AlgebraicGeometry
