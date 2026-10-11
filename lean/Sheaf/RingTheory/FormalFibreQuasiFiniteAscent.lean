/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.GRing
public import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Geometric regularity ascends along quasi-finite maps

Source: Stacks Project, More on Algebra, Lemma 07PP (blueprint:
lem-weil-pbc-formal-fibre-quasi-finite-ascent).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Geometric regularity of a formal fibre ascends along a map quasi-finite at the prime.
Source: Stacks Project, More on Algebra, Lemma 07PP, item (1)
(blueprint: lem-weil-pbc-formal-fibre-quasi-finite-ascent).
The fibre rings use Mathlib's residue-field-first tensor order, canonically isomorphic
as residue-field algebras to the completion-first order in the source.

Proof plan, following the six steps of the node:
1. Completion-at-quasi-finite-prime splits completion(R_p) ⊗[R] R' as
   completion(R'_(p')) × B, compatibly with the natural R'-algebra structures.
2. Tensor this splitting over R' with κ(q'); tensor products commute with finite
   products, so the target formal fibre F is a factor of the resulting algebra.
3. Since q is the contraction of q', localization-at-prime induces κ(q) → κ(q').
   Tensor-cancel-base-change, twice, identifies the resulting algebra with
   C = κ(q') ⊗[κ(q)] (κ(q) ⊗[R] completion(R_p)).
4. The images of finitely many R-algebra generators of R' generate κ(q') as a
   field extension of κ(q), so this extension is finitely generated.
5. For κ(q') itself or any finite purely inseparable extension L/κ(q'), L/κ(q)
   is finitely generated. Geometrically-regular-finitely-generated-extensions
   shows L ⊗[κ(q')] C is Noetherian and regular. Thus C is geometrically regular.
6. Tensor the splitting C ≅ F × B' with each such L. Projection to L ⊗[κ(q')] F
   is localization at the idempotent (1,0); localization-of-regular-ring makes
   this factor regular. Taking L = κ(q') gives Noetherianity of F. Thus F is
   geometrically regular over κ(q'), as required.
-/
theorem isRegular_formalFiber_of_isQuasiFiniteAtPrime
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing R']
    [Algebra R R'] [Algebra.FiniteType R R']
    (q' p' : Ideal R') [q'.IsPrime] [p'.IsPrime] (hqp : q' ≤ p')
    (hq : Algebra.IsQuasiFiniteAtPrime R R' ⟨p', inferInstance⟩)
    :
    let q := q'.comap (algebraMap R R')
    let p := p'.comap (algebraMap R R')
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)
    let C' := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
      (Localization.AtPrime p')
    Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) →
      Algebra.IsGeometricallyRegular q'.ResidueField (q'.Fiber C') := by
  sorry

end RingHom
