/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Abelian étale pullback along an isomorphism of absolute Galois groups

Source: Stacks Project, Tags 03QW and 04JQ; the Galois-action argument in
ILO, Travaux de Gabber, XX 4.4, printed p.374.
-/

@[expose] public section

set_option autoImplicit false

universe u s t

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- If restriction is an isomorphism of absolute Galois groups, the actual inverse
image functor on abelian étale sheaves is an equivalence. This assertion has no
valuation or torsion hypotheses and makes no assertion about cohomology.
Source: Stacks Project, Tags 03QW and 04JQ; ILO, XX 4.4, printed p.374,
the Galois-action comparison (blueprint: lem-per-galois-restriction-etale-equivalence).

Proof: First replace the chosen separable closures by isomorphic separable
closures in the universe of K and L. Such closures exist and their algebraic
embeddings into the given closures are surjective by uniqueness of separable
closures. Conjugation transports the Krull topology: pointwise stabilizers of
finite subextensions pull back to pointwise stabilizers of their images. Thus
the given isomorphism and its restriction formula transport to these closures.
Choose an algebraic closure Omega of the new Ls and compose the embeddings into
it. Apply lem-exc-abelian-sheaves-gmodules to K and L with this common field.
Use the normalized stalk-action clauses of these equivalences in
lem-per-field-pullback-galois-action. Its natural comparison identifies the actual
upperStar functor, followed by the L equivalence, with the K equivalence followed
by restriction along e. Restriction along a topological group isomorphism is an
equivalence of discrete continuous integral representations: its inverse acts
by e.symm on the same modules and maps, with the unit and counit identity maps.
Open stabilizers are preserved because e and its inverse are continuous; the
action identities follow from the two inverse identities. The composite on the
representation side is therefore an equivalence. Transport across the natural
comparison and cancel the L equivalence to see that upperStar is an equivalence.
This identifies the existing functor itself, so the constant-sheaf comparison
used in cohomology remains the existing canonical comparison. -/
theorem upperStar_isEquivalence_of_galoisRestriction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (Ks : Type s) (Ls : Type t) [Field Ks] [Field Ls]
    [Algebra K Ks] [IsSepClosure K Ks]
    [Algebra L Ls] [IsSepClosure L Ls]
    [Algebra Ks Ls] [Algebra K Ls]
    [IsScalarTower K Ks Ls] [IsScalarTower K L Ls]
    (e : Gal(Ls/L) ≃ₜ* Gal(Ks/K))
    (he : ∀ (σ : Gal(Ls/L)) (x : Ks),
      algebraMap Ks Ls (e σ x) = σ (algebraMap Ks Ls x)) :
    (upperStar AddCommGrpCat.{u + 1}
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).IsEquivalence := by sorry

end AlgebraicGeometry.Etale
