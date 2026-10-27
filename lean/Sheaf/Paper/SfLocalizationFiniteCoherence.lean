/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.SfLocalizationData
public import Sheaf.Paper.ExceptionalCommonStageDescent

/-! # Finite coefficient coherence for supported localization

Source: supported localization proof, coefficient-extension coherence in step 12.
(blueprint: lem-sf-supported-localization-finite-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open ExceptionalCommonStage
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- The supplied rational supported localizations give the finite input to exceptional
common-stage descent, with precisely their functors and adjunctions.
Source: current blueprint, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, step 12 and the Vanishing paragraph
(blueprint: lem-sf-supported-localization-finite-coherence).

Proof: use the given closed/open pullback equalities to choose their canonical exact
shift structures. Identify the ordinary right adjoints with the rationalized completed
images via the given image normalizations and the integral ordinary-image comparisons.
Finite free scalar extension commutes with those ordinary images by the projection
mate, and with the pullbacks by the tensor comparison. Conjugate these comparisons
by the normalizations. Their identity, tower and shift equations follow from tensor
associativity and the coefficient unit; the mate equations identify both adjunction
maps. Give each right adjoint the shift induced by its specified adjunction. Exactness
of adjoints gives all five exactness clauses. Closed and open restriction counits are
invertible because the immersions are fully faithful on direct image. Disjointness
makes closed-to-open Hom groups zero for arbitrary inputs and shifts, using the open
adjunction. The supplied supported triangle is already distinguished with the specified
counit and unit. These constructions give Hypotheses and GeometricNormalization.
They retain the given five functors and three adjunctions literally; only shift and
coefficient comparison data have been added. This is entirely a finite-stage assertion,
with no descended functor, common-stage Hom action or common-stage adjunction asserted.
-/
theorem sfSupportedLocalization_finite_coherence
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (S : ∀ E : Index l Ω, SfRationalLocalization l (Coefficient.{u} l Ω E)
      k hl t i j) :
    ∃ D : FiniteData l Ω X Z U, Hypotheses D ∧ GeometricNormalization i j D ∧
      ∀ E : Index l Ω,
        D.closedPull.Φ E = (S E).supported.iPull ∧
        D.openPull.Φ E = (S E).supported.jPull ∧
        D.closedPush.Φ E = (S E).supported.iPush ∧
        D.openPush.Φ E = (S E).supported.jPush ∧
        D.exceptional E = (S E).supported.exceptional ∧
        HEq (D.closedAdj E) (S E).supported.closedAdjunction ∧
        HEq (D.openAdj E) (S E).supported.openAdjunction ∧
        HEq (D.exceptionalAdj E) (S E).supported.exceptionalAdjunction := by sorry

end WeilConjectures
