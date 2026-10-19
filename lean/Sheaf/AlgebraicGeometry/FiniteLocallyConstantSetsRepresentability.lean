/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsLocalModels
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsDescent

/-! # Representability of finite locally constant sheaves of sets

Source: Stacks Project, Tag 03RV, implication (1) to (2).
(blueprint: lem-weil-pbc-finite-locally-constant-sets-representability)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Descent constructs a finite étale scheme representing a locally constant sheaf
of sets with finite geometric stalks.

Source: Stacks Project, Tag 03RV, implication (1) to (2).
(blueprint: lem-weil-pbc-finite-locally-constant-sets-representability)

Proof: Choose an étale cover trivializing E. On a nonempty member U, any geometric
point identifies the stalk of a constant local model with its value, so the value is
finite by IsFiniteSheaf. Empty members can be discarded. Each finite constant model
is represented by the disjoint union of finitely many copies of U. On overlaps, the
isomorphisms between these local models give unique isomorphisms of their representing
schemes by Yoneda. Their cocycle follows by Yoneda faithfulness from the cocycle of
restriction of E. Effective étale descent for affine schemes descends these finite
étale schemes to a scheme P over T; finiteness and étaleness descend along the cover.
The local representing isomorphisms agree by construction and glue to an isomorphism
of E with the sheaf of sections of P. On the empty base, use P empty. No uniform bound
on the ranks and no quasi-compactness of T is required. -/
theorem finiteLocallyConstant_sets_representable
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hloc : ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)))
    (hfin : IsFiniteSheaf E) :
    ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : Etale π),
      Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Etale.mk π)) := by
  obtain ⟨hlocal, hmodels⟩ := finiteLocallyConstant_exists_local_models T E hloc hfin
  exact finiteLocallyConstant_descent_of_local_models T E ⟨hlocal, hmodels⟩

end AlgebraicGeometry.Scheme
