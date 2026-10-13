/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
import Sheaf.Paper.ModuleCupGodementPairing
import Sheaf.Paper.ModuleCupFlasqueAcyclicity
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-! # Existence of a computing tensor-paired resolution

Source: Stacks Project, Cohomology of Sheaves, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-pairing-exists)
-/

@[expose] public section

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Module sheaves admit computing resolutions with a sectionwise tensor pairing.
Source: Stacks Project, Section 20.31 (0FKU), naive cup product and the
flasque/Godement proof of Lemma 20.31.4 (0FKV).
(blueprint: lem-sc-module-cup-pairing-exists)
Proof: take the existential strictly nonnegative flasque integer complexes,
quasi-isomorphic augmentations and tensor cochain map supplied by
moduleCup_godement_pairing. Restrict to natural degrees. On each tensor summand,
tensor sections and apply the supplied chain map; its cochain identity gives
signed Leibniz, and its degree-zero formula gives augmentation_pair. Restrictions
commute because its components are sheaf morphisms. Choose injective resolutions
and extend each augmentation to a comparison degree by degree by injectivity.
moduleCup_flasque_acyclicity makes the supplied terms acyclic, and the separately
cited Leray acyclic-resolution comparison criterion makes every global comparison
homology map invertible. Assemble the fields of CupResolutionPairing.
No specific Godement model or natural choice of the existential complexes is
assumed, and no coefficient flatness is required. -/
theorem exists_moduleCupResolutionPairing {X : Scheme.{uM}} (F G : X.Modules) :
    Nonempty (CupResolutionPairing F G) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
