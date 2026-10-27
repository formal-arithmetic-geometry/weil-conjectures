/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U6
-/
module

public import Sheaf.Paper.EtaleSystemCofinalData

/-! # Selected extension on the actual étale sequence site

Source: Zheng, Construction 4.1; Stacks 06YS and 06YT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The local selected extension, including its ordinary unit and derived representative
normalization, exists on the actual sequence-site category.
Source: Zheng, Construction 4.1, printed p. 21; Stacks 06YS and 06YT
(blueprint: lem-pur-etale-cofinal-extension-existence).

Proof: identify sequence-site modules with strict systems by the identity on every
section and restriction, using strictSystemSequenceEquivalence. Transport the ordinary
selected tensor extension and its adjunction across this equivalence. At m it is tensor
extension from r(t(m)) applied to the component at t(m). The tensor-adjunction formula
systemSelectedTranspose gives the recorded ordinaryLevel_unit, including t(r(i))=i.
Resolve on the ringed sequence site by a K-flat complex with flat terms. Exact evaluation
preserves these resolving complexes by systemSequenceEvaluation_preservesKFlat. The
selected extension preserves quasi-isomorphisms between them, by componentwise scalar
extension, so its normalized total left derived functor is adjoint to the exact
localization of the actual sectionwise restriction. Transport the selected extension
from systemLevelLeftExtensionTheory and use adjoint uniqueness with the ordinary unit
normalization to identify its ordinary functor. Evaluation of this normalized derivation
is the derived tensor formula; the universal cochain comparison gives level_normalization.
For a K-flat complex without flat terms, resolve it again by such a flat-term complex.
Its acyclic K-flat cone stays acyclic after scalar extension, so comparison with that
resolution gives the same computation and representative normalization. These comparisons
supply every field of CofinalExtension; no compact-support functor is involved. -/
theorem etaleCofinalExtension_nonempty (W : Scheme.{u}) {l : ℕ}
    (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) :
    Nonempty (CofinalExtension W B r) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
