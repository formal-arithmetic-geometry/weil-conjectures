/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.FieldExtensionStrictLimits

/-! # Completed scalar extension and strict derived limits

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
/-- The completed coefficient inclusion has the projection-normalized strict-limit
comparison, on all strict towers and without boundedness assumptions.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (1),
finite free tensor commutes with derived limits
(blueprint: lem-sp-field-extension-completed-strict-limit).

Proof: choose a finite integral basis for O_F over O_E, including ramified extensions.
After restriction, ordinary extension is a fixed finite sum, so it preserves limits
and is exact. The canonical limit comparison is characterized by its projections;
applying it degreewise gives chain and chain_projection. Choose a nonzero E-linear
functional on F. Multiplication identifies the F-dual with F; under this identification
Hom_O_E(O_F,O_E) is a full O_E lattice stable
under O_F. It is a finitely generated torsion-free O_F module of rank one. Since
O_F is a DVR it is free of rank one; a generator supplies a perfect O_E pairing
O_F times O_F to O_E. The induced isomorphism O_F tensor M to Hom_O_E(O_F,M)
identifies extension with coinduction, including on sheaves via the same finite
basis. Restriction is exact, so coinduction preserves K-injectives, also for strict
towers, by applying the adjunction to null homotopies from acyclic complexes. Thus the
chain comparison computes the comparison of total right derived limits on K-injective
representatives. Identify the exact derived
extension with completedDerivedScalarExtension by its K-flat counit. Localization
of the chain map gives iso, with precisely the representative equation normalized.
The auxiliary basis and dual generator prove invertibility and preservation only;
the comparison itself is the canonical projection-normalized map. -/
theorem field_extension_completed_strict_limit (P : PurityFiniteSetting.{u})
    (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u}) :
    Nonempty (StrictLimitComparison P E F h T) := by sorry

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
