/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization

/-! # Literal telescope models for a countable coproduct

Source: steps 1--2 of lem-sc-flat-telescope-sum-comparison-is-iso, expanding
Stacks Tags 06YS and 06YJ. (blueprint: lem-sc-flat-telescope-sum-models).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A sum of individually bounded flat complexes admits a literal telescope model
and a coproduct cofan whose summands are bounded literal telescope models.

Source: steps 1--2 of lem-sc-flat-telescope-sum-comparison-is-iso, expanding
Stacks Tags 06YS and 06YJ.

Proof. Put B_n = E_0 + ... + E_n, with the split inclusion into B_(n+1),
and let R be the mapping cone of one minus transition on the coproduct of B_n.
Each B_n has flat terms and is bounded by the finite maximum of its stage bounds.
Reindex the double coproduct by pairs (n,j) with j <= n. For each j its contribution
is the constant identity tower on E_j, starting at n=j. The augmentation sums the
coordinates, and the section inserts into the first coordinate. One minus successor
identifies the direct sum with the augmentation kernel: the inverse sends a
zero-sum finite sequence to its finite partial sums. Its tail vanishes precisely
because the input sums to zero. These operations commute with differentials.
Equivalently, on the n-th tail coordinate define the retraction of one minus
successor by minus the sum of the preceding coordinate inclusions. This sum is
finite on each input summand, so the coproduct universal property defines a
cochain map without any choice of lifts. The retraction identities telescope:
delta followed by retraction is identity; retraction followed by delta plus
augmentation followed by section is identity. The split cone is therefore E_j
plus a contractible identity cone. Sum these
splittings to obtain q(sum E) isomorphic to qR.
For each j let T_j be the same identity-tower cone on E_j. Its terms are sums of
flat terms and it is bounded above by the bound of E_j increased by one.
The same splitting gives qT_j isomorphic to qE_j. Compose its augmentation,
the j-th coprojection and the inverse augmentation of R to obtain the cofan legs.
The homotopy quotient preserves this coproduct: degreewise coproducts assemble
both chain maps and homotopies, so restriction to the summands gives a bijection
on homotopy classes into every target. Transport that universal property along
the displayed homotopy isomorphisms. This also proves the assertion for zero
complexes and the empty scheme; no uniform bound on j is used.
(blueprint: lem-sc-flat-telescope-sum-models). -/
theorem exists_flat_telescope_sum_models (Y : Scheme.{u})
    (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) :
    ∃ (R : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hR : isFlatTelescope Y R)
      (T : ℕ → CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hT : ∀ n, isFlatTelescope Y (T n))
      (s : ∀ n, (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (T n) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R),
      Nonempty ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E) ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) ∧
      (∀ n, boundedFlatShiftRepresentative Y
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (T n))) ∧
      Nonempty (IsColimit (Cofan.mk
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) s)) := by sorry

end AlgebraicGeometry
