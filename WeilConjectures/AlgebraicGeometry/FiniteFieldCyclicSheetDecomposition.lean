/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionWeilHeartData
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory

/-! # Finite-field cyclic sheet decomposition

Source: `literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, paragraph 5
(blueprint: lem-zl-real-scheme-cyclic-sheets).

The canonical constant-extension sheet maps are the cyclic translates of the
chosen inclusion sheet.  They are clopen, pairwise disjoint, and cover the
geometric fibre; the projection and Frobenius identities are included explicitly.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The finite-field constant-extension fibre decomposes into cyclic Frobenius sheets.

Source: `literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, paragraph 5
(blueprint: lem-zl-real-scheme-cyclic-sheets).

The hypotheses are the global finite-field datum, an integer `m ≥ 1`, and a separated
finite-type `k₀`-scheme `X₀`.  The maps are the canonical base-change projection,
the distinguished sheet induced by the inclusion of the degree-`m` subfield, the
geometric Frobenius on the constant-extension fibre, and the geometric Frobenius
on the original fibre.  The conclusion states that the cyclic translates of the
distinguished sheet are open-and-closed embeddings with pairwise disjoint ranges
covering the whole fibre, that the distinguished sheet is a section of the
projection, and that the `m`-th Frobenius iterate returns it after the corresponding
`m`-th iterate on the original fibre.  Naturality also gives the projection/Frobenius
identity.

The statement follows the five proof steps in that paragraph:

1. The finite-field Galois/Frobenius lemma identifies the `m` embeddings of the
   degree-`m` subfield with the powers of Frobenius, using
   `def-weil-finite-field-fiber`, `lem-sfb-finite-field-galois-frobenius`, and
   `def-weil-frobenius-detailed`.
2. The Galois tensor decomposition, tensor cancellation, finite-product tensor
   formula, and tensor universal property give the canonical evaluation
   isomorphism over the algebraic closure.
3. On affine charts, the fibre-product and tensor formulas identify the factors
   with copies of the original fibre; the affine coproduct and scheme-coproduct
   lemmas give clopen sheets, and compatibility on affine subopens glues them.
4. The affine Frobenius formulas give `H ≫ j_σ = j_(γ⁻¹σ) ≫ Fr_X`; induction
   identifies the cyclic maps with the prescribed `h_i`.
5. The same coordinate formulas give the projection section and naturality
   identities; the `m`-th cyclic return gives `H^m ≫ j₀ = j₀ ≫ Fr_X^m`.
-/
theorem finiteFieldCyclicSheetDecomposition :
    (∀ i : Fin m,
      IsOpenImmersion (constantExtensionCyclicSheet D m hm X₀ i) ∧
        IsClosedImmersion (constantExtensionCyclicSheet D m hm X₀ i)) ∧
    Pairwise (fun i j : Fin m ↦
      Disjoint (Set.range (constantExtensionCyclicSheet D m hm X₀ i))
        (Set.range (constantExtensionCyclicSheet D m hm X₀ j))) ∧
    (⋃ i : Fin m, Set.range (constantExtensionCyclicSheet D m hm X₀ i)) = Set.univ ∧
    constantExtensionCyclicSheet D m hm X₀ ⟨0, hm⟩ ≫
        zlFiberMap D (constantExtensionProjection D m hm X₀) = 𝟙 _ ∧
    (constantExtensionCyclicSheet D m hm X₀ ⟨0, hm⟩ ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ m).hom =
      ((D.geometricFrobenius X₀) ^ m).hom ≫
        constantExtensionCyclicSheet D m hm X₀ ⟨0, hm⟩) ∧
    (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom ≫
        zlFiberMap D (constantExtensionProjection D m hm X₀) =
      zlFiberMap D (constantExtensionProjection D m hm X₀) ≫
        (D.geometricFrobenius X₀).hom := by
  sorry

end WeilConjectures
