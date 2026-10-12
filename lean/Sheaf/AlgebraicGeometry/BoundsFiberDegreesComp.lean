/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.FiberDegreeBound
import Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints
import Sheaf.RingTheory.NakayamaNilpotent

/-!
# Fibre degree bounds under composition

Source: Stacks Project, Morphisms, Lemma Tag 03J6
(blueprint: lem-weil-pbc-composition-fibre-degree-bound).

## Main statements

* `AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_comp`: fibre degree bounds multiply.
* `AlgebraicGeometry.Scheme.Hom.hasUniversallyBoundedFibers_comp`: uniform bounds compose.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- Fibre degree bounds multiply under composition (Stacks Project, Morphisms, Tag 03J6).
(blueprint: lem-weil-pbc-composition-fibre-degree-bound)

Proof, following the seven steps of the node:
1. Fix `z : Z` and write `k = κ(z)`. The fibre `Y_z` is finite over `k`, hence affine
   with finite-dimensional global sections `B` of dimension at most `m`
   (`lem-weil-pbc-finite-over-field-affine-finite-dim`). Its spectrum is finite discrete
   (`lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`). Decompose `B` into its
   localizations `B_i` at maximal ideals (`lem-weil-pbc-product-of-localizations-at-maximal`).
   Each factor is Artinian (`lem-weil-pbc-finite-dim-algebra-artinian`), with nilpotent
   maximal ideal (`lem-weil-pbc-artinian-local-noetherian-nilpotent`), and residue field `K_i`.
2. Cartesian-square pasting (`lem-weil-pbc-cartesian-square-pasting`) identifies
   `X_z` with `X ×_Y Y_z`, and its fibres over the points of `Y_z` with
   `X ×_Y Spec K_i`. These are finite over `K_i`, with degree at most `n`
   (`lem-weil-pbc-fibre-degree-bound-field-points`), hence have finite discrete spectra.
3. The underlying space of `X_z` is a finite union of these finite fibres; every point
   is closed, since the corresponding point of `Y_z` is closed. Thus `X_z` is finite
   discrete, hence affine (`lem-weil-pbc-finite-discrete-scheme-affine`). Put
   `A = Γ(X_z, O)`; the morphisms yield `k → B → A`
   (`lem-weil-pbc-morphism-into-affine-scheme`).
4. Affine fibre products (`lem-weil-pbc-fibre-product-affine-spectra`) identify the
   fibre over the maximal ideal `n_i` with `Spec (A/n_i A)`, so its dimension over
   `K_i` is at most `n`.
5. Tensor the finite product decomposition of `B` with `A` to obtain the decomposition
   into `A_i = A ⊗_B B_i`; dimensions over `k` add across this finite product.
6. Lift a `K_i`-basis of `A_i/n_i A_i`, of size `d_i ≤ n`, to `A_i`. Nilpotent Nakayama
   (`lem-weil-pbc-nakayama-nilpotent`) makes the resulting map `B_i^{d_i} → A_i`
   surjective. Consequently `dim_k A_i ≤ n * dim_k B_i`.
7. Sum these inequalities to get `dim_k A ≤ n * dim_k B ≤ n * m`. Thus `A` is finite
   over `k`, and `X_z → Spec k` is finite (`lem-weil-pbc-finite-local-on-target`).
   This proves both clauses of `BoundsFiberDegrees (f ≫ g) (n * m)` for every `z`. -/
theorem boundsFiberDegrees_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n m : ℕ) (hf : BoundsFiberDegrees f n) (hg : BoundsFiberDegrees g m) :
    BoundsFiberDegrees (f ≫ g) (n * m) := by
  sorry

/-- A composition of morphisms with universally bounded fibres has universally bounded
fibres (Stacks Project, Morphisms, Tag 03J6).
(blueprint: lem-weil-pbc-composition-fibre-degree-bound)

Proof: choose bounds `n` and `m` from `hf` and `hg`, respectively. The preceding
`boundsFiberDegrees_comp` gives the bound `n * m` for `f ≫ g`, which witnesses the
existential defining `HasUniversallyBoundedFibers`. This is the last clause of step 7. -/
theorem hasUniversallyBoundedFibers_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasUniversallyBoundedFibers f) (hg : HasUniversallyBoundedFibers g) :
    HasUniversallyBoundedFibers (f ≫ g) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
