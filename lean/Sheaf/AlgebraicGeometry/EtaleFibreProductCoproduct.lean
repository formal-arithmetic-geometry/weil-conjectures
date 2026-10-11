/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Over

/-!
# Iterated fibre products of a finite coproduct

Source: Stacks Project, Schemes, Tags 01JB and 01JC, and Section 26.17
(blueprint: lem-sc-etale-fibre-product-coproduct).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, Schemes, Tags 01JB and 01JC and Section 26.17
(blueprint: lem-sc-etale-fibre-product-coproduct).
Products in `Over X` are iterated fibre products over `X`. The canonical isomorphisms
are oriented from the coproduct of indexed fibre products to the fibre product of the
coproduct. Their component equations specify the canonical map, and the final equations
specify compatibility with every omitted-factor projection.

Proof: (1) Form the component maps from the coprojections using fibre-product universality
(`def-pc-fibre-product`), then glue using `lem-weil-pbc-scheme-coproduct-family`.
(2) For one factor the map is the identity by coproduct uniqueness.
(3) Induct on the number of factors, using
`lem-sc-etale-fibre-product-base-change-coproduct` first on the last factor and then on
the preceding factors; exchange factors and flatten the resulting coproduct of coproducts.
Fibre-product uniqueness identifies the composite with the component map from (1).
(4) After omitting a factor, the two component maps have identical projections to all
remaining factors, so fibre-product uniqueness proves their equality. -/
theorem etale_fibre_product_coproduct (X : Scheme.{u}) (I : Type v) [Finite I]
    (U : I → Scheme.{u}) (u : ∀ i : I, U i ⟶ X) :
    let A : I → Over X := fun i => Over.mk (u i)
    let V : Over X := Over.mk (Sigma.desc u)
    let P := fun (p : ℕ) (J : Fin (p + 1) → I) => ∏ᶜ fun r => A (J r)
    let Q := fun p : ℕ => ∏ᶜ fun _ : Fin (p + 1) => V
    let c : ∀ i : I, A i ⟶ V := fun i =>
      Over.homMk (Sigma.ι U i) (Sigma.ι_desc u i)
    ∃ e : ∀ p : ℕ, (∐ P p) ≅ Q p,
      (∀ (p : ℕ) (J : Fin (p + 1) → I) (r : Fin (p + 1)),
        Sigma.ι (P p) J ≫ (e p).hom ≫ Pi.π (fun _ : Fin (p + 1) => V) r =
          Pi.π (fun s : Fin (p + 1) => A (J s)) r ≫ c (J r)) ∧
      (∀ (p : ℕ) (J : Fin (p + 2) → I) (r : Fin (p + 2)),
        Sigma.ι (P (p + 1)) J ≫ (e (p + 1)).hom ≫
            Pi.lift (fun s : Fin (p + 1) =>
              Pi.π (fun _ : Fin (p + 2) => V) (r.succAbove s)) =
          Pi.lift (fun s : Fin (p + 1) =>
              Pi.π (fun t : Fin (p + 2) => A (J t)) (r.succAbove s)) ≫
            Sigma.ι (P p) (fun s => J (r.succAbove s)) ≫ (e p).hom) := by
  sorry

end AlgebraicGeometry
