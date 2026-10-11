/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Morphisms into a coproduct of copies of a scheme

Source: Stacks Project, Groupoids, Example 03YW and Schemes, Lemmas 01JB and 01HI
(blueprint: lem-galois-coproduct-copies-morphisms-clopen).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An indexed clopen decomposition consists of pairwise disjoint open subschemes whose
union is the whole scheme. Each piece is also closed, since its complement is the union
of the other pieces. Source: Stacks Project, Groupoids, Example 03YW
(blueprint: lem-galois-coproduct-copies-morphisms-clopen). -/
def IsClopenDecomposition (W : Scheme.{u}) (E : Type v) (P : E → W.Opens) : Prop :=
  (∀ e e' : E, e ≠ e' → Disjoint (P e) (P e')) ∧ (⨆ e, P e) = ⊤

open Classical in
/-- Source: Stacks Project, Groupoids, Example 03YW, and Schemes, Lemmas 01JB and 01HI
(blueprint: lem-galois-coproduct-copies-morphisms-clopen).

The coprojections are open immersions with disjoint images covering the coproduct.
Pulling their images back along a map over `U` gives disjoint open pieces covering `W`;
their complements are unions of the other pieces. On each piece the map factors through
the corresponding coprojection, and its factor is forced by the map to `U`.
Conversely, map each open piece through its coprojection and glue the maps. The empty
overlaps make gluing automatic, while the open cover makes the glued map unique and
forces its component preimages. A decomposition is equivalently a locally constant
function to the discrete index type. The constant and empty-index cases follow from
these constructions. -/
theorem coproductCopiesMorphismsClopen (U W : Scheme.{u}) (E : Type v) [Small.{u} E]
    (s : W ⟶ U) :
    ((∀ f : W ⟶ ∐ fun _ : E => U,
      f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s →
        IsClopenDecomposition W E
          (fun e => f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange) ∧
        ∀ e : E,
          (f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange).ι ≫ f =
            ((f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange).ι ≫ s) ≫
              Sigma.ι (fun _ : E => U) e)) ∧
    (∀ P : E → W.Opens, IsClopenDecomposition W E P →
      ∃! f : W ⟶ ∐ fun _ : E => U,
        f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s ∧
          ∀ e : E, f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange = P e) ∧
    (∃ b : {f : W ⟶ ∐ fun _ : E => U //
          f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s} ≃
          {P : E → W.Opens // IsClopenDecomposition W E P},
      ∀ f e, (b f).1 e = f.1 ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange) ∧
    (∃ b : {f : W ⟶ ∐ fun _ : E => U //
          f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s} ≃ LocallyConstant W E,
      ∀ f e, ((f.1 ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange) : Set W) =
        {x : W | b f x = e}) ∧
    ((∀ e₀ : E, ∀ e : E,
      ((s ≫ Sigma.ι (fun _ : E => U) e₀) ⁻¹ᵁ
        (Sigma.ι (fun _ : E => U) e).opensRange) =
          if e = e₀ then ⊤ else ⊥)) ∧
    (IsEmpty E →
      IsEmpty (∐ fun _ : E => U : Scheme.{u}) ∧
      ((∃ f : W ⟶ ∐ fun _ : E => U,
          f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s) ↔ IsEmpty W)) := by
  sorry

end AlgebraicGeometry
