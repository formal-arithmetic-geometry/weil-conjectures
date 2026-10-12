/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Local noetherian approximation of a smooth morphism and its section

Source: Stacks Project, Tags 055Q, 01ZM and 0C0C.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A smooth quasi-compact quasi-separated morphism with a section admits, near any
source point, a noetherian model together with cartesian comparison squares and a
compatible restricted section. No assertion about connected components is made here.

Source: Stacks Project, Tag 055Q, first two paragraphs; Tag 01ZM, clauses (1)-(3);
and Tag 0C0C (descent of smoothness).
Proof: choose an affine open V containing g(x), and set W = g⁻¹(V). The restriction
q : W → V is smooth and finitely presented: smoothness gives local finite presentation,
and quasi-compactness and quasi-separatedness give finite presentation. Its section τ
is the restriction of σ, so τ≫W.ι = V.ι≫σ. Express the coordinate ring of V as the
filtered union of its finite-type ℤ-subalgebras. Tag 01ZM(1) descends q to a finitely
presented g₀ over one such subalgebra. Tag 01ZM(2) descends τ, and clause (3) permits
increasing the index until its section identity holds. Tag 0C0C permits another
increase so that g₀ is smooth. The affine base T₀ is noetherian because its ring is
finite type over ℤ. Finite presentation of g₀ supplies quasi-compactness and
quasi-separatedness. The base-change isomorphism supplies a and b and the second
cartesian square, with τ≫a = b≫σ₀. The first square is cartesian by the construction
W = g⁻¹(V). Every later increase of the index preserves these identities.

(blueprint: lem-sbc-smooth-section-component-noetherian-model-data) -/
theorem Smooth.exists_section_component_noetherian_model_data {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (x : P) :
    ∃ (W : P.Opens) (_ : x ∈ W) (V : T.Opens) (P₀ T₀ : Scheme.{u})
      (g₀ : P₀ ⟶ T₀) (σ₀ : T₀ ⟶ P₀) (a : W.toScheme ⟶ P₀)
      (q : W.toScheme ⟶ V.toScheme) (τ : V.toScheme ⟶ W.toScheme)
      (b : V.toScheme ⟶ T₀),
      IsNoetherian T₀ ∧ Smooth g₀ ∧ QuasiCompact g₀ ∧ QuasiSeparated g₀ ∧
      σ₀ ≫ g₀ = 𝟙 T₀ ∧ τ ≫ q = 𝟙 V.toScheme ∧
      IsPullback W.ι q g V.ι ∧ IsPullback a q g₀ b ∧
      τ ≫ W.ι = V.ι ≫ σ ∧ τ ≫ a = b ≫ σ₀ := by sorry

end AlgebraicGeometry
