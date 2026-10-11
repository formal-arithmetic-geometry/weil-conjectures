/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.AlgebraicGeometry.StrictHenselization

/-!
# Base change and the neighbourhood limit

Source: Weil conjectures blueprint, `sec-curve-estimates/sk-prop-h2`,
lemma `lemma-weil-pbc-fibre-product-limit`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Base change commutes with the inverse limit over the affine pointed etale
neighbourhoods `(V, v)` of a geometric point `s` of `S`: for a quasi-compact and
quasi-separated `f : X ⟶ S`, the strict henselization `S_(s)` carries a cone over the
neighbourhood diagram in `Over S` whose legs are those of `strictHenselizationCone s`
(after `Spec Γ(Spec R, ⊤) ≅ Spec R`), and its base change along `f` is a limit cone of
the base changes `V ×_S X`. The vertex of the base-changed cone is `S_(s) ×_S X`.

Source: Weil conjectures blueprint, `sec-curve-estimates/sk-prop-h2`, lemma
`lemma-weil-pbc-fibre-product-limit` (blueprint: lemma-weil-pbc-fibre-product-limit).
Proof: `strictHenselization_properties` makes the strict henselization cone limiting;
the structure map to `S` is a leg composed with the structure map of the neighbourhood.
A compatible cone of maps `T ⟶ V ×_S X` gives a cone into the neighbourhoods, hence one map
`T ⟶ S_(s)`, and maps to `X` that agree by cofilteredness; the fibre-product universal
property gives the unique factorization.
-/
theorem fibre_product_neighbourhood_limit
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {X : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    ∃ c : Cone ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
        CategoryOfElements.π _ ⋙ Scheme.AffineEtale.Spec S ⋙ Scheme.Etale.forget S),
      c.pt.left = Scheme.strictHenselizationScheme s ∧
      (∀ k : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
        HEq (c.π.app k).left ((Scheme.strictHenselizationCone s).π.app (op (op k)) ≫
          Spec.map (Scheme.ΓSpecIso
            ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              k).1.left.unop).inv)) ∧
      Nonempty (IsLimit ((Over.pullback f ⋙ Over.forget X).mapCone c)) := by
  sorry

end AlgebraicGeometry
