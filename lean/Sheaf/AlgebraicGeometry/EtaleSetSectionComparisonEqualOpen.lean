/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison

/-! # The agreement open for canonical inverse-image section comparisons
Source: Stacks Project, Tag 09XM, with inverse-image unit compatibility in
Sites Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-sets-section-comparison-equal-open). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09XM, applied to the pulled-back sheaf on the
étale object `V ×[R] S`; Sites Tags 03CB and 03CC for composition of inverse images.
(blueprint: lem-weil-pbc-sets-section-comparison-equal-open).

Proof:
1. Put F = f⁻¹G and Q = V ×[R] S. Apply
   `existsUnique_etaleSections_equal_open` to `(F, Q, s, t)`, giving the unique
   agreement open U in Q with its arbitrary-map factorization criterion.
2. For h ≫ f = k put P = V ×[R] T and p = (id_V,h) : P → Q. Write q : Q → S
   and q' : P → T for the étale second projections. Inverse image along an étale
   map is restriction, hence F(Q) is canonically Γ(Q,q⁻¹F), and (h⁻¹F)(P) is
   Γ(P,q'⁻¹h⁻¹F). Under these isomorphisms, restriction along p is the unit for h
   evaluated on Q: use p ≫ q = q' ≫ h, naturality of units in the site object,
   and the composition unit equation. The latter equation sends both paths
   around this cartesian square to the unit for its outer composite. The
   canonical iterated-pullback isomorphism is specified by its projections.
   Compose with h⁻¹f⁻¹G ≅ k⁻¹G and that pullback isomorphism. The resulting
   map is exactly etaleSetSectionComparison h f k hk G V. These identifications
   are isomorphisms, so its two values agree exactly when s,t restricted along p
   agree in the agreement-open factorization criterion.
3. That criterion identifies equality with factorization of p through U. A map
   factors through an open immersion exactly when all its points lie in U,
   by the open immersion lifting property; equivalently p⁻¹U is top.
Empty domains satisfy the same equivalence. For s=t the unique open U is top.
No limiting or finiteness hypothesis is used. -/
theorem etaleSetSectionComparison_equal_open
    {R S : Scheme.{u}} (f : S ⟶ R)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (V : R.Etale)
    (s t : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))) :
    ∃ U : (pullback V.hom f).Opens,
      ∀ (T : Scheme.{u}) (h : T ⟶ S) (k : T ⟶ R) (hk : h ≫ f = k),
        etaleSetSectionComparison h f k hk G V s =
          etaleSetSectionComparison h f k hk G V t ↔
        (pullback.map V.hom k V.hom f (𝟙 V.left) h (𝟙 R)
          (by simp) (by simpa using hk.symm)) ⁻¹ᵁ U = ⊤ := by sorry

end AlgebraicGeometry
