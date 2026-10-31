/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # An affine-space cell in a Borel quotient

Source: Milne, Algebraic Groups (2017), Lemma 18.21, proof, printed p.392;
Proposition 13.52, printed p.275, and the proof of Theorem 17.65, printed p.374.
(blueprint: lem-sfb-borel-quotient-affine-space-cell)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A represented fppf quotient of a smooth connected affine group by a Borel subgroup
contains a dense open affine space, including the zero-dimensional case.
The coequalizer is the presheaf of right cosets, and `hQ`, `ηQ`, `hηQ` say exactly
that its fppf sheafification is represented by `Q`. Tests range over schemes over F;
restriction to affine tests gives the equivalent algebra formulation in the node.
No reductivity hypothesis is used.

Source: Milne, Lemma 18.21, proof, printed p.392; Proposition 13.52, printed p.275,
and the proof of Theorem 17.65, printed p.374.
(blueprint: lem-sfb-borel-quotient-affine-space-cell)

Proof plan:
1. Apply lem-sfb-borel-quotient-affine-cell with precisely these field, group, Borel
   and quotient hypotheses. It gives a dense open U in Q and an F-isomorphism
   U ≅ Spec F[t₁,...,tₙ], without requiring reductivity.
2. Set d = n. By def-sbc-affine-space identify affine d-space over Spec F with
   this polynomial spectrum. Compose the identification with the inverse chart
   and U → Q. By def-weil-open-immersion the result is an open immersion;
   its image is U and hence its topological image is dense in Q.
3. If G = B, the coset presheaf and its sheafification are terminal. Therefore Q
   is F-isomorphic to Spec F. The canonical identification of affine 0-space with
   Spec F gives the required open immersion with image all of Q. -/
theorem exists_borelQuotient_affineSpace_denseOpen
    {F : Type u} [Field F] [IsAlgClosed F]
    (G B : Over (Spec (.of F))) [GrpObj G] [GrpObj B]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : B ⟶ G) (hB : IsBorelGroupScheme i)
    (Q : Over (Spec (.of F)))
    (hQ : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q))
    (ηQ : coequalizer (yoneda.map (fst G B))
      (yoneda.map (lift (fst G B) (snd G B ≫ i) ≫ μ[G])) ⟶ yoneda.obj Q)
    (hηQ : ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηQ ≫ f)) :
    ∃ (d : ℕ)
      (j : (AffineSpace (ULift.{u} (Fin d)) (Spec (.of F))).asOver (Spec (.of F)) ⟶ Q),
      IsOpenImmersion j.left ∧ DenseRange j.left := by
  sorry

end AlgebraicGeometry
