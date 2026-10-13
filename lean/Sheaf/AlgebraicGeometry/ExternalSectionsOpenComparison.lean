/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.ExternalSectionsComponents

/-! # External section components on open subschemes

Source: Stacks Project, Tag 0BED, omitted degree-zero canonical-cup verification;
Tags 0096, 0097 and 01CD.
(blueprint: lem-sc-external-sections-open-comparison).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The explicit external section component agrees with the external product on X times V.
Source: Stacks Project, Tag 0BED, degree-zero cup product and omitted canonical-map
verification; Tags 0096, 0097 and 01CD.
(blueprint: lem-sc-external-sections-open-comparison).

Proof: Let j : X times V -> X times Y be the base change of V -> Y. It is an
open immersion with image pr_2 inverse-image V. The section isomorphism for restriction
along V -> Y identifies G(V) with the global sections of G restricted to V; its scalar
action is unchanged because both structure maps to Spec(k) are composites with g.
Tensoring this isomorphism with Gamma(X,F) gives eS. Restriction of the external
coefficient to the image of j identifies its sections with global sections of its
restriction along j. Compare restriction with tensor pullback by the unique isomorphism
of the two left adjoints to j_*, normalized by the adjunction-unit equation. Apply the
module-pullback-tensor comparison, then the pullback-composition comparisons for
j followed by the two projections. The first composite is the projection to X;
the second is the projection to V followed by V -> Y. Finally identify the pullback
of G along V -> Y with its restriction by the same normalized open-immersion
comparison. These isomorphisms of coefficients and sections give eT, and are linear
over k by compatibility of their structure maps. On a pure tensor s tensor t the
unit equations send the restricted pr_1 pullback of s to its pullback on X times V,
and send the pr_2 pullback of t to the pullback of its restricted section on V.
The tensor comparison sends the tensor section to the tensor of these images.
Thus the displayed equality holds on pure tensors, and tensor induction proves it
on all tensors. For V empty, restriction and all these adjunction comparisons are
still isomorphisms, so the same proof applies without a nonemptiness assumption.
-/
theorem externalSectionsComponent_openComparison
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens) :
    ∃ eS : ModuleCat.of k (scalarObj f F (op ⊤) ⊗[k] scalarObj g G (op V)) ≅
        ModuleCat.of k (scalarObj f F (op ⊤) ⊗[k]
          scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤)),
    ∃ eT : scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (op (pullback.snd f g ⁻¹ᵁ V)) ≅
        scalarObj (pullback.fst f (V.ι ≫ g) ≫ f)
          (externalCupCoefficients f (V.ι ≫ g) F (G.restrict V.ι)) (op ⊤),
      externalSectionsComponent f g F G V ≫ eT.hom = eS.hom ≫
        ModuleCat.ofHom
          (externalGlobalSectionsTensor f (V.ι ≫ g) F (G.restrict V.ι)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
