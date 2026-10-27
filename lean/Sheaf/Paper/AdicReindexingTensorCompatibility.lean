/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Tensor compatibility of a normalized realization comparison

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9. The normalization calculation below is an
agent-written refinement of these comparison results.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- The tensor equation for one fixed scheme-isomorphism comparison.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-tensor-compatibility).

Proof: Enlarge the two finite coefficient fields of M and N to their compositum.
Choose integral constructible representatives there, then flat-term K-flat models.
Substitute integralRealizationAgreement for the comparison and integral_tensor and
representative from the two finite normalizations for the realization tensorators.
The reindexing representative equation identifies its derived tensorator with its
cochain tensorator. On homogeneous pure sections, balance_sections and pure identify
both composites with multiplication of the two scalar factors followed by the same
total-tensor generator. The cochain pullback tensor comparison respects the signed
sum differential and every quotient transition, so these section equations give an
equality of chain maps. The quotient-completion comparison has the prescribed quotient
map as its product coordinate and zero shifted coordinate; hence the equality also
holds for the whole completion map. Invert its isomorphism on constructible tensors,
apply the model comparison isomorphisms and raw rationalization, and include the
result at the common stage. Naturality along the stage and representative isomorphisms
transports it back to M and N and cancels the intervening comparison factors. The result
is precisely the displayed equation, with the fixed canonical pullback tensor map.
No identity, composition or internal-Hom equation is used. -/
theorem normalized_reindexing_tensor_compatibility
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (h_integral_normalization : ∀ (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g)) :
    ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) U.base.left),
    letI := (C.data T).units
    letI := (C.data U).units
    (derivedPull l T.base.left g.hom (C.ring T U g)).map ((C.data U).tensor.tensor.hom.app (M, N)) ≫
      (C.comparison T U g).inv.app ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj
        (M, N)) ≫
      (ordinary l T.base.left (C.data T).realization).map
        (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom M N).hom =
    (C.pullTensor T U g).tensor.hom.app
        ((ordinary l U.base.left (C.data U).realization).obj M,
         (ordinary l U.base.left (C.data U).realization).obj N) ≫
      (C.data T).tensor.closed.tensor.map (Prod.mkHom
        ((C.comparison T U g).inv.app M) ((C.comparison T U g).inv.app N)) ≫
      (C.data T).tensor.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
        (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N) := by
  sorry

end WeilConjectures.AdicQbarRealization
