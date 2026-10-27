/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Evaluation-transpose compatibility of realization reindexing

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- A tensor-compatible realization comparison preserves the permitted internal Hom map.
Source: Stacks 0GMX; Bhatt--Scholze, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-reindexing-hom).

Proof: Uncurry the asserted equation using the target tensor-Hom adjunction. Naturality
of this adjunction in its parameter and both Hom variables rewrites the left side as
pulled-back realized evaluation, followed by the comparison at the second input.
Here pullHom is by definition the transpose of pulled-back evaluation, so its counit
identity supplies this rewrite. Apply tensor compatibility and naturality of comparison
to the source evaluation arrow. The evaluation equation for the permitted-pair pullback
Hom comparison identifies the result with the uncurrying of the right side. The
realization HomLaws evaluation identities give the same realized evaluation on both
sides. Injectivity of uncurrying proves equality. All Hom objects used are the recorded
permitted pairs; no perfection assertion on their first input is needed. -/
theorem normalized_reindexing_hom
    (C : FamilyCore l D)
    (h_tensor_compatibility : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
          (M N : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) U.base.left),
        letI := (C.data T).units
        letI := (C.data U).units
        (derivedPull l T.base.left g.hom (C.ring T U g)).map ((C.data U).tensor.tensor.hom.app (M,
          N)) ≫
          (C.comparison T U g).inv.app ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj
            (M, N)) ≫
          (ordinary l T.base.left (C.data T).realization).map
            (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom M N).hom =
        (C.pullTensor T U g).tensor.hom.app
            ((ordinary l U.base.left (C.data U).realization).obj M,
             (ordinary l U.base.left (C.data U).realization).obj N) ≫
          (C.data T).tensor.closed.tensor.map (Prod.mkHom
            ((C.comparison T U g).inv.app M) ((C.comparison T U g).inv.app N)) ≫
          (C.data T).tensor.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj
            M,
            (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N)) :
    ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (P : (commonStageHomPairs l (PadicAlgCl l) U.base.left).FullSubcategory),
    letI := (C.data T).units
    letI := (C.data U).units
    (C.comparison T U g).hom.app
        ((commonStageDerivedInternalHom l (PadicAlgCl l) U.base.left).obj P) ≫
      (derivedPull l T.base.left g.hom (C.ring T U g)).map
        (homComparison l U.base.left (C.data U).realization (C.data U).tensor P) ≫
      pullHom l T.base.left g.hom (C.pullTensor T U g)
        ((ordinary l U.base.left (C.data U).realization).obj P.obj.1.unop)
        ((ordinary l U.base.left (C.data U).realization).obj P.obj.2) ≫
      (ambientHom l T.base.left (C.data T).realization).map
        (Prod.mkHom ((C.comparison T U g).hom.app P.obj.1.unop).op
          ((C.comparison T U g).inv.app P.obj.2)) =
    (ordinary l T.base.left (C.data T).realization).map
        (podCommonHomComparison l (PadicAlgCl l) g.hom P) ≫
      homComparison l T.base.left (C.data T).realization (C.data T).tensor
        ((podPairPullback (commonStageDerivedPullback l (PadicAlgCl l) g.hom)
      (commonStageHomPairs l (PadicAlgCl l) U.base.left)
      (commonStageHomPairs l (PadicAlgCl l) T.base.left)
      (podCommonPairs_pullback l (PadicAlgCl l) g.hom)).obj P) := by
  sorry

end WeilConjectures.AdicQbarRealization
