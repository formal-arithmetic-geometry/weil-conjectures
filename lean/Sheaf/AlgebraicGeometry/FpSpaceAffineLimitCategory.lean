/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.DescendMonomorphism
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Finitely presented algebraic spaces over affine inverse limits

Source: Stacks Project, Limits of Spaces, Tag 07SK, lemma-descend-finite-presentation,
specialized to affine scheme bases; Morphisms of Spaces, Tag 03XR
(blueprint: lem-sfb-fp-space-limit-category).

The three conjuncts express essential surjectivity, fullness and faithfulness of the
canonical filtered 2-colimit functor. All arrows are arbitrary morphisms over the base.
Base change is the usual pullback of presheaves over the represented scheme. The
comparison in the middle conjunct is exactly Mathlib's pullback composition isomorphism,
transported along the cone equation. No auxiliary comparison is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category of finitely presented algebraic spaces commutes with a nonempty directed
inverse limit of affine schemes. Finite presentation is quasi-compactness, quasi-compactness
of the relative diagonal, and local finite presentation on etale scheme charts.
Source: Stacks Project, Limits of Spaces, Tag 07SK, lemma-descend-finite-presentation;
Morphisms of Spaces, Tag 03XR, lemma-base-change-finite-presentation
(blueprint: lem-sfb-fp-space-limit-category).

Proof:
1. Base change preserves finite presentation by lem-sfb-space-flat-proper-fp-locality.
   For a finitely presented Y over T choose an affine etale atlas W and scheme kernel
   pair R, both finitely presented over T, by lem-sfb-fp-etale-presentation-criterion.
   By lem-a1-etale-atlas-presentation, Y is the sheaf quotient W/R.
2. Apply the object and morphism clauses of thm-pd-spreading-out to descend W, R and
   their two projections to a common stage. The affine bases are qcqs, and
   lem-weil-pbc-qcqs-morphism-permanence supplies all remaining qcqs conditions.
3. A map between finitely presented schemes over an affine base is locally finitely
   presented: if C=A[y]/J and B=A[x]/K, with y mapping to p(x), then
   B=C[x]/(K,y-p(x)). Use lem-weil-pbc-lfp-affine-opens-finite-presentation and
   def-weil-pbc-finitely-presented-algebra. Products remain finitely presented by
   lem-weil-pbc-qcqs-morphism-permanence and lem-weil-pbc-proper-fp-permanence.
4. By lem-weil-pbc-descend-etale and lem-weil-pbc-descend-monomorphism, enlarge the
   stage until both projections are etale and R to W times W is a monomorphism.
   These properties persist under base change, using lem-weil-pbc-etale-scheme-base-change
   and the pullback universal property.
5. Descend the diagonal, swapping and composition witnesses of the limiting kernel pair
   using thm-pd-spreading-out. Its equality clause makes their six projection equations
   hold at a common later stage; these give reflexivity, symmetry and transitivity.
6. Apply lem-trf-etale-relation-quotient to form Y_i=W_i/R_i. The presentation criterion
   makes Y_i finitely presented. Its pulled-back atlas and kernel pair agree with W,R
   by lem-trf-space-fibre-products-etale-covers. The quotient characterization from
   lem-a1-etale-atlas-presentation gives mutually inverse maps to Y, over T. This is
   the first conjunct.
7. For a limiting map between pullbacks of Y_i,Z_i, restrict to an affine etale atlas
   W_i of Y_i with finitely presented kernel pair R_i. Their base-change systems have
   limits W,R by lem-weil-pbc-scheme-over-limit. Apply
   lem-sfb-lfp-space-scheme-limit-test with fixed target Z_i to descend W to Z_i.
8. Apply the equality part of that limit test on the qcqs, possibly nonaffine R-system
   to equalize the two restrictions at a later stage. Pair the descended map with the
   structure map to the new base. By lem-a1-etale-atlas-presentation and the quotient
   universal property in lem-trf-etale-relation-quotient it factors through Y_j.
   The factorization is over T_j since its structure maps agree on the atlas; its
   pullback is the original map. This is the second conjunct.
9. If two stage maps have equal pullbacks, restrict to the same affine atlas and use
   the injectivity in lem-sfb-lfp-space-scheme-limit-test. Quotient uniqueness makes
   the maps equal at a later stage. This is the third conjunct. Maps initially at
   different stages are first moved to a common upper bound.
10. Objects of the filtered 2-colimit are represented at stages, and arrows are stage
    arrows modulo eventual equality. These three clauses give essential surjectivity
    and bijections on Hom sets. Choosing preimages of objects and using the inverse
    Hom bijections gives an inverse equivalence; uniqueness ensures functoriality.
    The universe convention is def-weil-size-convention. -/
theorem fp_space_affine_limit_category
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, IsAffine (D.obj (op i)).left] :
    (∀ (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
        (f : X.obj.obj ⟶ yoneda.obj c.pt),
      MapIsQuasiCompact f → MapIsQuasiCompact (pullback.diagonal f) →
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) X c.pt f →
      ∃ (i : I) (Y : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
        (g : Y.obj.obj ⟶ yoneda.obj (D.obj (op i))),
        MapIsQuasiCompact g ∧ MapIsQuasiCompact (pullback.diagonal g) ∧
        MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y (D.obj (op i)) g ∧
        Nonempty ((Over.pullback (yoneda.map (c.π.app (op i)))).obj (Over.mk g) ≅
          Over.mk f)) ∧
    (∀ (i : I) (X Y : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
        (f : X.obj.obj ⟶ yoneda.obj (D.obj (op i)))
        (g : Y.obj.obj ⟶ yoneda.obj (D.obj (op i))),
      MapIsQuasiCompact f → MapIsQuasiCompact (pullback.diagonal f) →
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) X (D.obj (op i)) f →
      MapIsQuasiCompact g → MapIsQuasiCompact (pullback.diagonal g) →
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y (D.obj (op i)) g →
      ∀ α : (Over.pullback (yoneda.map (c.π.app (op i)))).obj (Over.mk f) ⟶
        (Over.pullback (yoneda.map (c.π.app (op i)))).obj (Over.mk g),
      ∃ (j : I) (h : i ≤ j)
        (β : (Over.pullback (yoneda.map (D.map (homOfLE h).op))).obj (Over.mk f) ⟶
          (Over.pullback (yoneda.map (D.map (homOfLE h).op))).obj (Over.mk g)),
        α =
          eqToHom (congrArg (fun r ↦ (Over.pullback r).obj (Over.mk f))
            ((yoneda.map_comp (c.π.app (op j)) (D.map (homOfLE h).op)).symm.trans
              (congrArg (fun r ↦ yoneda.map r) (c.w (homOfLE h).op))).symm) ≫
          (Over.pullbackComp (yoneda.map (c.π.app (op j)))
            (yoneda.map (D.map (homOfLE h).op))).hom.app (Over.mk f) ≫
          (Over.pullback (yoneda.map (c.π.app (op j)))).map β ≫
          (Over.pullbackComp (yoneda.map (c.π.app (op j)))
            (yoneda.map (D.map (homOfLE h).op))).inv.app (Over.mk g) ≫
          eqToHom (congrArg (fun r ↦ (Over.pullback r).obj (Over.mk g))
            ((yoneda.map_comp (c.π.app (op j)) (D.map (homOfLE h).op)).symm.trans
              (congrArg (fun r ↦ yoneda.map r) (c.w (homOfLE h).op))))) ∧
    (∀ (i : I) (X Y : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
        (f : X.obj.obj ⟶ yoneda.obj (D.obj (op i)))
        (g : Y.obj.obj ⟶ yoneda.obj (D.obj (op i))),
      MapIsQuasiCompact f → MapIsQuasiCompact (pullback.diagonal f) →
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) X (D.obj (op i)) f →
      MapIsQuasiCompact g → MapIsQuasiCompact (pullback.diagonal g) →
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y (D.obj (op i)) g →
      ∀ α β : Over.mk f ⟶ Over.mk g,
        (Over.pullback (yoneda.map (c.π.app (op i)))).map α =
          (Over.pullback (yoneda.map (c.π.app (op i)))).map β →
        ∃ (j : I) (h : i ≤ j),
          (Over.pullback (yoneda.map (D.map (homOfLE h).op))).map α =
            (Over.pullback (yoneda.map (D.map (homOfLE h).op))).map β) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
