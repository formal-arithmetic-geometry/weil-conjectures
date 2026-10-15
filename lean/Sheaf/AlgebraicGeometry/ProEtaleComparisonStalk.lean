/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import Sheaf.Paper.StrictHenselizationPointedMap
import Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Mathlib.CategoryTheory.Sites.Point.Basic
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections

/-!
# Etale-to-pro-etale comparison on geometric stalks

Source: Stacks Project, Pro-etale Cohomology, Tags 0GLZ and 0993
(blueprint: lem-cbc-proetale-comparison-stalk).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The canonical stalk comparison, expressed as a natural isomorphism normalized on
unit germs. This predicate merely spells out the conclusion for a coefficient category;
it introduces no chosen isomorphism or extra assumption on the inverse image.
Source: Stacks Project, Tags 0GLZ and 0993
(blueprint: lem-cbc-proetale-comparison-stalk). -/
def HasCanonicalProEtaleStalkComparison (T : Scheme.{u})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u + 1, u + 1} A]
    [HasColimitsOfSize.{u, u} A]
    (L : Sheaf T.smallEtaleTopology A ⥤ Sheaf (ProEt.topology T) A)
    (η : 𝟭 (Sheaf T.smallEtaleTopology A) ⟶
      L ⋙ (toProEt T).sheafPushforwardContinuous A
        T.smallEtaleTopology (ProEt.topology T)) : Prop :=
  ∃ c : L ⋙ sheafToPresheaf (ProEt.topology T) A ⋙
      (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ A).obj
        (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim ≅
      (pointSmallEtale t).sheafFiber,
    ∀ (H : Sheaf T.smallEtaleTopology A) (U : T.Etale)
      (x : (pointSmallEtale t).fiber.obj U),
      (η.app H).hom.app (op U) ≫
        colimit.ι (proEtaleGeometricStalkDiagram t (L.obj H))
          (op (StructuredArrow.mk (Y := (toProEt T).obj U) x)) ≫
        c.hom.app H = (pointSmallEtale t).toPresheafFiber U x H.obj

/-- Geometric stalks commute canonically with etale-to-pro-etale inverse image,
naturally for sets, abelian groups, and left modules over any fixed ring.
Source: Stacks Project, Tags 0GLZ, 0993, 03QO, 03Q1 and 00YR
(blueprint: lem-cbc-proetale-comparison-stalk).

Proof:
1. Form the strict localization S = Spec of the strict henselization at t. The
local-structure and pointed-map lemmas give a strictly henselian local ring and
its specified closed geometric point s, lying over t.
2. The classical pro-etale stalk lemma identifies the stalk with evaluation at S.
3. The comparison-pullback-sections lemma identifies that evaluation with sections
of the etale inverse image on S (Tag 0GLZ).
4. Strictly henselian closed-point sections equal the stalk at s (Tag 03QO).
The etale inverse-image-stalk-germ lemma identifies that stalk with the stalk at t.
Compose these identifications, using the inverse of the evaluation-to-stalk map.
5. Evaluation, sections comparison and germs commute with sheaf morphisms. The
last comparison is natural by its formula on unit germs, which exhaust the stalk.
The pointed lift is unique by its specified composites with all limit projections.
Thus the comparison is canonical and satisfies the displayed unit-germ normalization.
6. Both set stalk functors preserve finite products. Naturality with projections,
addition, zero and negation makes the comparison additive. Forgetting abelian groups
preserves the filtered neighbourhood colimits, so these are the abelian stalks.
7. Apply naturality to each scalar endomorphism. The filtered module-colimit
representatives and common-refinement formulas identify the resulting operations with
module stalk operations, so the comparison and its inverse are linear. The module
Kan extension and sheafification implement the set inverse image with these operations
(Sites, Tag 00YR). This uses no commutativity or finiteness of the ring. -/
theorem proEtale_comparison_stalk (T : Scheme.{u})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    HasCanonicalProEtaleStalkComparison T Ω t (Type (u + 1))
      (Functor.sheafPullbackConstruction.sheafPullback (toProEt T)
        (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T))
      (proEtaleSiteComparison T).unit ∧
    HasCanonicalProEtaleStalkComparison T Ω t AddCommGrpCat.{u + 1}
      (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T)
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit ∧
    ∀ (Λ : Type (u + 1)) [Ring Λ],
      HasCanonicalProEtaleStalkComparison T Ω t (ModuleCat.{u + 1} Λ)
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
        (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) T).unit := by
  sorry

end AlgebraicGeometry.Scheme
