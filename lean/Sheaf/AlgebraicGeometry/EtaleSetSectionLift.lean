/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
import Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.EtaleSetSectionComparisonLaws
import Sheaf.AlgebraicGeometry.EtaleSetSectionEventualEquality
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.CategoryTheory.ColimitSiteSections
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-! # An intermediate step in continuity of étale sections
Source: Stacks Project, Tag 09YQ. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Theorem Tag 09YQ, proof via Tags 0EYL,
04HR, and 09YN, followed by finite affine-cover descent.
(blueprint: lem-weil-pbc-sets-section-lift).
Proof: restrict to the cofinal tail of the chosen stage. For affine W₀, affine transition
maps and limit projections allow the affine-site inverse-image comparison. The affine
site colimit and restriction equivalences identify limit sections with the filtered
colimit of stage sections, by the colimit-of-sites section theorem. The composition
isomorphisms identify the pulled-back sheaves at the limit with the constant sheaf
system having value the inverse image of G there; connectedness identifies its colimit
with that inverse image. Unit compatibility identifies its maps with the displayed
comparisons, so every section lifts to a stage.
For general W₀, choose a finite affine cover and finite affine refinements of its overlaps.
Lift the restrictions of t on this finite cover by the affine result. The overlap
equalities hold at the limit; etaleSetSectionEventualEquality makes them hold at some
later stage. Directedness supplies one common stage for all lifts and equalities.
The sheaf equalizer condition glues these compatible lifts to a section of W at that
stage. Uniqueness in the sheaf condition identifies its limit image with t. Empty
covers give the unique section of the empty object, so include that case. -/
theorem etaleSetSectionLift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀))) :
    ∃ (j : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀))),
      (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G W₀) s = t := by sorry

end AlgebraicGeometry
