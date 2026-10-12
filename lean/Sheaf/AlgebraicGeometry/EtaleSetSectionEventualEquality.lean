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
(blueprint: lem-weil-pbc-sets-section-eventual-equality).
Proof: directedness first moves the two sections to a common stage on the cofinal tail.
For an affine descended object, the affine-site colimit theorem and unit-compatible
inverse-image comparison turn the given limit equality into equality in the filtered
colimit of section sets. Equality in a filtered colimit holds at some later stage.
For general W₀, restrict to a finite affine cover. Apply the affine assertion to the
two restrictions on each member. Choose a common later stage for these finitely many
equalities. Separatedness of the sheaf on this covering then gives equality of the
two sections over the entire base changed W₀. The resulting arrows to the original
two stages and comparison coherence give the displayed equality. Empty covers need
no equalities and separatedness already gives uniqueness. -/
theorem etaleSetSectionEventualEquality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    (j k : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀)))
    (t : ((Scheme.etaleSetPullback (D.map k.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)).obj W₀)))
 :
    (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
      (c.π.app (op i₀)) (c.w j.hom) G W₀) s =
      (etaleSetSectionComparison (c.π.app k.left) (D.map k.hom)
        (c.π.app (op i₀)) (c.w k.hom) G W₀) t →
    ∃ (l : Over (op i₀)) (a : l ⟶ j) (b : l ⟶ k),
      (etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map l.hom)
          ((D.map_comp a.left j.hom).symm.trans
            (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) a.w)) G W₀) s =
        (etaleSetSectionComparison (D.map b.left) (D.map k.hom) (D.map l.hom)
          ((D.map_comp b.left k.hom).symm.trans
            (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) b.w)) G W₀) t := by sorry

end AlgebraicGeometry
