/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
import Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.AlgebraicGeometry.EtaleSetSectionComparisonLaws
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.CategoryTheory.ColimitSiteSections
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Affine stage lifting of étale inverse-image sections
Source: Stacks Project, Étale Cohomology, Tag 09YQ, using Sites Tag 09YN. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology Tag 09YQ, proof via Tags 0EYL,
04HR and Sites Tag 09YN (blueprint: lem-weil-pbc-sets-section-lift-affine).
Proof: restrict the system to the upper tail of i₀, which is cofinal and directed.
The limit-affine-transition theorem makes each limit projection affine; affine base
change therefore preserves the affine étale objects. Present their limit site by the
strict affine-site system and its comparison equivalence. Restriction from the full
étale site is an equivalence, and the unit-compatible inverse-image comparison
transports the stage sheaves to the affine sites. At the limit, composition identifies
the pulled-back stage sheaves with the inverse image of G. These identifications
respect the transitions and units; the resulting constant diagram has that sheaf as
its colimit since the tail is connected. Sites Tag 09YN identifies sections on the
specified affine object with the filtered colimit of its stage section sets.
Choose a representative of t in that colimit. Unit compatibility, composition, and
pullback pasting identify its image with etaleSetSectionComparison, giving the
asserted stage and section. The empty affine scheme causes no exception: its section
set is a singleton by the sheaf condition and the tail is nonempty. -/
theorem etaleSetSectionLift_affine
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [IsAffine W₀.left]
    [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀))) :
    ∃ (j : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀))),
      (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G W₀) s = t := by sorry

end AlgebraicGeometry
