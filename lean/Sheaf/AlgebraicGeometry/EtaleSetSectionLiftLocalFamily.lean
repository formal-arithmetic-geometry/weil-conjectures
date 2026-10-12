/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.EtaleSetSectionComparisonLaws
import Sheaf.AlgebraicGeometry.EtaleSetSectionEventualEquality
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-! # Compatible local stage lifts of étale inverse-image sections
Source: Stacks Project, Étale Cohomology, Tag 09YQ, using Sites Tag 09YN. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology Tag 09YQ, finite affine-cover
reduction, using Sites Tag 09YN
(blueprint: lem-weil-pbc-sets-section-lift-local-family).
Proof: W₀ is qcqs since its structure map is quasi-compact and quasi-separated and
its base is qcqs. Choose a finite affine open cover V of W₀ and identify its finite
index type with Fin n. All V are étale over the base, with quasi-compact and
quasi-separated structure maps. Apply haff to the restrictions of t and choose one
common stage for the finitely many lifts. Comparison coherence preserves their images.
Choose finite affine refinements of the pairwise intersections; these exist because
W₀ is quasi-separated. The two restrictions to each such affine refinement have
identical limit images by naturality. Apply eventual equality on these finitely many
objects, then choose one later stage for all the equalities. Separatedness on each
refined intersection gives compatibility on that intersection, hence on every pair
of arrows with equal composites into W₀. The original covering stays covering under
base change at both the chosen stage and the limit. The local images are the original
restrictions of t by coherence. If n is zero, there are no representatives or overlap
equalities to choose; nonemptiness supplies a stage and all compatibility clauses
are vacuous. This lemma constructs only a compatible family, not a global section. -/
theorem etaleSetSectionLift_local_family
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    (haff : ∀ (W : (D.obj (op i₀)).Etale) (_ : IsAffine W.left),
      QuasiCompact W.hom → QuasiSeparated W.hom →
      ∀ t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W)),
      ∃ (j : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W))),
        (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G W) s = t)
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀))) :
    ∃ (n : ℕ) (V : Fin n → (D.obj (op i₀)).Etale) (f : ∀ b, V b ⟶ W₀)
      (j : Over (op i₀))
      (s : ∀ b, ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b)))),
      (∀ b, IsAffine (V b).left) ∧
      Sieve.ofArrows (fun b ↦
        (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b))
        (fun b ↦ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map (f b)) ∈
        (D.obj j.left).smallEtaleTopology
          ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀) ∧
      Sieve.ofArrows (fun b ↦
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V b))
        (fun b ↦ (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op i₀))).map (f b)) ∈ c.pt.smallEtaleTopology
          ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀) ∧
      (∀ (Y : (D.obj j.left).Etale) (b b' : Fin n)
        (a : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b))
        (a' : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b')),
        a ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map (f b) =
          a' ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map (f b') →
        ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map a.op (s b) =
          ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map a'.op (s b')) ∧
      (∀ b, (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G (V b)) (s b) =
        ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).map (f b)).op t)
        := by sorry

end AlgebraicGeometry
