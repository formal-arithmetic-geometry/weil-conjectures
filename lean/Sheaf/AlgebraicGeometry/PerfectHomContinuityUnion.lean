/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomContinuityOn
import Sheaf.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Mayer--Vietoris gluing for continuity of perfect Hom
Source: Stacks Project, perfect.tex, Tag 09RE, quasi-compact-open induction step.
(blueprint: lem-pc-perfect-hom-continuity-union).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Continuity is preserved by adjoining an affine open, provided it also holds
on the intersection. The hypotheses are continuity for all perfect pairs, hence
supply the adjacent shifts in the long exact Hom sequence.
Source: Stacks Project, perfect.tex, Tag 09RE, Mayer--Vietoris step.
(blueprint: lem-pc-perfect-hom-continuity-union).

Proof: Let t : Y → X present U ∪ V. The preimages of U and V cover Y and their
intersection presents U ∩ V. Quasi-compactness of U and affineness of V make
both preimages quasi-compact; quasi-separatedness makes their intersection
quasi-compact. At every ring stage and at the colimit apply the derived
Mayer--Vietoris triangle to Q, whose cohomology is quasi-coherent because Q is
perfect. Apply Hom(P, -[n]). The open-immersion derived adjunction identifies
its local terms with Hom between the restrictions of P and Q[n]. Restriction
preserves perfectness, including all shifts. The given three open-local
conditions identify their filtered Hom colimits with the limit Hom groups in
all degrees. For each affine transition h, use
`schemeDerived_mayerVietoris_directImage` to compare the direct image of the
source triangle with the triangle of Rh_*Lh^*Q. Its natural boundary and the
adjunction unit Q → Rh_*Lh^*Q give the comparison from the target triangle.
Apply Hom(P, -[n]) and the derived adjunction to obtain a morphism of long exact
Hom sequences. Identify its local maps by open restriction and its middle map
with the canonical transport using the counit-pinned composition comparisons.
These identifications are necessary; the existence of a triangle alone does
not establish compatibility of the boundary maps.
Filtered colimits of abelian groups preserve exactness. The five lemma around
Hom(P, Q[n]) therefore gives a bijection at Y. Cofinality of every tail gives
the first clause of the condition; injectivity and the filtered-set equality
criterion give equality at a later stage, and functoriality propagates it along
the entire later tail, giving the second. These arguments also apply when U,
V or their intersection is empty; the corresponding Hom groups are zero. -/
theorem perfect_hom_continuity_union
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (X : Scheme.{u}) (s : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (hcontU : PerfectHomContinuityOn R c i X s U)
    (hcontV : PerfectHomContinuityOn R c i X s V)
    (hcontUV : PerfectHomContinuityOn R c i X s (U ⊓ V)) :
    PerfectHomContinuityOn R c i X s (U ⊔ V) := by sorry

end AlgebraicGeometry
