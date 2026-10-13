/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Continuity of Hom sets for perfect complexes in a ring-colimit system.
Source: Stacks Project, perfect.tex, Tag 09RE, affine calculation and open induction.
(blueprint: lem-pc-perfect-hom-continuity).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical Hom map is surjective on every cofinal tail, and two representatives
with the same image agree on some entire later tail. These are the set-colimit
consequences of continuity of Hom; no isomorphism descent or finite collection of
relations is asserted here.
Source: Stacks Project, perfect.tex, Tag 09RE, proof of lemma-descend-homomorphisms
(blueprint: lem-pc-perfect-hom-continuity).

Proof: for each quasi-compact open of X, prove continuity in every shift. On an affine
open use `perfect_iff_affine_bounded_projective` to represent the restrictions by bounded
finite-projective complexes, use `exists_affineQCohDerivedEquivalence` to identify the
Hom groups with module-derived Hom, and use `affine_perfect_hom_colimit`. Bounded
projective complexes are K-flat, so these identifications intertwine derived pullback
with tensor extension. For a union of a quasi-compact open and an affine open, apply
`schemeDerived_mayerVietoris_triangle` to the second object at each stage and at the
limit. The open-immersion case of `nonempty_derivedPullbackAdjunction` identifies its
Hom exact sequence with the Hom sequences on the two opens and their intersection.
Filtered colimits of abelian groups are exact; the five lemma proves the comparison
bijection on the union from those on the opens and intersection in adjacent shifts.
`quasiCompactOpen_induction` now gives the bijection on X. The canonical composition
comparisons ensure compatibility of the transition maps. The tail above any fixed
stage is cofinal, giving the first assertion. Injectivity of the comparison and the
filtered-set colimit equality criterion give equality at a later stage; functoriality
of the transition maps preserves it at every stage beyond that stage, giving the
second assertion. The fixed starting index makes the index category nonempty. -/
theorem perfect_hom_continuity
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (X : Scheme.{u}) (s : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P Q : schemeDerivedCategory X) (hP : X.IsPerfect P) (hQ : X.IsPerfect Q) :
    (∀ (j₀ : I) (hij₀ : i ≤ j₀)
      (φ : (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q),
      ∃ (j : I) (hj₀j : j₀ ≤ j)
        (f : (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj P ⟶
          (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj Q),
        perfectLimitMap R c s (hij₀.trans hj₀j) f = φ) ∧
    (∀ (j : I) (hij : i ≤ j)
      (a b : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q),
      perfectLimitMap R c s hij a = perfectLimitMap R c s hij b →
      ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hkl : k ≤ l),
        perfectStageMap R s hij (hjk.trans hkl) a =
          perfectStageMap R s hij (hjk.trans hkl) b) := by sorry

end AlgebraicGeometry
