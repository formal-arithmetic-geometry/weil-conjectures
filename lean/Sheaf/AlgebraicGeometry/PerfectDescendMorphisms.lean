/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction

/-! # Descent of morphisms between perfect complexes

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.29.2, Tag 09RE,
used in Lemma 36.29.3, Tag 09RF (blueprint: lem-pc-perfect-descend-morphisms).

The shared coherent derived-pullback composition comparisons transport the stage map
to the direct pullbacks of both objects. The equality clause uses a common starting stage for the
finite list of morphisms; directedness puts any finite list of starting stages in this form.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The recorded canonical composition comparison along a base-change map.
This specializes the shared counit-pinned comparisons of
`exists_derivedPullbackComposition`; it introduces no new pullback functor.
Source: Stacks Project, Derived Categories of Schemes, Tag 09RE; Cohomology, Tag 0D5S
(blueprint: lem-pc-perfect-descend-morphisms). -/
noncomputable def perfectDescentComparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    derivedPullback (pullback.fst s T'.hom) ≅
      derivedPullback (pullback.fst s T.hom) ⋙ derivedPullback (baseChangeMap s g) :=
  eqToIso (congrArg (fun k ↦ derivedPullback k) (baseChangeMap_fst s g).symm) ≪≫
    (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
        (baseChangeMap s g) (pullback.fst s T.hom)).symm

/-- Morphisms between perfect complexes descend, isomorphisms descend as isomorphisms,
and finitely many equalities are eventually true at one common stage.
Source: Stacks Project, Derived Categories of Schemes, Tag 09RE, used in Tag 09RF
(blueprint: lem-pc-perfect-descend-morphisms).

Proof, following the three steps of the node:
1. For a quasi-compact open of `Xi`, consider the assertion that the colimit of Hom
   groups maps bijectively to the limit Hom group, in every shift. Perfect objects have
   quasi-coherent cohomology (Tag 08DB). Apply the quasi-compact-open induction principle
   lem-sc-invert-s-cohomology-induction. For the gluing step, the derived Mayer--Vietoris
   triangle (lem-pc-derived-mayer-vietoris-triangle) and the open-immersion adjunction
   (lem-pc-ringed-spaces-derived-adjoint) give compatible long exact Hom sequences.
   Filtered colimits of abelian groups are exact; the five lemma (lem-weil-pbc-five-lemma)
   gives bijectivity on the union from bijectivity on its two opens and their intersection.
2. On an affine open, represent both perfect objects by bounded complexes of finite
   projective modules (lem-pc-perfect-affine-bounded-projective). These are K-flat, so
   derived pullback is ordinary tensor product. The affine derived equivalence
   (lem-pc-affine-qcoh-derived-equivalence) identifies the relevant Hom groups with those
   of these tensor products. Apply lem-pc-affine-perfect-hom-colimit.
3. Surjectivity gives a representative of a morphism. Injectivity says that an equality
   in the limit becomes true later; directedness makes finitely many equalities true
   together. For an isomorphism, descend its inverse too, and then descend the two
   inverse identities, giving an isomorphism at a common later stage. -/
theorem perfect_descend_morphisms
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : Xi.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Xi.toRingedSpace).over U))]
    (Pi Qi : schemeDerivedCategory Xi) (hP : Xi.IsPerfect Pi) (hQ : Xi.IsPerfect Qi)
    :
    (∀ φ : (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Pi ⟶
        (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Qi,
      ∃ (j : I) (hij : i ≤ j)
        (φj : (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Pi ⟶
          (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Qi),
        (perfectDescentComparison s
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (c.ι.app i)))
            (Over.homMk (Spec.map (c.ι.app j))
              (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))).hom.app Pi ≫
          (derivedPullback (baseChangeMap s
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (c.ι.app i)))
            (Over.homMk (Spec.map (c.ι.app j))
              (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])))).map φj =
            φ ≫ (perfectDescentComparison s
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (c.ι.app i)))
            (Over.homMk (Spec.map (c.ι.app j))
              (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))).hom.app Qi ∧
          (IsIso φ → IsIso φj)) ∧
    (∀ (j : I) (hij : i ≤ j) (n : ℕ)
      (a b : Fin n →
        ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Pi ⟶
          (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Qi)),
      (∀ t : Fin n,
        (derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])))).map (a t) =
        (derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])))).map (b t)) →
      ∃ (k : I) (hjk : j ≤ k), ∀ t : Fin n,
        (derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))).map (a t) =
        (derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))).map (b t)) := by
  sorry

end AlgebraicGeometry
