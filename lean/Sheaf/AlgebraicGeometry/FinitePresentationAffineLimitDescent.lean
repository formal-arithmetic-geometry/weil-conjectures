/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.Algebra.FinitePresentationColimit
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSectionsBijective
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Finitely presented modules descend along affine transition limits

Source: Stacks Project, Limits, Tag 01ZR, lemma-descend-modules-finite-presentation,
clauses (1), (2), (3) (blueprint: lem-trf-fp-modules-affine-limit-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical identification of an iterated tensor pullback with pullback along a
limit-cone projection. This is the inverse of the section-normalized composition comparison,
followed by transport along the cone equation; it makes no choice of module isomorphisms.
Source: Stacks, Tag 01ZR, clause (2), and Sheaves, Tag 0097
(blueprint: lem-trf-fp-modules-affine-limit-descent). -/
noncomputable def affineLimitTensorPullbackComparison
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (hij : i ≤ j) (M : (D.obj (op i)).Modules) :
    (tensorPullback (c.π.app (op j))).obj
        ((tensorPullback (D.map (homOfLE hij).op)).obj M) ≅
      (tensorPullback (c.π.app (op i))).obj M :=
  ((tensorPullbackSectionComp (c.π.app (op j)) (D.map (homOfLE hij).op)).symm.app M) ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj (op i) ↦ (tensorPullback f).obj M)
      (c.w (homOfLE hij).op))

/-- Objects, morphisms, and equalities of finitely presented modules descend to a stage.
Finite presentation is Mathlib's local finite free presentation, with no extra
quasi-coherence hypothesis. All pullbacks use the tensor formula.

Source: Stacks Project, Limits, Tag 01ZR, lemma-descend-modules-finite-presentation,
clauses (1), (2), (3) (blueprint: lem-trf-fp-modules-affine-limit-descent).

Proof:
1. Choose finite affine covers of the limit and of pair and triple intersections, including
   refinements of pair-chart overlaps. Descend this finite list by
   `lem-trf-affine-open-limit-descent`. The restricted systems remain affine-transition
   limits by `lem-weil-pbc-limit-cone-affine-projections-opens`.
2. Descend the quasi-compact intersections by clause (1) of
   `pqf-lem-limit-qc-open-descends`, then use its eventual-equality clause (2) to stabilize
   all inclusions and finite covering equations at a common upper stage. Each chart ring
   is a filtered colimit by `lem-weil-pbc-limit-global-sections-colimit`.
3. Finite presentation implies quasi-coherence by
   `lem-weil-pbc-quasi-coherent-finite-type-affine`. The affine tilde/global-sections
   adjunction `lem-weil-pbc-affine-tilde-gamma-adjunction` and
   `lem-weil-pbc-module-pullback-affine-sections-bijective` identify tensor pullback with
   scalar extension. Descend the local modules and comparison maps by
   `lem-pc-fp-module-map-descent-affine`.
4. Descend the inverse of each limit comparison by the map clause of that affine lemma.
   Its equality clause makes both composites identities after a common enlargement.
   Thus the descended pair-chart comparisons are isomorphisms before gluing.
5. On pair-chart overlaps, the comparison maps have equal limit pullback. The affine
   equality clause makes them agree on every overlap refinement at one later stage.
   Their inverses agree by uniqueness, so they glue on the full pair intersections.
6. On the triple refinements, apply that equality clause to the cocycle and repeated-index
   identity equations. Their finite covers make the equations hold on full intersections.
7. The finite open cover is fpqc. Apply `lem-pc-fpqc-descent` to glue the local modules
   and their comparisons. Finite presentation descends by the same result, and the local
   limit identifications glue to the isomorphism in clause (1).
8. For clause (2), descend the restrictions of the given map on the finite affine cover
   using the affine map clause. Its equality clause makes these lifts agree on all pair
   refinements at a common stage, and fpqc descent glues them. The displayed comparison
   is the canonical tensor-pullback composition identification.
9. For clause (3), the affine equality clause makes the restrictions equal on a common
   stage cover. Faithfulness of fpqc descent gives equality of the global pulled-back maps.
-/
theorem finitePresentation_descent_affineLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) :
    (∀ F : c.pt.Modules, F.IsFinitePresentation →
      ∃ (i : I) (F_i : (D.obj (op i)).Modules), F_i.IsFinitePresentation ∧
        Nonempty ((tensorPullback (c.π.app (op i))).obj F_i ≅ F)) ∧
    (∀ (i : I) (F_i G_i : (D.obj (op i)).Modules),
      F_i.IsFinitePresentation → G_i.IsFinitePresentation →
      ∀ u : (tensorPullback (c.π.app (op i))).obj F_i ⟶
          (tensorPullback (c.π.app (op i))).obj G_i,
        ∃ (j : I) (hij : i ≤ j)
          (u_j : (tensorPullback (D.map (homOfLE hij).op)).obj F_i ⟶
            (tensorPullback (D.map (homOfLE hij).op)).obj G_i),
          (affineLimitTensorPullbackComparison D c hij F_i).inv ≫
            (tensorPullback (c.π.app (op j))).map u_j ≫
            (affineLimitTensorPullbackComparison D c hij G_i).hom = u) ∧
    (∀ (i : I) (F_i G_i : (D.obj (op i)).Modules),
      F_i.IsFinitePresentation → G_i.IsFinitePresentation →
      ∀ u_i v_i : F_i ⟶ G_i,
        (tensorPullback (c.π.app (op i))).map u_i =
          (tensorPullback (c.π.app (op i))).map v_i →
        ∃ (j : I) (hij : i ≤ j),
          (tensorPullback (D.map (homOfLE hij).op)).map u_i =
            (tensorPullback (D.map (homOfLE hij).op)).map v_i) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
