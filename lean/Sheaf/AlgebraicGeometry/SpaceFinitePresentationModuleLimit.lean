/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitDescent

/-!
# Continuity of finitely presented module sheaves on algebraic spaces

Source: Stacks Project, spaces-limits.tex, Tag 07V7,
lemma-descend-modules-finite-presentation; sites-modules.tex, Tag 03DO(7)
(blueprint: lem-sfb-space-fp-module-limit-category).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical composition comparison followed by the cone equation.
Source: Stacks, Tag 07V7, morphism clause; Tag 03D7, tensor associativity
(blueprint: lem-sfb-space-fp-module-limit-category). -/
def moduleLimitPullbackComparison {S : Scheme.{u}}
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ AlgebraicSpace S) (c : Cone D)
    {i j : I} (hij : i ≤ j) (M : (D.obj (op i)).Modules) :
    (moduleTensorPullback (c.π.app (op j))).obj
        ((moduleTensorPullback (D.map (homOfLE hij).op)).obj M) ≅
      (moduleTensorPullback (c.π.app (op i))).obj M :=
  (moduleTensorComposition (c.π.app (op j)) (D.map (homOfLE hij).op)).app M ≪≫
    eqToIso (congrArg (fun f ↦ (moduleTensorPullback f).obj M) (c.w (homOfLE hij).op))

/-- Tensor pullback preserves finite presentation for every space morphism.
Source: Stacks, sites-modules.tex, Tag 03DO, lemma-local-pullback, clause (7)
(blueprint: lem-sfb-space-fp-module-limit-category).
Proof: finite presentation is a local cokernel of a map of finite free modules.
Use the canonical enlarged ringed sites of lem-trf-space-enlarged-etale-ringed-site-model.
Tensor pullback preserves cokernels and finite coproducts, being a left adjoint,
and sends the structure module to the structure module. On localized sites this
pulls a finite presentation back to a finite presentation. Refine the pulled-back
cover by scheme charts and restrict through the module comparison equivalences.
Thus the presentation is local for the small etale topology on the source. -/
theorem isFinitePresentation_moduleTensorPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (a : X ⟶ Y) (M : Y.Modules) [M.IsFinitePresentation] :
    ((moduleTensorPullback a).obj M).IsFinitePresentation := by
  sorry

/-- Objects, maps and equalities of finitely presented modules descend along affine limits.
Quasi-compactness is the existence of a quasi-compact scheme atlas. Quasi-separatedness
is expressed by quasi-compact scheme intersections of every two affine scheme charts;
this is absolute quasi-separatedness, without an assumption on the ambient scheme.

Source: Stacks, spaces-limits.tex, Tag 07V7, lemma-descend-modules-finite-presentation,
with the hypotheses of lemma-descend-finite-presentation
(blueprint: lem-sfb-space-fp-module-limit-category).

Proof:
1. Finite presentation implies quasi-coherence by def-trf-space-quasi-coherent-module.
   Use lem-sfb-scheme-etale-module-exact-finiteness-comparison and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence to identify scheme-chart
   finite presentations and their tensor pullbacks with the scheme module notions.
2. Use lem-trf-space-enlarged-etale-ringed-site-model to localize at arbitrary etale
   spaces and identify the canonical ringed pullbacks. Finite presentation is preserved
   by the preceding theorem, the space version of lem-pc-tensor-pullback-finite-presentation.
3. Fix a stage and choose an affine surjective etale atlas, using
   lem-trf-space-qc-finite-affine-atlas-refinement, lem-a1-space-finite-affine-subatlas
   and lem-sfb-qc-space-affine-etale-atlas. Base change it along the tail of the system.
   By lem-sfb-space-affine-locality the chart schemes are affine. By
   lem-sfb-space-affine-limits-schematic-stages their limit is the corresponding
   limit chart. The double and triple overlaps are qcqs schemes by
   lem-sfb-qcqs-space-fibre-product and lem-weil-pbc-affine-scheme-qcqs.
4. Apply lem-sfb-space-qcoh-groupoid-equivalence: a module is a chart module with an
   isomorphism on the double overlap, identity on the diagonal and the cocycle on
   the triple overlap. The cocycle orientation is alpha02 = alpha12 composed alpha01.
5. Apply lem-trf-fp-modules-affine-limit-descent to descend the chart module to a stage.
6. Apply its map clause on the overlap to descend the gluing isomorphism and its
   inverse, and its equality clause to make their composites identities at a later stage.
7. On the chart and triple overlap, its equality clause forces the diagonal identity
   and cocycle at a common stage. The groupoid equivalence then glues a finitely
   presented module, whose pullback is the given module. This proves object descent.
8. Descend a map on the chart by the scheme map clause. Force compatibility on the
   double overlap by eventual equality, then glue by full faithfulness of the groupoid
   equivalence. For two maps equal on the limit, descend that equality on the chart
   and apply faithfulness. These give map descent and eventual equality. Directedness
   supplies common upper bounds throughout. The displayed comparison is the canonical
   tensor composition isomorphism, so all map equations have their specified meaning.
-/
theorem finitePresentation_module_descent_affineLimit {S : Scheme.{u}}
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ AlgebraicSpace S)
    (hqc : ∀ i : Iᵒᵖ, ∃ (U : Over S) (a : yoneda.obj U ⟶ (D.obj i).obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ (i : Iᵒᵖ) (U V : Over S), IsAffine U.left → IsAffine V.left →
      ∀ (a : yoneda.obj U ⟶ (D.obj i).obj.obj) (b : yoneda.obj V ⟶ (D.obj i).obj.obj),
        ∃ (W : Over S) (p : W ⟶ U) (q : W ⟶ V),
          IsPullback (yoneda.map p) (yoneda.map q) a b ∧ CompactSpace W.left)
    (haff : ∀ {i j : Iᵒᵖ} (f : i ⟶ j),
      IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map f).hom.hom)
    (c : Cone D) (hc : IsLimit c) :
    (∀ M : c.pt.Modules, M.IsFinitePresentation →
      ∃ (i : I) (M_i : (D.obj (op i)).Modules), M_i.IsFinitePresentation ∧
        Nonempty ((moduleTensorPullback (c.π.app (op i))).obj M_i ≅ M)) ∧
    (∀ (i : I) (F_i G_i : (D.obj (op i)).Modules),
      F_i.IsFinitePresentation → G_i.IsFinitePresentation →
      ∀ f : (moduleTensorPullback (c.π.app (op i))).obj F_i ⟶
          (moduleTensorPullback (c.π.app (op i))).obj G_i,
        ∃ (j : I) (hij : i ≤ j)
          (f_j : (moduleTensorPullback (D.map (homOfLE hij).op)).obj F_i ⟶
            (moduleTensorPullback (D.map (homOfLE hij).op)).obj G_i),
          (moduleLimitPullbackComparison D c hij F_i).inv ≫
            (moduleTensorPullback (c.π.app (op j))).map f_j ≫
            (moduleLimitPullbackComparison D c hij G_i).hom = f) ∧
    (∀ (i : I) (F_i G_i : (D.obj (op i)).Modules),
      F_i.IsFinitePresentation → G_i.IsFinitePresentation →
      ∀ f g : F_i ⟶ G_i,
        (moduleTensorPullback (c.π.app (op i))).map f =
          (moduleTensorPullback (c.π.app (op i))).map g →
        ∃ (j : I) (hij : i ≤ j),
          (moduleTensorPullback (D.map (homOfLE hij).op)).map f =
            (moduleTensorPullback (D.map (homOfLE hij).op)).map g) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
