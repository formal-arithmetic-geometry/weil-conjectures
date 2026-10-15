/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.RingTheory.SmoothPushoutFilteredColimitStage
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Topology.Defs.Filter

/-!
# Smoothness descends along qcqs affine-transition limits

Source: Stacks Project, Limits, Tag 0C0C, lemma-descend-smooth, in Situation 081D;
persistence at later stages by Morphisms, Tag 01VB
(blueprint: lem-weil-pbc-descend-smooth-qcqs).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented morphism between qcqs schemes over a qcqs stage is
smooth at every sufficiently late stage if its limit base change is smooth.

Source: Stacks Project, Limits, Tag 0C0C, lemma-descend-smooth, Situation 081D;
Morphisms, Tag 01VB (blueprint: lem-weil-pbc-descend-smooth-qcqs).

Proof:
1. Choose affine triples U_a → V_a → W_a around each point of X₀, with W_a in S₀,
   V_a in Y₀, and U_a in X₀. Quasi-compactness gives finitely many U_a covering X₀
   (lem-weil-pbc-affine-opens-basis, def-weil-pbc-quasi-compact-scheme).
2. Base change the triples along S_k → S₀ and S → S₀. The resulting schemes are
   affine by affine permanence and the affine limit projections. Their restricted maps
   are induced by finitely presented ring maps B₀ → C₀
   (def-pc-fibre-product, lem-weil-pbc-limit-affine-transition,
   lem-weil-pbc-affine-morphism-permanence,
   lem-weil-pbc-lfp-affine-opens-finite-presentation,
   lem-weil-pbc-morphism-factors-through-open-subscheme).
3. The open-limit clause and the fibre-product universal property identify V with the
   limit of V_k. Thus B = colim B_k and C_k = C₀ ⊗[B₀] B_k, C = C₀ ⊗[B₀] B,
   compatibly with projections (def-pc-fibre-product,
   lem-weil-pbc-limit-affine-transition, lem-weil-pbc-fibre-product-affine-spectra).
4. Restrict limit smoothness to U → V, translate to B → C, and apply fixed-map smooth
   pushout descent to obtain a smooth stage for each triple
   (lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-weil-pbc-affine-opens-induced-ring-map-spec-square,
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine,
   lem-sbc-smooth-pushout-filtered-colimit-stage).
5. Directedness gives a common upper bound i for i₀ and the finitely many stages.
   Pullback pasting and smooth base-change stability make all chart maps smooth at i;
   compose with the open inclusions into Y_i
   (def-pc-fibre-product, lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-smooth-ring-map-base-change-composition,
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine,
   lem-weil-pbc-affine-opens-induced-ring-map-spec-square,
   lem-weil-pbc-smooth-restrict-open-subschemes).
6. The pulled-back U_a cover X_i, so smoothness local on the source gives smoothness
   of f_i (lem-weil-pbc-smooth-local-on-source). This also covers empty X₀.
7. For every j ≥ i, pullback pasting identifies f_j with the base change of f_i;
   smooth base-change stability gives the conclusion
   (def-pc-fibre-product, lem-pc-proper-base-change). -/
theorem exists_eventually_smooth_of_isLimit_qcqs
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (_hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (_hf : Smooth (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j),
      Smooth (((Over.pullback (D.map (homOfLE (hi.trans hij)).op)).map f₀).left) := by
  sorry

end AlgebraicGeometry
