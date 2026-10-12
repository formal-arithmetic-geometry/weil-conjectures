/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.AlgebraicGeometry.EtaleDirectedColimitDescent

/-!
# Descent of étaleness to a stage of an inverse limit

Source: Stacks Project, Limits, Lemma 07RP in Situation 081D
(blueprint: lem-weil-pbc-descend-etale).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented morphism over a quasi-compact quasi-separated stage,
whose source and target are quasi-compact quasi-separated, is étale at some later stage
if its base change to the inverse limit is étale.

Source: Stacks Project, Limits, Lemma 07RP in Situation 081D
(blueprint: lem-weil-pbc-descend-etale).

Proof:
1. Cover X₀ by finitely many affine opens U mapping into affine opens V of Y₀,
   themselves mapping into affine opens W of S₀. Local finite presentation makes the
   maps of their coordinate rings finitely presented
   (lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-morphism-into-affine-scheme,
   lem-weil-pbc-lfp-affine-opens-finite-presentation, def-weil-pbc-scheme-conventions).
2. The inverse images Wᵢ are affine by pqf-def-affine-morphism. Their coordinate rings
   have colimit A, and the inverse image of W in the limit is Spec A, compatibly with
   projections (lem-weil-pbc-limit-affine-transition, lem-weil-pbc-spec-colimit-limit,
   def-weil-pbc-category-colimit, lem-weil-pbc-morphism-into-affine-scheme).
3. The corresponding pieces of the base changes of X₀ and Y₀ are spectra of tensor
   products. The restricted morphism is induced by the tensor product of the original
   ring map, as checked on both projections (def-pc-fibre-product,
   lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-colimit-etale-ring-map). The source pieces cover every stage.
4. Restrict the étale limit morphism to these opens and transport across the affine
   identifications (lem-weil-pbc-etale-composition-cancellation).
5. Apply lem-weil-pbc-colimit-etale-ring-map to each affine triple. Étaleness persists
   at larger indices by tensor cancellation and étale base change
   (lem-weil-pbc-tensor-cancel-base-change, lem-weil-pbc-etale-ring-base-change,
   lem-weil-pbc-etale-composition-cancellation).
6. Directedness gives a common upper bound of the finitely many indices and i₀.
   At this stage the restrictions are étale; their source opens cover, so the entire
   morphism is étale (lem-weil-pbc-etale-local-on-source,
   lem-weil-pbc-etale-composition-cancellation). -/
theorem Etale.exists_stage_of_inverseLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (hf : Etale (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (h : i₀ ≤ i),
      Etale (((Over.pullback (D.map (homOfLE h).op)).map f₀).left) := by
  sorry

end AlgebraicGeometry
