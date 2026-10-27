/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.AlgebraicGeometry.RelativeSectionAlgebraCanonicalMap
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange

/-! # Descent of full generation and the normalized canonical section map

Source: Stacks Project, Constructions, Tag 01O9(3), and Morphisms, Tag 01VJ.
(blueprint: lem-trf-section-canonical-map-open-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Full generation and canonical maps descend through normalized open comparisons.
This does not assert existence of the global graded algebra or openness of its map.

Source: Stacks, Constructions, Tag 01O9(3) and its proof; Morphisms, Tag 01VJ,
(3) implies (5), adjunction-map and restriction paragraphs.
(blueprint: lem-trf-section-canonical-map-open-descent).

Proof: The specified comparison sends a homogeneous section s to its restriction,
written as the tensor-pullback unit 1 tensor s followed by the power comparison.
On a further trivializing open chart the adjunction evaluation therefore sends
b tensor s to b times the same restricted section, both before and after the base
restriction. Tensor multiplication and the degree-zero unit are preserved by this
formula. Thus it identifies the graded evaluations, not only their sources.
The scheme case of space_line_module_proj_map gives the generation-open and canonical
map for this evaluation, and its base-change clause, with D_i, identifies their
restrictions to h inverse U_i with the local generation opens and canonical maps.
The stalk condition defining GeneratesEverywhere is precisely generation of the
invertible homogeneous target: over a local ring its maximal-ideal quotient is a
one-dimensional vector space, so a section generates exactly when its residue is
nonzero. Since all local generation opens are full and the inverse images of U_i
cover Z, the global generation open is all of Z. Its canonical map is consequently
defined on Z. On each local trivializing principal chart, the normalized section
formula makes its homogeneous fraction map identical to that of r_local i. The
uniqueness/chart clause of the canonical-map theorem gives the displayed equality
after composing with D_i.relProjComparison. The relative-Proj base-change theorem
identifies this comparison with the canonical projection from the pullback. Chart
uniqueness also verifies the all-chart predicate IsCanonicalMap, including degree
zero, so the resulting map has exactly the asserted predicate. No open-immersion
hypothesis on any local map is used. Empty Z and the empty cover are allowed. -/
theorem section_canonical_map_open_descent {Z S : Scheme.{u}} (h : Z ⟶ S)
    [QuasiCompact h] [IsSeparated h] (N : Z.Modules) [N.IsInvertible]
    {I : Type v} (U : I → S.Opens) (hU : ∀ i : I, IsAffineOpen (U i))
    (hcover : iSup U = ⊤) (A : RelativeSectionAlgebra h N)
    (A_local : ∀ i : I, RelativeSectionAlgebra (h ∣_ U i)
      ((tensorPullback (h ⁻¹ᵁ U i).ι).obj N))
    (D : ∀ i : I, Scheme.GradedAlgebraData.PullbackData (U i).ι A.data (A_local i).data)
    (hD : ∀ (i : I) (V : S.affineOpens) (W : (U i).toScheme.affineOpens)
      (hle : W.1 ≤ (U i).ι ⁻¹ᵁ V.1) (n : ℕ) (a : A.data.grading V n),
      (A_local i).sectionEquiv W n
          ⟨(D i).map hle a, ((D i).map hle).map_mem a.property⟩ =
        (((tensorPullback (h ⁻¹ᵁ U i).ι).obj N).tensorPow n).val.map
          (homOfLE (by
            intro x hx
            change h ((h ⁻¹ᵁ U i).ι x) ∈ V.1
            rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι]
            exact hle hx)).op
          ((boundaryPullbackPowIso (h ⁻¹ᵁ U i).ι N n).hom.app _
            (tensorPullbackSection (h ⁻¹ᵁ U i).ι (N.tensorPow n) (h ⁻¹ᵁ V.1)
              (A.sectionEquiv V n a))))
    (hgen : ∀ i : I, (A_local i).GeneratesEverywhere)
    (r_local : ∀ i : I, (h ⁻¹ᵁ U i).toScheme ⟶ (A_local i).data.relProj)
    (hcanonical : ∀ i : I, (A_local i).IsCanonicalMap (r_local i)) :
    A.GeneratesEverywhere ∧ ∃ r : Z ⟶ A.data.relProj, A.IsCanonicalMap r ∧
      ∀ i : I, (h ⁻¹ᵁ U i).ι ≫ r = r_local i ≫ (D i).relProjComparison := by sorry

end AlgebraicGeometry.Scheme.Modules
