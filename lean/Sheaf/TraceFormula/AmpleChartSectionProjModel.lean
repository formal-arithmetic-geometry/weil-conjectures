/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.TraceFormula.SectionProjEtaleEmbedding
public import Sheaf.AlgebraicGeometry.OrdinaryEtaleIdentification
public import WeilConjectures.AlgebraicGeometry.Ample

/-! # The canonical section-Proj model on an ample scheme chart

Source: Stacks Project, Morphisms, Tag 01VJ, (1) implies (5), and Descent, Tag 03LC
(blueprint: lem-trf-ample-chart-section-proj-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative ampleness on one scheme chart gives the local model and open canonical map
required by section-Proj descent. The ordinary module is identified with the given
small-etale line module on every localized test, including the scalar actions.

Source: Stacks, Morphisms, Tag 01VJ, (1) implies (5), and Descent, Tag 03LC
(blueprint: lem-trf-ample-chart-section-proj-model).

Proof: ampleness on each inverse image of an affine base open gives compactness of
that inverse image, so p is quasi-compact. Apply the forward scheme canonical-Proj
criterion to H. This supplies its canonical RelativeSectionAlgebra, everywhere generation,
and an open canonical immersion. The ordinary/etale identification, its naturality,
and the cartesian realization of the line module identify H with the realization on
the chart. Pulling to every scheme test identifies all tensor powers, their products,
and units by the tensor-pullback composition and power comparisons. On affine base
opens, the compatible-section universal property identifies the ordinary pushforward
degrees with SpaceSectionAlgebra degrees. Transport the ordinary affine presentation
and evaluation along these identifications. The resulting degreeIso preserves products,
unit and restrictions. Both evaluations send a section to its tensor unit, so the
evaluation_eq field holds. The canonical chart formula is unchanged under these
identifications. Thus everywhere generation and the same open scheme immersion give
the asserted model. No trivialization, positive degree, or nonempty chart is chosen
globally; generation and the canonical formula are checked locally on all charts.
-/
theorem exists_sectionProjModel_of_ample_chart
    {S : Scheme.{u}} (X : AlgebraicSpace S) (L : X.Modules) (hL : X.IsLineModule L)
    (T : Over S) (V : X.EtaleSite) (p : V.obj.left ⟶ T)
    (H : (X.etaleForget.obj V).Modules) (hH : H.IsInvertible)
    (identification : OrdinaryEtaleIdentification X V L H)
    (hample : ∀ W : T.left.Opens, IsAffineOpen W →
      ∃ h : ((tensorPullback (p.left ⁻¹ᵁ W).ι).obj H).IsInvertible,
        @IsAmple (p.left ⁻¹ᵁ W).toScheme
          ((tensorPullback (p.left ⁻¹ᵁ W).ι).obj H) h) :
    ∃ A : SectionProjModel (yoneda.map p) ((lineTestFamily X L hL).pullback V.obj.hom),
      ∃ r : V.obj.left ⟶ projOver T A.affine,
        A.evaluation.IsGenerationOpen ⊤ ∧
          A.evaluation.IsCanonicalMap ⊤
            ((⊤ : Subfunctor (yoneda.obj V.obj.left)).ι ≫ yoneda.map r) ∧
          IsOpenImmersion r.left := by sorry

end AlgebraicGeometry.AlgebraicSpace
