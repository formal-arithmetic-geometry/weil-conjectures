/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.QcqsEtaleLimitPresentation

import Sheaf.CategoryTheory.FilteredColimitPseudococones
import Sheaf.CategoryTheory.Sites.LexCoverFunctorExtension
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-! # Canonical comparisons of etale limit presentations

Source: Stacks Project, Sites, Tags 09YL and 0A35; Categories, Tags 04E7 and 04AX.
(blueprint: lem-per-qcqs-etale-presentation-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.QcqsEtaleLimit

/-- Initial reindexing and a scheme-diagram isomorphism canonically compare supplied
presentations. This includes independence of the chosen strictification.

Source: Stacks Project, Categories, Tags 04E7 and 04AX; Sites, Tags 09YL, 0A35,
00X6 and 03A1; ILO XX 4.4, printed p.373.
(blueprint: lem-per-qcqs-etale-presentation-comparison).

Proof: the opposite of r is final. Final reindexing induces an equivalence of the
object-and-arrow category colimits. The scheme isomorphisms give equivalences of the
qcqs etale categories, coherent with pullback by the naturality of epsilon. Transfer
these through the evaluation equivalences of the two presentations and apply descent
of coherent objectwise equivalences. This gives an equivalence of the colimit
categories, with specified stage comparisons. It identifies the generated topologies:
a cover coming from a reindexed stage is an original stage cover; conversely every
original stage maps to a reindexed stage by finality, and pullback carries its finite
covers to that stage. Dense site comparison gives the sheaf equivalence. Restriction
of sections identifies its direct-image composites with the displayed projection
direct images; the stage comparisons and pullback pasting give Comparison.compatibility.
For another comparison, restrict its inverse-image functor and comparisons to stage
representables. Full faithfulness of pseudococone restriction and lex-cover extension
provides a unique comparison transformation there, hence on all sheaves. It is
invertible because the stage transformations are invertible; its inverse extends in
the same way. Adjunction mates give exactly Comparison.IsCanonical. This uses only
the two supplied presentations and constructs neither of them. -/
theorem presentation_comparison
    {I J : Type u} [SmallCategory I] [SmallCategory J]
    [IsCofiltered I] [IsCofiltered J]
    {D : I ⥤ Scheme.{u}} {D' : J ⥤ Scheme.{u}}
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ j : J, CompactSpace (D'.obj j)] [∀ j : J, QuasiSeparatedSpace (D'.obj j)]
    (P : Presentation D) (P' : Presentation D') (r : J ⥤ I) [r.Initial]
    (ε : D' ≅ r ⋙ D) :
    ∃ c : Comparison P.projections P'.projections r ε, c.IsCanonical := by sorry

end AlgebraicGeometry.QcqsEtaleLimit
