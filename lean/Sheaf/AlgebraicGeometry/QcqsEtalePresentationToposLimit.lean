/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.QcqsEtaleLimitPresentation

import Sheaf.CategoryTheory.FilteredColimitPseudococones
import Sheaf.CategoryTheory.Sites.LexCoverFunctorExtension

/-! # The universal property of a finite-cover etale limit presentation

Source: Stacks Project, Sites, Tags 00X6, 03A1 and 0A35; ILO XX 4.4.
(blueprint: lem-per-qcqs-etale-presentation-topos-limit)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.QcqsEtaleLimit

/-- Every normalized finite-cover presentation has the topos 2-limit property.

Source: Stacks Project, Sites, Tags 00X6, 03A1, 0A35 and 04AX; ILO XX 4.4,
printed p.373 (blueprint: lem-per-qcqs-etale-presentation-topos-limit).

Proof: for a cone from a Grothendieck topos E, restrict each inverse image to
sheafified representables on the corresponding stage. The lex-cover extension
equivalence identifies these with finite-limit-preserving functors sending covers to
jointly epimorphic families. The cone comparisons, after taking adjunction mates,
are the coherent pseudococone comparisons of these functors. The restriction
equivalence for filtered category colimits glues them to a functor from P.colimit.pt.
Finite diagrams and finite covers descend to stages, so this functor is left exact and
cover preserving. Extend it by the lex-cover equivalence. Its right adjoint on a sheaf
is the Hom presheaf, which on stage representables is restriction of sections;
P.restriction therefore identifies the resulting composites with the original cone.
The pseudococone coherence supplies Factorization.compatibility. Both restriction
equivalences are fully faithful on all natural transformations, hence lift every
compatible family of inverse-image transformations uniquely. Taking adjunction mates
reverses the direction and gives precisely the unique direct-image transformation in
IsToposLimit, with the displayed whiskering equalities. This proves both conjuncts of
the universal property for an already supplied presentation, without constructing a
presentation, choosing points, or proving reindexing invariance. -/
theorem presentation_isToposLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (P : Presentation D) : IsToposLimit P.projections := by sorry

end AlgebraicGeometry.QcqsEtaleLimit
