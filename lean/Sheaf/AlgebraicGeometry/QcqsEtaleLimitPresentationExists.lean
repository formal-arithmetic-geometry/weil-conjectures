/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.QcqsEtaleLimitPresentation

import Sheaf.CategoryTheory.PseudofunctorSplitFamily
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-! # Existence of finite-cover presentations of qcqs etale limit sites

Source: Stacks Project, Sites, Tags 09YL and 0A35; ILO XX 4.4, printed p.373.
(blueprint: lem-per-qcqs-etale-limit-presentation-exists)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.QcqsEtaleLimit

/-- The strict finite-cover site and its normalized projection cone exist.

Source: Stacks Project, Sites, Tags 09YL and 0A35; ILO XX 4.4, printed p.373.
(blueprint: lem-per-qcqs-etale-limit-presentation-exists).

Proof: take the full qcqs subcategories of the small etale sites. Every morphism
between their objects is qcqs, and their finite limits are computed in schemes.
Pullback preserves these limits and finite jointly surjective families. Finite affine
refinements give the topology induced from the full small etale site, so dense
comparison identifies their sheaf categories. Normalize identity pullbacks and apply
split-family strictification with empty incoming diagram to the pullback pseudofunctor
on I opposite. Transport coverings through the evaluation equivalences. Apply the
colimit-of-sites theorem to the resulting strict diagram, giving the object and arrow
colimits, finite covering axioms and projection adjunctions. A finite diagram lifts to
one stage. Its limit there remains a limit after taking the category colimit: maps from
a test object are the filtered colimit of stagewise Hom sets, and filtered colimits of
sets commute with finite limits. The empty diagram proves the terminal-object clause.
Finally identify each stage's sheaves with the full small etale topos and transport the
projection adjunctions through these equivalences. The right adjoints are restriction
of sections, so their cocycle and the restriction compatibility are evaluation of the
strict cocone identities and the canonical pullback composition isomorphisms. Assemble
these data into Presentation. No topos universal property or point construction is
required for this step. -/
theorem presentation_nonempty
    (I : Type u) [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (a : i ⟶ j), QuasiCompact (D.map a)]
    [∀ (i j : I) (a : i ⟶ j), QuasiSeparated (D.map a)] :
    Nonempty (Presentation D) := by sorry

end AlgebraicGeometry.QcqsEtaleLimit
