/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.AlgebraicGeometry.EtaleGloballyGenerated
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Filtered colimits of globally generated abelian sheaves

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary`, lemma `lem-kun-colim-gbl-gen`
(blueprint: lem-kun-colim-gbl-gen).

The evaluation is the constant sheaf of the free abelian group on all global sections,
with the morphism adjoint to the linear combination of those sections. Since the
constant-sheaf functor is a left adjoint, its source is the coproduct of copies of the
constant integer sheaf. This extends the free-group model used in
`AlgebraicGeometry.Scheme.etaleAbelianGlobalSectionsEvaluation` to an arbitrary site,
using Mathlib's general global-sections functor instead of evaluation at a final object.

## Main definitions and statements

- `CategoryTheory.Sheaf.abelianGlobalSectionsEvaluation`: general-site evaluation.
- `CategoryTheory.Sheaf.epi_globalSectionsEvaluation_colimit`: the evaluation of a
  filtered colimit is epi if every stage evaluation is epi.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- The evaluation morphism from the coproduct of constant integer sheaves indexed by
all global sections of an abelian sheaf on an arbitrary site.

Source: blueprint lemma `lem-kun-colim-gbl-gen`, opening paragraph and displayed evaluation
(blueprint: lem-kun-colim-gbl-gen). The global-sections group `Sheaf.Γ` is the limit of
the underlying abelian presheaf, so its elements are precisely compatible families.
Equivalently these are maps from the constant integer sheaf. The free abelian group on
these sections is the coproduct of integer groups, and the left-adjoint constant-sheaf
functor preserves that coproduct. The adjoint of `Finsupp.linearCombination ℤ id` therefore
sends the generator indexed by each section to that same section, as required. -/
noncomputable def abelianGlobalSectionsEvaluation
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{max u v}) :
    (constantSheaf J AddCommGrpCat.{max u v}).obj
      (AddCommGrpCat.of (((Sheaf.Γ J AddCommGrpCat.{max u v}).obj G) →₀ ℤ)) ⟶ G :=
  ((constantSheafΓAdj J AddCommGrpCat.{max u v}).homEquiv _ G).symm
    (AddCommGrpCat.ofHom (Finsupp.linearCombination ℤ id).toAddMonoidHom)

/-- A filtered colimit of globally generated abelian sheaves is globally generated.
The source of `abelianGlobalSectionsEvaluation` is a model for the coproduct indexed
by all maps from the constant integer sheaf, and its composites with those summand
injections are exactly the indexing maps. Thus `Epi` expresses the evaluation definition.

Source: blueprint lemma `lem-kun-colim-gbl-gen`, statement and categorical proof;
Stacks Project, Tags 03CO, 002F and 003B (blueprint: lem-kun-colim-gbl-gen).

Proof plan:
1. A morphism from the constant integer sheaf is, by the sheafification adjunction,
   a compatible family of sections: the presheaf map sends `n` to `n` times the section.
   If a terminal object exists, the family is determined by its section there. This is
   the abelian evaluation notion of `def-kun-global-generated`.
2. Form the sheaf colimit and the coproduct evaluation maps, using the existence clause
   of `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` and the universal
   properties in `def-weil-pbc-category-colimit`.
3. For each stage `i`, map its evaluation coproduct into the colimit evaluation coproduct
   by sending the summand indexed by `s` to the one indexed by `s ≫ colimit.ι F i`.
   The coproduct universal property makes the resulting evaluation square commute.
4. If two maps out of `colimit F` agree after its evaluation, precompose with the maps
   from step 3 and cancel the stage evaluations using `hF` and `def-galois-epi-final`.
   They then agree after every colimit injection.
5. The uniqueness part of the colimit universal property makes the two maps equal.
   Thus the colimit evaluation is epi. The argument even works without filteredness,
   but the statement retains the filteredness hypothesis of the node. -/
theorem epi_globalSectionsEvaluation_colimit
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {I : Type (max u v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J AddCommGrpCat.{max u v})
    (hF : ∀ i : I, Epi (abelianGlobalSectionsEvaluation J (F.obj i))) :
    Epi (abelianGlobalSectionsEvaluation J (colimit F)) := by
  sorry

end CategoryTheory.Sheaf
