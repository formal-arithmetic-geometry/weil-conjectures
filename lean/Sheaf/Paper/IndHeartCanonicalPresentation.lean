/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.IndHeartFullFaithfulness
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt
public import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Filtered.Final
import Sheaf.Paper.CoefficientHeart
import Sheaf.Paper.CondensedConstantConstructibility

/-!
# Canonical presentations of ind-constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`sk-prop-ind-heart-canonical-presentation.md` and its proof
(blueprint: det-ind-heart-canonical-presentation).

`CostructuredArrow` is exactly the category of constructible modules mapping to B.
`Functor.isDenseAt` asserts the colimit property for its tautological cocone, whose
leg at (C,c) is c. Small diagrams and essential smallness use universe u+1, as in
`IndHeartFullFaithfulnessAssertions` and def-weil-size-convention. The universal property
over the full essentially small category is equivalent to the one over a small skeleton.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical-presentation assertions for the coefficient ring object Λ on X.
Here IndCons is the replete filtered-colimit closure `ObjectProperty.ind`, as in
`det-ind-heart-full-faithfulness`. The category J(B) is the existing costructured-arrow
category of the constructible inclusion. Density at B means precisely that the cocone
with legs c at (C,c) is a colimit, rather than just that some colimit object is isomorphic
to B. The final clause applies to every small filtered constructible colimit presentation,
with the functor to J(B) induced by its specified cocone legs.
Source: blueprint sk-prop-ind-heart-canonical-presentation.md, entire statement
(blueprint: det-ind-heart-canonical-presentation). -/
def IndHeartCanonicalPresentationAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : Prop :=
  ∀ B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B →
    EssentiallySmall.{u + 1}
      (CostructuredArrow (ObjectProperty.ι (IsConstantModelConstructible Λ X)) B) ∧
    IsFiltered
      (CostructuredArrow (ObjectProperty.ι (IsConstantModelConstructible Λ X)) B) ∧
    (ObjectProperty.ι (IsConstantModelConstructible Λ X)).isDenseAt B ∧
    ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (pres : ObjectProperty.ColimitOfShape (IsConstantModelConstructible Λ X) I B),
      pres.toCostructuredArrow.Final

/-- For the two canonical condensed coefficient rings, every ind-constructible sheaf
has its canonical filtered presentation by all constructible objects mapping to it;
every small filtered constructible presentation induces a final functor to this category.
Source: blueprint sk-prop-ind-heart-canonical-presentation.md and its proof
(blueprint: det-ind-heart-canonical-presentation).

Proof (the node's four steps):
1. A field is Noetherian and its spectrum is quasi-compact. Finite type then makes X
Noetherian (lem-weil-pbc-finite-type-over-noetherian, Stacks 01T6). By
sk-lem-coefficient-heart(2), choose a small set of constructible representatives.
For each representative the maps to B form a set, in universe u+1 by the size convention.
Together these give representatives for J(B); every pair (C,c) is isomorphic over B to
one of them. Cocones extend uniquely from this small full subcategory.
2. Zero is constructible, giving an object of J(B). Extension closure gives the
constructible direct sum of any two domains and hence a common successor. For parallel
g,h over B, coker(g-h) is constructible by sk-lem-coefficient-heart(1). The map to B
factors through this cokernel, giving an equalizing successor. Thus J(B) is filtered.
3. Fix any small filtered presentation of B from det-ind-heart-full-faithfulness(2).
Enlarge the representatives by its small set of objects. Finite presentation in part (1)
of that node identifies Hom(C,B) with colim Hom(C,C_i): surjectivity factors each c,
and injectivity makes any two such factorizations eventually equal. For a general filtered
index category, equality in the set colimit is a finite zigzag; a common stage and
successive equalization of its finitely many arrows make the representatives equal.
Apply lem-weil-pbc-initial-functor-cofiltered-criterion to the opposite presentation
functor. Its two hypotheses are exactly these two facts, so the presentation functor
is final, for every presentation.
4. That criterion also gives existence of the colimit over the small representatives
and its isomorphism with B (Stacks 04E7). The tautological cocone induces a map back to B.
Its composite with the comparison fixes every presentation leg, so colimit uniqueness
makes it the inverse comparison. Extend cocones from the representatives to all of J(B).
This proves precisely the tautological colimit, without assuming its existence. -/
theorem indHeart_canonicalPresentation
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hne : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      IndHeartCanonicalPresentationAssertions (Profinite.continuousMapRingObj.{u} E) X) ∧
    IndHeartCanonicalPresentationAssertions (Profinite.padicAlgClRingObj.{u} ℓ) X := by
  sorry

end AlgebraicGeometry.ProEtale
