## Worker report

The module `Sheaf.Paper.DetIndHeartIISums` states
`AlgebraicGeometry.ProEtale.det_ind_heart_ii_sums` with proof `sorry`.  It uses
`CategoryTheory.Mod` for the category of module objects over the coefficient ring
object, `DerivedCategory.singleFunctor` to place module sheaves in degree zero,
and `shiftFunctor` for the integer shift.  An arbitrary coproduct is represented
by `c : Cofan B` with `hc : IsColimit c`; this is the categorical coproduct in the
ambient module category.  The displayed additive homomorphism is the direct-sum
map whose `s`-component is postcomposition with the shifted map induced by
`c.inj s`.  Its `Function.Bijective` conclusion is exactly that this natural map
is an isomorphism of abelian groups.

The hypotheses and clauses are rendered as follows.

* The prime and finite coefficient extension are `(ℓ : ℕ) [Fact ℓ.Prime]` and
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`.
* “Noetherian scheme” is represented by
  `(X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]`, i.e. locally
  Noetherian and quasi-compact, with no separatedness or finite-type hypothesis.
* The two coefficient choices are the sheaf variable `Λ`, the ring-object
  instances `[MonObj Λ] [IsCommMonObj Λ]`, and
  `hΛ : Λ = Profinite.continuousMapRingObj E ∨
  Λ = Profinite.padicAlgClRingObj ℓ`.  The canonical `padicAlgClRingObj` is the
  project’s formal realization of the fixed algebraic closure coefficient ring.
* The ambient category `Mod_{Λ_X}` is
  `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab) (condensedRingObj Λ X)`.
  The source object is `C` with
  `hC : IsConstantModelConstructible Λ X C`.
* The integer degree is `(q : ℤ)`.  The set-indexed family is
  `S : Type (u + 1)`, `B : S → CategoryTheory.Mod ...`, with
  `hB : ∀ s, ObjectProperty.ind (IsConstantModelConstructible Λ X) (B s)`.
  Thus every `B s` is a small filtered colimit of constructible sheaves in the
  ambient module category.
* `c : Cofan B` and `hc : IsColimit c` express the coproduct
  `⊕ s, B s`; the codomain of the displayed map is the shifted derived Hom from
  `C` to `c.pt`.  The direct-sum domain is the abelian-group sum of the shifted
  derived Hom groups.  The conclusion is `Function.Bijective` for this map.

The dependency declaration used for module objects is the exact Mathlib
`CategoryTheory.Mod` in `Mathlib.CategoryTheory.Monoidal.Mod`; it supplies the
module action, action-compatible morphisms, module category, and `Mod.forget`.
The other dependency declarations are `AlgebraicGeometry.IsLocallyNoetherian`
from `Mathlib.AlgebraicGeometry.Noetherian`, `CompactSpace` from
`Mathlib.Topology.Defs.Filter`, `AlgebraicGeometry.ProEtale.padicSubfieldRingObj`
and `padicAlgClRingObj` from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`,
`AlgebraicGeometry.ProEtale.IsConstantModelConstructible` from
`Sheaf.Paper.CondensedConstantConstructibility`, `ObjectProperty.ind` from
`Mathlib.CategoryTheory.ObjectProperty.Ind`, and `DerivedCategory` from
`Mathlib.Algebra.Homology.DerivedCategory.Basic`.  The finite-subextension and
algebraic-closure sheaves are used through their condensed forms
`Profinite.continuousMapRingObj E` and `Profinite.padicAlgClRingObj ℓ`, followed
by `condensedRingObj`.

The proof docstring follows the node’s three proof steps: finite biproduct
inverses; the filtered finite-subset presentation of a coproduct (including the
empty subset); and constructible Ext-continuity, which transports the compatible
finite inverses to the full coproduct.  No theorem is proved in this stage.

Edge cases checked: `S = Empty` (the initial coproduct and zero direct sum),
`S` a singleton, finite `S`, arbitrary infinite `S`, `q = 0`, negative and
positive `q`, zero source or summands, and the empty scheme.  No characteristic,
separatedness, or finite-type condition was added.  The finite coefficient and
canonical algebraic-closure choices are both retained.

Searches made:

* `msearch.py ... leanfinder "Ext out of a constructible sheaf commutes with sums of ind-constructible sheaves"`: only generic additive Ext declarations (`Ext.comp_sum`, `Ext.sum_comp`, `Ext.mk₀_sum`, etc.); no exact theorem.
* `msearch.py ... loogle "Ext, DirectSum, ObjectProperty.ind"`: no result; `ObjectProperty.ind` is not accepted by Loogle’s parser.
* `msearch.py ... grep "IndCons|constructible.*Ext|Ext.*sum" Mathlib/CategoryTheory`: no hits.
* `msearch.py ... grep "def Mod|Module objects" Mathlib/CategoryTheory/Monoidal`: no textual hit because the declaration is in the imported `Mod.lean` structure section.
* `msearch.py ... leanfinder "module objects over a monoid object in a monoidal category"`: found `CategoryTheory.ModObj`, `CategoryTheory.Mod`, `CategoryTheory.Mod.forget`, and related declarations; `CategoryTheory.Mod` was read in full and used directly.
* `msearch.py ... loogle "CategoryTheory.Mod"`: found the exact `CategoryTheory.Mod` declaration in `Mathlib.CategoryTheory.Monoidal.Mod` and its module-object documentation.
* `rg` over the source and project found no theorem named for this node.  It did find the generic finite-sum infrastructure and the existing `IndConstructibleFilteredColimits` module, which confirms that `ObjectProperty.ind` is the project’s IndCons encoding but does not state this Ext comparison.

No `STATEMENT-DISPUTED` flag is needed for the corrected node statement.  The
imported pre-correction statement was false without a Noetherian hypothesis; the
current node already records the source-based correction and its citer audit.

## Second reading by Q49

I reread the node and module independently.  The node’s locally Noetherian and
quasi-compact hypotheses match the two explicit typeclass binders.  The prime,
finite extension, both coefficient alternatives, coefficient ring object,
constructible source, arbitrary set-indexed IndCons family, integer degree, and
coproduct are each present.  `hΛ` keeps exactly the two coefficient choices;
`[MonObj Λ] [IsCommMonObj Λ]` records the ring-object structure required by the
node’s `Λ_X` clause.  The source and every summand are module objects in the same
sheaf module category.  The `Cofan` colimit supplies the categorical coproduct,
and the `DirectSum.toAddMonoid` map has precisely the shifted coprojection as its
component.  `Function.Bijective` therefore renders the requested isomorphism of
abelian groups.  The degree is an unrestricted integer, so no positive-degree
restriction was introduced.  Empty and zero cases remain included.  I found no
mismatch and made no further change.

## Dependency modules

The dependency node `sk-def-sfb-module-objects` had no recorded Lean declaration on the base.  Its notion is exactly Mathlib's `CategoryTheory.Mod` in `Mathlib.CategoryTheory.Monoidal.Mod`, whose structure `Mod (A : C) [MonObj A] where` packages an ambient object with a `ModObj` action; the Mathlib category and `Mod.forget` provide the action-compatible morphisms, category, forgetful functor, and regular module required by the node.  The dependency record therefore points to this existing declaration with a note explaining the exact specialization.
