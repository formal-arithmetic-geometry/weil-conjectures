## Worker report

The module `Sheaf.AlgebraicGeometry.DisjointClosedSubstacksAlgebraQuotient` states
`CategoryTheory.disjoint_closed_substacks_algebra_quotient`. The item statement and
all of its dependency lists and proof steps are unchanged. Its Lean record is the
only changed field. There are no new nodes or dependency repairs.

The section algebra is constructed, with real data, as compatible regular functions
on `CostructuredArrow W.inclusion.toFunctor x`. An object is a closed-substack
object z together with an arrow i(z) → x. Thus this is the category of test-scheme
objects over the closed base change, rather than a choice of a representing scheme.
`closedModuliSectionDiagram` uses exactly the existing structure presheaf of
`def-sfb-stack-quasi-coherent-algebra`. `closedModuliSectionRing` uses Mathlib's
`RingCat.sectionsSubring`; restrictions precompose families with
`CostructuredArrow.map`. The ring laws are pointwise. `closedModuliStructureMapApp`
pulls a function back along every comma arrow. Its data are explicit. Only its
compatibility, functor laws, naturality and sheafness are named theorem obligations.
`closedModuliAlgebra_sections` states the identification with Γ(Z,O_Z) for EVERY
scheme representing the specified 2-base change, using the recorded
`HasSchemeModuliBaseChange`. This comparison theorem chooses no data used in the
algebra construction. It is the section convention in the node, expressed without
choosing fibre-product representatives or forcing site universes equal.

Hypothesis and clause correspondence:

* The field is `(k : Type u) [Field k]`; the base is `Spec (.of k)`.
* The arbitrary algebraic stack is
  `F : BasedCategory.{v, w} (Over (Spec (.of k)))` with
  `hF : IsAlgebraicModuliStack F`. The independent object/morphism universes of F
  are retained, and coefficient rings lie in `max (u + 1) v w`, exactly as in
  the imported site convention. `hF.1.1` supplies its fibred-groupoid proof.
* The two closed substacks are `W₁ W₂ : ClosedModuliSubstack F`. This existing
  structure includes strict fullness, pullback stability, stack descent and the
  scheme-represented closed-immersion test. The inclusions are `W₁.inclusion`
  and `W₂.inclusion`; no independent atlas or representation is required.
* Disjoint underlying spaces are `hd : Disjoint (Set.range (moduliPointMap
  W₁.inclusion)) (Set.range (moduliPointMap W₂.inclusion))`. These are the actual
  images on the quotient of field-valued objects from the topology dependency.
* The value B_a(x) is `closedModuliAlgebra Wₐ hF.1.1`, with the explicit
  comma section construction above and the all-representatives section theorem.
  Restrictions are literal pullbacks, including arrows over nonflat scheme maps.
* Quasi-coherence of B₁ and B₂ is the first two conjuncts
  `IsQuasicoherentModuliAlgebra (closedModuliAlgebra Wₐ hF.1.1)`.
* Their product is `closedModuliProductAlgebra W₁ W₂ hF.1.1`, defined using
  Mathlib's existing binary product of commutative-ring sheaves and `prod.lift`
  of the two structure maps. Its underlying rings and operations are the product
  rings under the canonical projections. Quasi-coherence is the third conjunct.
* The canonical restriction map is the structure map `.hom` of that product,
  viewed by `Under.homMk` as a map of algebras from the identity structure algebra.
  Its two components are the constructed restriction maps by the product cone.
  `IsSurjectiveModuliAlgebra` is precisely local section lifting in the fppf
  topology, the fourth conjunct. No surjectivity on global sections is asserted.
* The last two universally quantified equations say that a global compatible
  family `s : moduliGlobalSectionsRing (moduliStructureSheaf F hF.1.1)`, when
  mapped and evaluated on any comma object, has value
  `s.1 (op (Wₐ.inclusion.obj i.left))`. This is its original component on the
  corresponding closed-substack object, exactly restriction to that substack.
  The binary product structure map therefore sends s to its two restrictions.
* There is no Noetherian, finite-type, reducedness, flatness or nonemptiness
  hypothesis anywhere in the theorem. The field characteristic is unrestricted.

Dependencies read and used:

* `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, line 180,
  the commutative ring with division and nontriviality structure.
* `def-sfb-algebraic-moduli-stack`: `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`,
  `CategoryTheory.IsAlgebraicModuliStack`, including its fibred-groupoid component.
* `lem-sfb-invariant-closed-substack-descent`:
  `Sheaf.AlgebraicGeometry.InvariantClosedSubstackDescent`,
  `CategoryTheory.invariantClosedSubstackDescent`. Its public dependency
  `Sheaf.AlgebraicGeometry.ClosedModuliSubstack` supplies
  `ClosedModuliSubstack`, `.inclusion`, and `HasSchemeModuliBaseChange`.
  I read their complete definitions, including the projection normalization.
* `lem-sfb-smooth-presentation-closed-subsets`:
  `Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets`,
  `CategoryTheory.smooth_presentation_closed_subsets` and its imported
  `ModuliPoints` / `moduliPointMap`. The supports use these actual point maps.
* `def-sfb-stack-quasi-coherent-algebra`:
  `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`,
  `moduliStructurePresheaf`, `moduliStructureSheaf`, `ModuliAlgebraSheaf`,
  `IsQuasicoherentModuliAlgebra`, `IsSurjectiveModuliAlgebra`, and
  `moduliGlobalSectionsRing`. The whole source module was read. No site,
  structure sheaf, quasi-coherence or surjectivity predicate is privately copied.
* Proof-only imports retain the plan:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
  (`Scheme.Modules.tensorPullbackSectionAdjunction` and `tensorPullback`),
  `WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange`
  (`Scheme.Modules.affinePushforward_baseChange`, its algebra and composition
  clauses), and
  `WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension`
  (`Scheme.Modules.isQuasicoherent_biprod`). Their signatures and docstrings
  were read. `AlgebraicGeometry.IsClosedImmersion` is already publicly imported
  through the closed-substack dependency. The proof dependency
  `lem-sfb-cartesian-module-fppf-realization` has no recorded module/declaration,
  so there is no import to add for it; no such interface is needed to TYPE the
  present statement. It remains a named step of the postponed proof, unchanged.

The theorem docstring carries all five proof steps: affine quotient/base change,
cartesian realization, binary sum/product, lifting on the complementary affine
opens, and global-function compatibility. Helper theorem docstrings state the
part of this construction they express and give its complete argument.
Every theorem in the delivery has proof `by sorry`. Definitions contain genuine
ring/family/map/product data; their required mathematical proofs are named
separately. All 14 declarations are listed in `lean.declarations`.

Sources opened: Stacks `stacks-sheaves.tex` Tag 06WK, statement and full proof,
Tag 06WT, proposition and its construction; `stacks-properties.tex` Tag 0507;
`morphisms.tex` Tag 01QQ; `algebra.tex` Tag 00DT, statement and proof. The item
is an agent-formulated consequence, not a direct restatement of just 06WT.
No source correction is needed.

Edge cases checked mathematically:

* Empty ambient stack: the global function family and support hypotheses have
  their empty-site meanings; no object/nonempty binder excludes this case.
* One closed substack empty: its comma categories have no objects and the ring
  of compatible families is the zero ring, so the product reduces to the other
  quotient. The formulas still hold. Both empty also works.
* Equal nonempty closed substacks do not satisfy hd; for Spec k in itself the
  diagonal k → k×k is not surjective, confirming why disjointness is essential.
* On A¹, V(t) and V(t−1) give the two evaluation quotient maps. Nilpotent
  thickened closed subschemes are retained because ClosedModuliSubstack stores
  closed-immersion scheme tests, not only point subsets.
* Nonaffine T needs only local lifting; no false global-section-surjectivity
  clause was added. Arbitrary nonflat arrows remain in the presheaf category.
* Arbitrary ideals and arbitrary field characteristic remain allowed.

Searches actually run (also recorded by the prescribed wrapper in searches.jsonl):

* LeanFinder, "Two disjoint closed substacks have a quasi coherent product
  structure algebra quotient": eight scheme quasi-separatedness/coproduct hits,
  none states the stack algebra quotient theorem.
* Loogle, "AlgebraicGeometry.IsClosedImmersion, CategoryTheory.Sheaf": zero hits.
* Mathlib grep, "closedSubstack|ClosedModuliSubstack|disjoint.*[Aa]lgebra",
  AlgebraicGeometry: zero hits.
* LeanSearch, "Disjoint closed substacks give a locally surjective quasi coherent
  structure algebra product quotient": eight hits, including
  `TopCat.Sheaf.isProductOfDisjoint` and scheme closed immersions/coproducts;
  none gives the general stack statement.
* Local rg over both `lean/Sheaf` and `lean/WeilConjectures` for closed-substack
  and disjoint-algebra names found the existing ClosedModuliSubstack and the two
  downstream uses in adequate-moduli proofs. No declaration states this item.
  Exact item-id search in `lean/WeilConjectures` gave no match.
* Fresh helper names were searched in Mathlib, WeilConjectures and Sheaf;
  there were no existing declarations with these names. The upstream-name
  index was searched for the relevant module-pullback and new construction names.

Validation: prescribed `scompile.py` passed both sandbox and actual module-name
compilation (8.7 s and 8.8 s on the successful run), with no errors or warnings
other than the allowed postponed-proof diagnostics. No local/global build and
no direct Git command was run. All writing was confined to the assigned sandbox.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
