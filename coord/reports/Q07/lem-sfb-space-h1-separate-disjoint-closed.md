## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceH1SeparateClosed` states
`AlgebraicGeometry.AlgebraicSpace.exists_global_function_separating_closed`, with its
single proof `sorry`. It formalizes Stacks Project, Spaces Cohomology, Tag 07V1
(lemma-vanishing-separate-closed) under Situation 07UY. Both passages were read in
`literature/stacks-project/spaces-cohomology.tex`, lines 2773–2780 and 2854–2878.
The node's statement and proof are unchanged. Its `stmt_deps` gains the already-landed
`def-sfb-space-absolute-quasi-separated`, whose interface expresses the absolute
diagonal condition, including over a base which is not quasi-separated.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary scheme base is `{S : Scheme.{u}}`; `X : AlgebraicSpace S` is the
  existing full subcategory of fppf sheaves with representable diagonal and an etale
  surjective scheme atlas. There is no absolute base restriction to Spec Z.
- The field-valued point classes are `Point X.obj.obj`. Their topology is the existing
  `pointTopologicalSpace`, the final topology for all etale scheme charts.
- Quasi-compactness is `hqc : CompactSpace (Point X.obj.obj)`.
- Absolute quasi-separatedness is `hqs : IsAbsolutelyQuasiSeparated X`. This existing
  predicate says that the fibre product of any two affine scheme charts has compact
  point space, the affine-test criterion for the absolute diagonal to be quasi-compact.
  This does not replace absolute quasi-separatedness by quasi-separatedness over S.
- Quasi-coherent modules are the actual `F : X.Modules` with `F.IsQuasicoherent`,
  Mathlib's locally presented module-sheaf predicate, using the specialization
  instances in `AlgebraicSpaceQuasiCoherentModule`. The structure sheaf and site are
  exactly the recorded small etale ones.
- `hH` quantifies over every such F, and asks that first cohomology of its underlying
  additive sheaf be `Subsingleton`. This is exactly vanishing of an abelian group.
  Forgetting the module structure is `(SheafOfModules.toSheaf X.structureSheaf).obj F`.
  Before `Sheaf.H`, `sheafCompose ... AddCommGrpCat.uliftFunctor.{u + 1, u}` applies the
  canonical carrier lift, with unchanged group operations and restriction maps on
  descended elements. This makes sheafification available on the site of object
  universe u+1. `HasExt.standard _` supplies the standard Ext realization explicitly;
  it is a closed Mathlib theorem, not an added assumption. Carrier lifting does not
  change sheaf cohomology: an affine-etale small basis computes both, and ordinary
  ULift is an equivalence on the groups in that computation. The hypothesis is the
  cohomology of the underlying additive sheaf, not derived sections in module sheaves.
- The subsets are arbitrary `Z₀ Z₁ : Set (Point X.obj.obj)`. Closedness is `hZ₀` and
  `hZ₁`; their disjointness is `hdisj : Disjoint Z₀ Z₁`. No nonemptiness is assumed.
- The conclusion chooses `a : RingCat.sectionsSubring X.structurePresheaf`. This is
  exactly a family of regular functions on all small etale charts, compatible with
  every restriction, hence Gamma(X,O_X). It is Mathlib's existing sections construction,
  not a new or hollow definition and not an arbitrary abstract ring presentation.
- The first conjunct says that for every etale chart T and point x whose image
  `schemePointMap T.obj.hom x` lies in Z₀, residue-field evaluation
  `(X.etaleForget.obj T).Γevaluation x (a.val (op T))` is zero.
- The second conjunct is the identical condition on Z₁ for `(a - 1).val (op T)`.
  Thus these are precisely Z₀ contained in V(a) and Z₁ contained in V(a-1).
  Subtraction is in the actual compatible-sections ring, so the unit and all its
  restrictions are the structure-sheaf unit.

Why the chart formulation is the node's field-valued zero locus: `schemePointMap`
uses the residue-field representative of x. Every point class lifts to an etale
scheme atlas. Given any other field-valued representative, base change that atlas
to its field spectrum, and choose a point of its nonempty etale cover. The compatible
chart section evaluates after the resulting field extension to the original section's
value. The extension is injective, so zero there is equivalent to zero before extension.
Common extensions compare two representatives in the quotient relation. Consequently
vanishing is independent of the representative, and testing every chart point gives
exactly the two stated subset inclusions. No extra vanishing outside the specified
closed sets, or equality of global sections with zero/one on their reduced structures,
is required in the conclusion.

Recorded statement-dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleForget`, `structurePresheaf`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  and the imported `Point`, `schemePointMap` from `AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  specialization instances; the predicate is the same `SheafOfModules.IsQuasicoherent`
  used by that full subcategory, not a replacement definition.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`, with
  its documented retention of Mathlib `Sheaf` and `Sheaf.H` cohomology conventions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated` (the additional existing statement dependency).

Further Mathlib interfaces read: `RingCat.sectionsSubring` (Ring/Limits),
`Scheme.Γevaluation` (ResidueField), `Sheaf.H` and its full signature
(Sites/SheafCohomology/Basic), `HasExt.standard` (DerivedCategory/Ext/Basic),
`AddCommGrpCat.uliftFunctor` and its limit-preservation interface (Grp/Ulift).

Plain proof imports cover every currently recorded proof dependency with a usable
module: `ReducedClosedSubspaceSupport`, `AlgebraicSpaceClosedPushforwardStalks`,
`RingedSiteModules`, `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`,
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`,
`Mathlib.CategoryTheory.Abelian.RightDerived`, `AlgebraicSpaceModuleOperations`, and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`. The quasi-coherent predicate's
module is already a public import. The still-unstated proof dependencies
`lem-sfb-space-closed-immersion-quasi-coherent-modules`,
`lem-sfb-space-etale-conservative-geometric-points`, and
`lem-sfb-space-qcoh-kernels-colimits` have no recorded Lean module to import;
they remain proof dependencies and are named in the proof docstring.

Edge cases checked before writing:

- Z₀ empty: the compatible unit section works; the first condition is vacuous.
- Z₁ empty: the compatible zero section works; the second condition is vacuous.
- Both empty, and X empty: either section works, without a nonempty point or chart
  assumption; on empty chart schemes there are no points to test.
- Disconnected and nonreduced spaces: only values in residue fields are prescribed,
  so no stronger global equality or unwarranted reducedness hypothesis is introduced.
- Arbitrary base S, including one which is not quasi-separated: absolute
  quasi-separatedness is retained via its existing affine-test definition.
- All characteristics, all universes u, arbitrary cardinalities of presentations:
  no finite presentation, field characteristic, or equality of distinct universes is
  imposed. The coefficient lift is canonical and does not lift or alter the module F.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “Vanishing first cohomology of quasi-coherent modules
  separates disjoint closed subsets of an algebraic space by a global function zero
  and one”. Eight results, led by `exists_of_res_zero_of_qcqs_of_top` and
  `exists_of_res_zero_of_qcqs`; these clear powers in scheme sections and do not state
  the separation theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry, IsClosed, Sheaf.H` returned zero hits
  with an unknown-identifier diagnostic. A second query `IsClosed, Disjoint` returned
  twelve topology results about compact closed families and separated neighbourhoods;
  none supplies a regular function or a cohomological criterion.
- `msearch.py ... grep`: `separate.*closed|closed.*separat` under AlgebraicGeometry
  returned eleven results, concerning separated morphisms and closed diagonals only.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for separation, global sections,
  cohomology and algebraic-space interfaces located the existing qcqs and sections
  ingredients and the sibling `AlgebraicSpaceH1AffineBaseChange`, but no theorem
  separating disjoint closed subsets from H1 vanishing. Exact item-id search in the
  upstream Lean sources returned no declaration.

No statement dispute, correction, new definition node, or dependency repair is needed.
The sole added statement dependency already has its recorded Lean interface.
Compilation uses only the prescribed `scompile.py`, against the live server build.
The final module passed both sandbox and library checks without errors or warnings.

## Second reading by Q07

This is a separate rereading by the same dispatcher-started worker; no independent
reader or sub-agent was started. The maintainer performs the independent review.
I reopened the node and final module and checked the arbitrary S and X binders,
compact point space, absolute quasi-separatedness, universal quasi-coherent H1
vanishing, the two arbitrary closed sets and their disjointness, the genuine
compatible global function, and both zero-locus clauses against the correspondence
above. All are present. In particular, the two chart conditions impose pointwise
residue-field zero on a and a-1, exactly the specified V conditions; neither forces
a stronger equality on a nonreduced closed thickening. The canonical coefficient
lift avoids adding sheafification or Ext hypotheses. There are no free universes,
auto-bound variables, diagnostic commands, local notation, local instances, helper
sorries, or extra conclusions. The final proof is one `sorry` with the complete
source proof plan in its docstring. No mismatch requiring a statement change was found.
