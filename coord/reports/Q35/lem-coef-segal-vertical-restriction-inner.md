## Worker report

The module `Sheaf.AlgebraicTopology.SegalVerticalRestrictionInner` states
`SSet.segal_vertical_restriction_inner`. Its sole theorem has proof `sorry`.
Two real helper constructions belong to this node's own displayed definition of W/T:
`SSet.segalVerticalDivision` and `SSet.segalVerticalRestriction`. Both use Mathlib's
co-Yoneda functor, with no choice of data and no postponed construction proof.
The node copy changes only `lean`; there is no statement correction, dependency
repair, new node, or disputed statement.

Clause-by-clause correspondence:

- Small simplicial sets and a simplicial space W are rendered by the explicit universe
  `u` and `(W : SimplexCategoryᵒᵖ ⥤ SSet.{u})`.
- Reedy fibrancy is `hReedy : Reedy.rightClass (monomorphisms SimplexCategory).op
  (fibrations SSet.{u}) (terminal.from W)`. The negative arrows of the opposite
  simplex Reedy structure are opposites of injections. The dependency's relative
  matching construction applied to the terminal map is exactly the Reedy fibrancy
  test, with no alternative model structure assumed.
- The homotopy Segal hypothesis is exactly
  `hSegal : HomotopySegal.IsHomotopySegalSpace W`. This retains levelwise Kan and
  all weak homotopy equivalences of the canonical consecutive-edge constant-path
  comparisons into the path-model homotopy products, in every degree at least two.
- The displayed ordinary set `(W/T)_p = Hom(T,W_p)` is the actual object part of
  `segalVerticalDivision W T := W ⋙ coyoneda.obj (op T)`.
  Its action on an outer operator a sends f to `f ≫ W.map a`. It is a simplicial
  set of ordinary maps, rather than the vertical internal hom `(ihom T).obj W_p`.
- The first conclusion is `(∀ T : SSet.{u}, Quasicategory
  (segalVerticalDivision W T))`. It quantifies over every T, including empty and
  non-Kan simplicial sets.
- The map v is quantified by `∀ (S T : SSet.{u}) (v : S ⟶ T)` and the exact
  degreewise injectivity hypothesis is
  `(∀ n : SimplexCategoryᵒᵖ, Function.Injective (v.app n))`.
- Restriction is the canonical map `segalVerticalRestriction W v :=
  Functor.whiskerLeft W (coyoneda.map v.op)`. In degree p it sends f to `v ≫ f`.
- The second conclusion is `InnerFibration (segalVerticalRestriction W v)`.
  Mathlib defines this as right lifting against precisely the inner horn inclusions:
  all commutative squares with `Λ_i^n → Δ^n`, `0 < i < n`, have a diagonal filler.
  No completeness hypothesis, and no Kan or nonemptiness hypothesis on S or T,
  occurs anywhere in the signature.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones` (recorded declaration
  `SSet.Enhanced.coneCategory`) explicitly reuses Mathlib's `SSet`, `horn`,
  `stdSimplex`, `Quasicategory`, and `KanComplex`; the last quasicategory primitive
  supplies the first conclusion. Its definitions and source convention were read.
- `Sheaf.CategoryTheory.ReedyModelStructure`,
  `HomotopicalAlgebra.Reedy.model_structure`, with its `rightClass`,
  `relativeMatching`, `matchingFrom` and `simplex_reedy_structure`, supplies the
  relative matching test. The declaration signatures and docstrings were read.
- `Sheaf.CategoryTheory.SegalDKDiagonalEquivalence`,
  `SSet.segal_dk_diagonal_equivalence`, publicly imports
  `Sheaf.CategoryTheory.HomotopySegalSpace`. The reused definition is
  `SSet.HomotopySegal.IsHomotopySegalSpace`; its full definition, path target,
  canonical comparison and docstrings were read. The DK theorem is not assumed
  as a hypothesis; its recorded homotopy-Segal convention is used as the node asks.
- `Mathlib.CategoryTheory.Yoneda`, `CategoryTheory.coyoneda`, supplies both helper
  constructions. `Mathlib.AlgebraicTopology.Quasicategory.InnerFibration`,
  `SSet.InnerFibration`, `innerFibrations`, and `innerHornInclusions`, supplies the
  second conclusion, with its explicit inner-horn family read in source.

The stated proof dependencies are imported privately when they are not needed in the
signature: `Sheaf.AlgebraicTopology.KanPullbackPathComparison`
(`SSet.Enhanced.kan_pullback_path_comparison`),
`Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`
(`SSet.Enhanced.kan_homotopy_pullback_invariance`),
`Sheaf.AlgebraicTopology.KanQuillenRightProper`
(`SSet.KanQuillen.right_proper_kan_quillen`),
`Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`
(`CategoryTheory.MorphismProperty.llp_isStableUnderRetracts`,
`llp_isStableUnderCobaseChange`, `llp_isMultiplicative`), and
`Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`
(`CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp`).
There are currently no recorded modules for
`lem-coef-bisimplicial-reedy-division-calculus` or
`lem-coef-spine-cancellation-inner-horns`; no imports for those unstated proof-only
nodes can be added. They are named in the theorem's complete seven-step proof
plan. Neither is needed to type this stage-2 statement. No import cycle is introduced.

Edge cases checked before writing:

- If W is empty in every degree, it is Reedy fibrant and homotopy Segal. Division
  by empty T is terminal; division by nonempty T is empty. Both are quasicategories,
  and restriction is either an identity or the empty-to-terminal inner fibration.
- For any W, division by empty T has exactly one simplex in every degree. Taking
  S empty gives the terminal-map test for the first conclusion, as in source
  Corollary 3.6. No degree-zero nonemptiness is required by the horn conditions.
- Taking v the identity gives identity restriction. Empty S and T are allowed.
- The first inner horn is n = 2, i = 1. There is no inner-horn condition in degrees
  zero and one. Higher dimensions include every interior i.
- A discrete simplicial space on an ordinary nerve gives the expected functor
  simplicial sets; completeness is not forced by the signature. Non-Kan parameters
  such as Δ[1] are allowed.
- The one explicit, arbitrary universe u covers all small W, S and T in a fixed
  universe. The Hom sets are in the same universe u; no extra universe equality,
  finiteness, or inhabitance restriction is imposed.

Searches made:

- `msearch.py ... leanfinder`, query: “For a Reedy fibrant homotopy Segal space W
  the simplicial set with p simplices Hom(T,W_p) is a quasicategory and restriction
  along a monomorphism is an inner fibration”. Eight hits, principally ordinary
  nerves, `SSet.IsStrictSegal`, `StrictSegal.quasicategory` and `Quasicategory`.
  These concern single simplicial sets with strict Segal structure, not the stated
  bisimplicial homotopy-Segal restriction theorem. No exact match.
- `msearch.py ... loogle`, query `"InnerFibration"`: twelve hits defining inner
  fibrations and their stability, including `SSet.quasicategory_of_innerFibration`.
  None constructs this restriction or supplies its inner lifting property.
- `msearch.py ... grep`, query `SegalSpace|Rezk|InnerFibration`, subdirectory
  `AlgebraicTopology`: twelve hits on primitive inner fibrations and the ordinary
  simplicial internal-hom pushout-product theorem. That theorem assumes an inner
  fibration in one simplicial direction, which is the conclusion needed here.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf`, query
  `verticalDivision|verticalRestriction|segal.*inner|SegalSpace|ReedyFibrant`:
  existing strict Segal/Reedy interfaces and the homotopy Segal interface, with
  no vertical-division statement. `rg` for the exact node id in upstream has no hits.
- Read Mathlib's Quasicategory/Basic.lean, Quasicategory/InnerFibration.lean,
  CategoryTheory/Yoneda.lean and SimplicialSet/Basic.lean, and the project Segal
  interfaces. Co-Yoneda is reused directly rather than rebuilding its functor laws.
  The available division-calculus DAG node contains the general division notion
  but has no Lean record; the two small helpers here implement this item's own
  explicit map-set construction, not its independent division/lifting theorem.

Source verification: read the actual online Joyal–Tierney arXiv HTML,
https://arxiv.org/html/math/0607820, Section 2, Proposition 3.4(v),
Corollary 3.6 and Proposition 3.10. Proposition 3.4(v) gives inner restriction for
all monomorphisms; Corollary 3.6 gives every division quasicategorical. The path
Segal-to-strict-Segal conversion is exactly the node's proof steps 1–2, using the
recorded comparisons. WANTED: archive this paper in the project's literature;
the node itself already records that it is not archived. No source change is made.

Validation: `scompile.py Q35 lem-coef-segal-vertical-restriction-inner` compiled the
module cleanly, separately as a sandbox and library module, within the 60-second
limit. A separate sandbox probe checks by definitional equality the degreewise
Hom set, postcomposition operators, and precomposition restriction, and prints
the helper axioms and theorem signature. All three definitional checks passed;
both helpers depend only on propext, Classical.choice and Quot.sound. The delivered
module has no probe commands, no auto-implicit binders, no long lines and no
postponed definition data. The independent second reader supplies the second
reading section and performs delivery.

## Second reading by Q35

I reread the node statement, its source place, and the delivered module independently.
The node's objects and hypotheses match as follows:

- The small simplicial-space object is `W : SimplexCategoryᵒᵖ ⥤ SSet.{u}`. The module uses
  exactly this single universe `u`; no finiteness, inhabitance, or universe equality is added.
- Reedy fibrancy is the hypothesis
  `Reedy.rightClass (monomorphisms SimplexCategory).op (fibrations SSet.{u})
  (terminal.from W)`. This is precisely the opposite-injection relative-matching test
  from the recorded Reedy structure.
- The homotopy Segal hypothesis is exactly
  `HomotopySegal.IsHomotopySegalSpace W`, including levelwise Kan complexes and the
  canonical consecutive-edge homotopy-product weak equivalences.
- For each `T : SSet.{u}`, the module's
  `segalVerticalDivision W T := W ⋙ coyoneda.obj (op T)` has degree `p` equal to the
  ordinary simplicial-map set `T ⟶ W.obj p`; its operators postcompose by `W.map`.
  This is the node's ordinary map-set division, not a vertical internal hom.
- The first conclusion is exactly
  `∀ T : SSet.{u}, Quasicategory (segalVerticalDivision W T)`, including empty and
  non-Kan `T`.
- The restriction data are `S T : SSet.{u}`, `v : S ⟶ T`, and the exact hypothesis
  `∀ n : SimplexCategoryᵒᵖ, Function.Injective (v.app n)`. The module's
  `segalVerticalRestriction W v` is the canonical co-Yoneda precomposition map
  `W/T ⟶ W/S`.
- The final conclusion is exactly
  `InnerFibration (segalVerticalRestriction W v)`, hence the right lifting property
  against every `Λ_i^n ↪ Δ^n` with `0 < i < n`. No completeness or Kan hypothesis on
  `S` or `T` is present.

The source check was against Joyal--Tierney, *Quasi-categories vs Segal spaces*,
Proposition 3.4(v), Corollary 3.6, and Proposition 3.10 (online arXiv
math/0607820, Section 3). Proposition 3.4(v) gives the monomorphism restriction
mid-fibration, Corollary 3.6 gives `X/A` quasicategorical for every simplicial set
`A`, and Proposition 3.10 specializes to the terminal target to give the stated
inner-fibration restriction. The module's homotopy-Segal convention is the recorded
levelwise-Kan/weak-Segal-map convention used for this specialization.

Edge cases checked: `T = ∅` gives the terminal division; `W` empty in every degree,
`S = ∅`, identity `v`, and arbitrary non-Kan parameters are admitted; the empty
simplicial space and zero-dimensional outer degrees introduce no extra condition;
inner horns begin at `n = 2`, `i = 1`; all cases remain in the single explicit
universe `u`.

Searches were reread in `searches.jsonl`: LeanSearch, Loogle/LeanFinder, and grep
searches over Mathlib and both project/upstream trees found only primitive inner
fibration, strict-Segal, Reedy, and co-Yoneda declarations. No existing declaration
states this mixed homotopy-Segal vertical-division theorem, and the two helpers do
not duplicate a project or Mathlib notion. Dependency declarations and source files
for `def-cbc-enhanced-diagrams-cones`, `lem-coef-reedy-model-structure`, and
`lem-coef-segal-dk-diagonal-equivalence` were opened and their recorded interfaces
are the ones imported and used.

No mismatch was found, so no Lean or node repair was necessary. The only action was
this second-reading record. The module compiled cleanly with
`scompile.py Q35 lem-coef-segal-vertical-restriction-inner` (sandbox and library
compilations, no errors or warnings beyond permitted `sorry`).
