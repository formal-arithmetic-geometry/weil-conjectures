## Worker report

The module imports the finite split etale hypercover and finite-data descent declarations. It states the descent theorem with the inverse-system hypotheses and limit cone. The formal conclusion is currently `True`; this is a known statement fault requiring repair by the lead/second reader because the source requires explicit descent clauses for truncations, morphisms, equalities, and matching covers.

Dependencies used: `Sheaf.Paper.FiniteSplitEtaleHypercover`, declaration `AlgebraicGeometry.FiniteSplitEtaleHypercover`; `Sheaf.Paper.EtaleFiniteDataDescent`, declaration `AlgebraicGeometry.etale_finite_data_descent`.

Searches: rg for hypercover descent in project (found only FiniteSplitEtaleHypercover); node/dependency records inspected; Mathlib/source search found no existing theorem with this node statement.

Historical worker concern (resolved by the second reading below): the available tuple truncation lacked an independently typed stage model; the placeholder required correction.

## Earlier second reading (a previous round; superseded)

The module compiles locally. The placeholder conclusion is flagged above for correction; no proof is claimed.

## Second reading by M1

I opened the item JSON, both statement dependencies (including the scheme-conventions
node in sec-nagata-compactification), the complete FiniteSplitEtaleHypercover module,
and EtaleFiniteDataDescent. I read Stacks limits.tex, lemma-descend-finite-presentation
(01ZM), lines 2370 onward, and etale-cohomology.tex, lemma-colimit-affine-sites (0EYL),
lines 7336 onward. The local literature checkout is absent; the cited Stacks .tex files
were fetched into the item's scratchpad from the Stacks project's source repository.
01ZM explicitly assumes a directed inverse system, affine transitions, and qcqs stages;
0EYL's qcqs case explains eventual descent of covering families. I also read the
stage-1 report of E1 to distinguish the node's Detailed form from the earlier
refinement-existence paragraph. No change to the node's natural-language statement
or to a unit statement was required.

The node's objects, hypotheses and conclusions, matched individually:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Cofiltered inverse system of schemes | `I : Type w`, `[SmallCategory I] [IsFiltered I]`, `D : Iᵒᵖ ⥤ Scheme.{w}` | Exact: the diagram category is cofiltered, not restricted to preorders. |
| Affine transition maps | `[∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]` | Exact, on every transition. |
| Quasi-compact stages | `[∀ i, CompactSpace (D.obj i)]` | Exact, Mathlib's scheme convention. |
| Quasi-separated stages | `[∀ i, QuasiSeparatedSpace (D.obj i)]` | Exact; no separated or Noetherian hypothesis. |
| Limit scheme X and projection maps | `(c : Cone D) (hc : IsLimit c)` and `c.pt`, `c.π.app i` | Exact; no extra instance on X. |
| Each nonnegative truncation degree | `∀ r : ℕ` in all three conjuncts | Exact, includes zero. |
| Finite split étale hypercover through degree r | `TruncatedFiniteSplitEtaleHypercover c.pt r` | Exact independent finite truncation; see dependency audit below. |
| Descent of the truncation to one stage | `∃ i Ui, Ui.IsBaseChange (c.π.app i) U ∧ ...` | Exact; comparison retains the chosen splitting, not just underlying terms. |
| Descended matching arrows are covers sufficiently late | `Ui.matching_cover` and `∀ j h n, Surjective (...) .left` | The chosen i is already sufficiently late; covers persist by base change. Étaleness is built into the matching arrows in the small étale category. |
| Every morphism between truncations descends | Second conjunct: stage models U,V, arbitrary natural transformation φ after limit pullback; `∃ j h ψ` with componentwise comparison equations | Exact 01ZM (2), including all face, degeneracy and augmentation compatibilities. Arbitrary limit truncations are covered by the first clause and a common stage. |
| Every equality between morphisms descends | Third conjunct: stage morphisms φ,ψ, equality of their limit pullbacks implies equality at `∃ j h` | Exact 01ZM (3); equality is equality of natural transformations, not equality of individual unconstrained maps. |
| Quantifier order and common stage | Each existential stage follows the supplied finite datum; `j ⟶ i` specifies a later stage | Exact. Finitely many data can be combined at a common stage by filteredness. |

Dependency audit (H4/H12/H13): the scheme-conventions node is a collection of
Mathlib meanings, not a missing scheme definition. The recorded full hypercover
structure does match its node: simplicial object in X.Etale, canonical Mathlib
Splitting, matching universal property over ALL `T : Over X`, surjective matching
arrows, finite coproducts of qcqs étale fp nondegenerate pieces. Its recorded
`truncation`, however, is a tuple extracted from a FULL hypercover and provides
no independently constructible finite-stage truncated type. Requiring a full
hypercover at the stage would silently require descent of infinitely many degrees.
This is a missing part of that existing dependency node's truncation clause,
not a new DAG notion. I therefore deliver a dependency module for
`def-weil-pbc-finite-split-hypercover`, retaining every existing declaration verbatim
and adding the typed finite truncation and its diagram/base-change comparison.

The added structure uses Mathlib `SimplicialObject.Truncated`, so its functor laws
are exactly all retained simplicial identities. `N : Fin (r+1) → X.Etale` and
`inclusion` specify retained nondegenerate pieces. The splitting cofan uses the
same order-preserving epimorphisms as Mathlib `Splitting.IndexSet`; its targets
are bounded by r, and an epimorphism automatically has target degree no greater
than its source. Consequently there are neither missing degeneracies nor extra
summands. `IsColimit` of the canonical inclusion-followed-by-degeneracy cofan
is the splitting condition, not an arbitrary coproduct isomorphism. The finite
component condition is copied from the full dependency. The matching fields are
its original universal property restricted to retained degrees and tested on ALL
schemes over X. `matchingMap_projection` makes each matching arrow canonical.
`IsBaseChange` gives a natural isomorphism of diagrams AND compatible isomorphisms
of chosen nondegenerate pieces. It therefore identifies their degeneracy cofans;
matching schemes, projections and matching arrows are identified uniquely by the
universal property. There is no arbitrary predicate standing in for descent and
no forgotten splitting clause. Refinements themselves remain arbitrary augmented
simplicial maps, as in the recorded dependency's `Refinement`; they do not have
to preserve the chosen splitting.

Edge cases: r=0 retains N_0, U_0 and the augmentation; the matching universal
property has an empty lower-degree diagram, so M_0 is X and the cover is the
augmentation. Fin k admits k=0: empty nondegenerate summands and empty schemes
are not excluded. Surjectivity onto an empty matching scheme has the usual
meaning. No point of the limit is assumed. Empty indexing categories are
excluded by cofilteredness itself, exactly as in the node, not by an extra
hypothesis. No coefficient group, nonzero object, field, characteristic or
Noetherian assumption is introduced. Scheme and index universes are uniformly
polymorphic, with indices in the schemes' universe as required by the contract;
all universes and variables are explicitly bound. The extra truncation structure
does not require a qcqs instance on the limit, so no instance is silently added.

Independent searches (different wording from the worker): LeanSearch query
`Descent of a truncated split simplicial etale hypercover along an inverse limit
of schemes` returned service unavailable, recorded without a mathematical verdict.
LeanFinder query `Finite split truncated etale hypercovers descend to a stage of
an inverse limit` returned OneHypercover homotopy, étale-algebra products and
scheme gluing, none this statement or definition. Loogle `SimplicialObject.Truncated`
reported unknown identifier; the follow-up `"truncation"` found Mathlib's simplicial
and cosimplicial truncation functors, which are used here, but no étale finite split
truncation with matching data or descent. msearch grep
`hypercover.*descen|truncated.*split|split.*truncated` found only an unrelated
set-family lemma. Direct rg on Mathlib, the project's Lean, the source's
WeilConjectures, and the DAG for `TruncatedFinite|FiniteSplit.*Trunc|hypercover.*descen`
found the existing full hypercover node/module, this item, and its citers, not an
alternative typed truncation or an exact descent declaration. Search queries and
service results are recorded in searches.jsonl. No existing declaration realizes
the whole item; no new definition node was created.

Mismatches repaired: the original `True` omitted EVERY conclusion and did not
introduce r or hypercover data. Replaced it with explicit object, morphism and
equality descent. Added the missing independent truncated type in the existing
dependency, rather than privately copying its full hypercover. Removed the unused
finite-data-descent import; used the filtered category definition directly.
Generalized the worker's preorder indexing to arbitrary small filtered categories.
Added the conventional copyright header. Expanded the theorem docstring to the
node's three proof steps, including eventual covers and the two distinct
morphism/equality clauses. Updated both Lean records from parsed signatures.
The worker's statement dispute is resolved by these repairs; it was about the
placeholder Lean, not a defect of the node's mathematics.

Validation: both modules compiled together locally with the prescribed
lcompile.py, relaxedAutoImplicit=false and autoImplicit=false, no errors or
warnings. There is exactly one theorem with proof `sorry`, the item's statement;
no result is proved and no definition uses `sorry`. No file-local notation,
private definition, local instance, hidden let or unbound variable is used.

## Dependency modules

- `def-weil-pbc-finite-split-hypercover`: Sheaf.Paper.FiniteSplitEtaleHypercover;
  preserve the full hypercover and all previous declarations, add the independently
  typed finite truncation needed for the dependency's existing truncation clause.
  The node changes only in lean, with the required explanatory note.
