# Worker report: lem-sfb-continuous-coefficient-free-rank

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-coefficient-free-rank.json`: statement node, now split; no exact Mathlib match. The statement, source, originating Q125 metadata, chapter and unit are retained.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `report.md`: this report. `searches.jsonl` was produced by the required msearch command.

New nodes: 0. New Mathlib leaves: 0. Every ingredient was already present in the DAG; elementary matrix calculations remain steps.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag and for continuous/free/rank combinations. `FieldCoefficient/UnitMatrix.lean` has the scalar-endomorphism and matrix calculations, and `FieldCoefficient/Abelian.lean:144,195` compares ranks of morphisms under changes of trivialization. These declarations concern the separate continuous-function coefficient implementation, rather than directly stating all clauses about internal modules over pulled-back condensed coefficients. No declaration found states this item exactly, so I do not claim ATTACH.

## WANTED

None. Hemo–Richarz–Scholbach, Example 3.1, p. 6, and the current blueprint rank proof are available and were read.

## What needed correction

The item was statement-only, not a split. There was no prior sandbox item or report to resume. Its mathematical statement is correct and is unchanged. In particular, no Noetherianity, connectedness, quasi-compactness or invertibility of ell has been added.

The blueprint first paragraph's field-valued-stalk wording is unnecessary and is not used: no assertion about all pro-etale stalks being fields is needed. The split constructs actual inverse finite matrices over global continuous sections and evaluates them at one ordinary topological point. This also makes the rank-zero case explicit.

The generic realization node is in another unit. It is declared in `split_report.tool_uses`: it supplies only the coefficient-ring identification, not a replacement for the unit's stratified-lattice or rank-descent route. The absolute-value, additive-category, dimension and independent-family nodes are existing Mathlib leaves or definitions. No unit realization field is changed: this is not the unit key node.

## Search and duplication review

I searched the full DAG by concept and statement and used `tools/blueprint_refs.py ancestor` and `search` for continuous functions, invariant basis, finite free, dimension, free rank, independent family, continuous coefficient free, finite free sheaves, and rank invariant. No other blueprint node states this exact rank comparison. The rank-descent parent is a stronger geometric assertion that uses this comparison and cannot be cited without circularity. The existing general ring realization and the existing ordinary-vector-space dimension/bound leaves suffice, so no new node duplicates them.

The original Q125 searches remain intact. I additionally ran the item searches through msearch: LeanFinder in two phrasings, Loogle, LeanSearch and source grep (two patterns). I read all hits. The candidate `SheafOfModules.freeHomEquiv` concerns global sections of a free module; `pullbackObjFreeIso` and `freeFunctorCompPullbackIso` concern preservation under pullback. Ordinary `Module.nonempty_linearEquiv_iff_rank_eq` / finite-rank equivalence and invariant-basis-number results become applicable only after the coefficient realization and matrix argument. I read the relevant source in `Algebra/Category/ModuleCat/Sheaf/Free.lean:62-68`, `PullbackFree.lean`, `LinearAlgebra/Dimension/Free.lean:231-247`, and `InvariantBasisNumber.lean:313-317`. This item is consequently not a one-line Mathlib specialization.

## Not duplicates

No new nodes were created; there are no new/existing-node pairs to distinguish.

## Review by Q153

I read Hemo–Richarz–Scholbach Example 3.1 on PDF p. 6, which identifies pulled-back condensed topological-ring coefficients with U ↦ continuous maps from |U|. I also read the current main-20261015 chapter, the sk-lem-stratified-lattice unit, its rank proof first paragraph, and the parent DAG split. The item's role is precisely that paragraph's assertion that transition isomorphisms preserve the ranks on a nonempty overlap. Below that assertion the following is an explicit agent argument; I have not attributed its matrix calculations to a nonexistent Stacks lemma. No SGA source is used.

For step 1 I opened `lem-weil-l-adic-extension-absolute-value` and checked that its hypotheses are exactly prime ell and finite E/Q_ell and that its conclusion supplies the nonarchimedean inequality. I wrote out why balls are clopen, giving total disconnectedness without silently assuming it. I opened `lem-sfb-continuous-ring-universe-realization`; its statement allows an arbitrary scheme and totally disconnected topological ring in the scheme universe, and expressly preserves multiplication and unit. Thus it supplies the ring-sheaf, rather than merely abelian-sheaf, isomorphism needed to transport the module action. Neither its statement nor this application imposes Noetherianity. Transport of the two inverse maps is conjugation along the coefficient isomorphism, retaining both inverse equations.

For step 2 I opened `sk-def-sfb-module-objects`: module morphisms preserve the action, and the regular module has its multiplication action. Addition of the underlying sheaf maps remains action-compatible by bilinearity. The finite coproduct projections are explicitly constructed by their values on the inclusions; testing the finite sum of inclusion/projection composites on each inclusion proves it is the identity. I also opened `def-weil-additive-category`; the displayed biproduct relations are exactly the relations used, not an unsupported claim about the existence of arbitrary products. These few universal-property calculations establish the finite coordinates directly. The empty coproduct and the zero identity are included.

For step 3 the only citation is again the actual module-morphism equation of `sk-def-sfb-module-objects`. Evaluating it on a pure tensor gives h(ab)=a h(b); substituting b=1 gives the scalar formula. The two equations BA=I_m and AB=I_n are derived by inserting the finite identity resolutions and expanding one component. This uses no exactness, stalk theorem or assertion about infinite direct sums. I checked the matrix indices: A has n rows and m columns; B has m rows and n columns.

Step 4 has no citations because it only uses the displayed matrices, pointwise ring operations, finite sums and the given nonempty |W|. Evaluation sends both inverse equations to inverse equations over E, and the stated matrix formulas explicitly give inverse linear maps. A chosen ordinary point of W suffices. This is not an appeal to a field-valued pro-etale stalk.

For step 5 I opened both `def-weil-vector-space-dimension` and `lem-weil-independent-family-card-le-dimension`. The first says the dimension is the cardinality of a finite basis; I exhibited and checked the coordinate basis rather than invoking an unnamed basis theorem. The second says a k-element linearly independent family in a finite-dimensional vector space has k at most its dimension. Its hypotheses hold for E^n and E^m by those coordinate bases. Applying the inverse matrix proves independence of the images; two applications give the two inequalities. I checked the pinned Mathlib source `LinearAlgebra/Dimension/Finite.lean:161` and `StrongRankCondition.lean:451` against these existing leaves.

I tested m=n=0, m=0<n, and n=0<m: in the unequal zero cases evaluation would force a positive-size identity matrix to be zero, or equivalently yield a positive integer at most zero in step 5. On the empty scheme all finite free sheaves would be zero, confirming why the nonemptiness hypothesis is needed. I also checked disconnected schemes, infinite disjoint unions (hence non-quasi-compact), nonreduced schemes, and characteristic ell: the argument still uses only one point and pointwise operations, so no forbidden geometric hypothesis appears. Every proof step is below 2000 characters and none hides a separate substantial lemma. I checked delivery-errors B–E: no new node, no duplicate or re-labelled clause, every non-elementary input has a node, every quote is from that node's actual statement, no target or unit route is weakened, no circular dependency is introduced, and no compiler or Lake tool was run.

## What could not be finished

Nothing in the mathematical split. Delivery validation is recorded below after the required dry run.
