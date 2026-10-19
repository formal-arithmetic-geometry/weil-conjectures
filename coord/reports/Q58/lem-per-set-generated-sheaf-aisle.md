# Worker report — Q58

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-set-generated-sheaf-aisle.json`: item, split; unchanged statement, nine proof steps, no Mathlib match for the whole assertion.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-preaisle-transfinite-monomorphism-closure.json`: new statement-only lemma; no Mathlib match after LeanFinder, LeanSearch, Loogle and source grep. It states closure for arbitrary continuous monomorphic filtrations, not existence of truncation triangles or a generator test.
- `citations.json`: every step/node pair has a verbatim quote from the statement read. The quotes include whole statements so their hypotheses remain visible.

The previous sandbox had only an unchanged unsplit item and twelve search result files, not a report, split, citations or a delivery result. I retained those files, inherited searches and `searches.jsonl`. No interrupted delivery invocation was present in the supplied tool context, and the sandbox was not ready for a prior delivery. No Lean was written or compiled; no git command was run in the shared repository.

## Attachments

None for the item. The existing `SheafOfModules.isGrothendieckAbelian` belongs to the already attached `lem-weil-pbc-ring-sheaves-grothendieck`, which is reused rather than recreated. Searches under the read-only `WeilConjectures/` for the item tag, preaisle, aisle, generated t-structure and the conceptual variants found no declaration stating the item. The K-injective declarations found there concern only the reused foundations.

## Wanted literature

WANTED: a source for cocomplete preaisles in the unbounded derived category of a Grothendieck abelian category being closed under filtered homotopy colimits, hence continuous transfinite extensions; for `lem-per-preaisle-transfinite-monomorphism-closure`. The source should include unbounded complexes and arbitrary small ordinal lengths, not just a sequential telescope or compact generators. The general set-generated t-structure reference, for comparison, is Lurie, Higher Algebra, Proposition 1.4.4.11; it is not archived here and is not used as a substitute for the proof.

## Problems found and changes

The inherited item is a true agent-formulated auxiliary theorem; ILO XVII 5.2 (printed p. 287, PDF p. 293) states Gabber's geometric perversity t-structure but does not prove this arbitrary-site set-generated-aisle theorem. I read that paragraph and do not attribute a cellular proof to it. The proof is marked `by: agent`. No statement correction is needed. Arbitrary ring sheaves are retained, including noncommutative ones; no compactness, boundedness, enough-projectives or finiteness assumption was added.

An injective model structure would be unnecessarily broad. The old exploratory searches for one are retained, but the split constructs a set of disk and identity-cone tests directly using existing Stacks nodes. The only new lemma concerns a real limit-stage issue: a countable telescope alone cannot justify an arbitrary uncountable cellular filtration. Conversely moving the whole set-generated aisle theorem into another node would not split the item. The nine steps carry the truncation construction themselves.

The item is below the fixed perverse-curve route through the imported ancestor/via chain, not the statement node of its unit. No chapter or unit fields were changed. Off-unit general inputs are declared in `split_report.tool_uses`; no maintainer-owned `tool_uses` field was set. None of the proof uses SGA.

## Not duplicates

`lem-per-preaisle-transfinite-monomorphism-closure` vs `lem-kun-complex-colimit-hocolim`: the existing node is a sequential telescope identity for module sheaves over a commutative ring; the new node concerns membership in a general cocomplete preaisle along arbitrary small ordinals in any Grothendieck abelian category. The latter cannot be obtained by applying that sequential identity at an ordinal of uncountable cofinality.

`lem-per-preaisle-transfinite-monomorphism-closure` vs `lem-per-etale-support-aisle-generators`: the existing node identifies one geometric support class with a generated preaisle on a Noetherian etale site; the new node is a general limit-stage closure assertion with no scheme, support filtration, or generators.

`lem-per-preaisle-transfinite-monomorphism-closure` vs `lem-coef-generating-set-cotorsion-smallness`: the latter constructs cotorsion approximations and describes filtered objects in an abelian category; it does not assert that arbitrary extension/coproduct/positive-shift closed derived subcategories contain the derived objects of such filtrations.

`lem-per-preaisle-transfinite-monomorphism-closure` vs `lem-coef-infinity-local-union-transfinite-extension`: that node concerns simplicial inclusions, local unions and anodyne extensions, not monomorphisms of complexes or preaisles. Whole DAG and whole-blueprint searches for preaisle, cocomplete, transfinite and set generated found no equal statement. The new source has no Stacks tag and hence no pair with an existing identical-tag node.

## Review by Q58

I read the current item, its live counterpart (same unsplit statement), chapter and unit records, the current main-20261015 ancestor proof, ILO XVII 5.2, and Stacks `injectives.tex` at `lemma-set-iso-classes-bounded-size` (079E), `proposition-objects-are-small` (079F), `lemma-characterize-injective` (079G), `lemma-acyclic-quotient-complexes-bounded-size` (079K) and `lemma-characterize-K-injective` (079L). For the new node I checked its full self-contained statement against the required limit-stage argument; no archived source claims it verbatim, so its source explicitly says agent-formulated and WANTED. It has no proof steps or proof dependencies. Its statement includes smallness of the ordinal, zero at the start, continuity at every nonzero limit, and degreewise monicity; none can be silently omitted in its use here.

Step 1 takes arbitrary-ring-sheaf Grothendieckness from the exact statement of `lem-weil-pbc-ring-sheaves-grothendieck`, and termwise derived coproducts, including empty sums, from `lem-kun-grothendieck-derived-coproducts`. I checked the former has no commutativity restriction. The definition of derived localization supplies representatives, not the existence of arbitrary Hom sets by itself; the fixed-universe Grothendieck setting is in force.

Step 2 uses the bounded acyclic-complex theorem for the very cardinal needed by the K-injective criterion, the bounded-object isomorphism-set theorem for the set of complexes, and the subobject-set theorem for the subobjects of the chosen generator. It uses each statement, not the more elaborate constructions in those proofs. The disk differential is the identity in adjacent degrees; the identity-cone inclusion has quotient the positive shift of its domain. Thus all its test cokernels are acyclic. The set of complexes is a subset of a countable product of object-representative sets and morphism sets, so no proper-class test family is introduced.

Step 3 reads the Baer criterion exactly for subobjects of the chosen generator, and then applies the K-injective criterion only after proving termwise injectivity and the required bounded-size acyclic nullhomotopies. I checked both parts of the cardinal hypothesis are supplied by 079K. Extending over the identity cone really kills a map up to chain homotopy, not merely on cohomology.

Step 4 uses 079F only for degreewise maps into a monomorphic chain. Uncountable regular cofinality bounds the countably many component stages; monicity then gives both the chain equations and uniqueness at a common stage. It does not assert that arbitrary complexes are compact. The AB5 definition justifies infinite sums of monomorphisms and monicity of chain colimit maps. Step 5 consequently meets precisely the smallness and cocompleteness assumptions in the existing small-object Mathlib leaf. That leaf supplies a genuine small ordinal cell chain, so the new closure lemma has an admissible indexing ordinal.

Step 6 applies the new statement to the complexes `(K_beta/K_0)[-1]`, not to `K_beta` followed by an unsupported negative shift. The successive derived factors are exactly sums of `G[k]`, k nonnegative, and zero. The reused coproduct theorem gives precisely the required termwise/derived identification. No closedness of the preaisle under negative shifts is assumed.

Step 7 uses the existing K-injective Hom-bijection statement, whose source and target complexes need not be bounded; it does not use only its bounded-below clause. It therefore converts actual cone-lifting nullhomotopies for all nonnegative shifts of the chosen representatives into all required derived Hom vanishings.

Step 8 uses exactly contravariant Hom factorization from `lem-weil-pbc-hom-out-of-triangle-exact`. Every remaining closure assertion follows by a coproduct universal property, splitting maps or reindexing nonnegative shifts. This is an elementary closure/minimality step. I checked its use of all nonnegative shifts is essential: testing just S would not give positive-shift closure. Step 9 uses the existing short-exact cone comparison (not merely a definition of an exact sequence); inverse rotation supplies A -> K -> B. The lower class is `U^perp[1]`, so its shift axiom is `U^perp subset U^perp[1]`, obtained from `U^perp[-1] subset U^perp`. This checks the sign convention against all three axioms in `def-weil-t-structure`.

Small cases checked: empty S yields U=0 and a quasi-isomorphic K-injective B; S={0} has the same outcome; the zero ring/empty site gives the zero category; theta=0 in the new lemma has zero endpoint; a one-successor filtration is just its quotient; a countable limit agrees with the usual telescope; uncountable cofinality is expressly handled by the new lemma rather than an invalid sequential reduction. Arbitrary unbounded representatives cause no finite-degree assumption. A general ring (including noncommutative) only enters through its Grothendieck module category. No new node is a clause of the item. Each step is below 2000 characters, and I checked for hidden lemma-sized identifications: the limit-stage closure is precisely the one extracted new node. Citations were read in full, and `citations.json` quotes their actual statements.

## Unfinished work

Only the intentionally statement-only new auxiliary node remains unsplit, as required for a one-level split.

## Resumption and validation

On resumption after the provider interruption I found no still-running delivery process. The current shared item remains unsplit with the identical statement, and its attachment searches in the current read-only project source still return no matching declaration. I reopened every statement cited by the nine proof steps and checked all twenty step/node quotations against the current statements; all remain verbatim. In particular, the small-object leaf assumes only the monomorphic-chain smallness verified in Step 4, and the K-injective criterion receives both bounded-size acyclic-complex hypotheses. The current ancestor proof uses middle-perverse truncation in Step 2; this is the place realized here, as the split report explains.

The server-only check_dag passed. The required delivery dry run exited successfully with `OK (not pushed)` and preflight passed at `a12a68adce`. No delivery invocation remained active after that result. The report update records these checks; a final dry run precedes the push.
