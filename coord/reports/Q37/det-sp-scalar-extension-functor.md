# Stage-1 repair: det-sp-scalar-extension-functor

## Files written

- `dag/nodes/sec-smooth-purity/det-sp-scalar-extension-functor.json`: unchanged statement; replaced the 8,762-character proof with seven assembly steps totalling 2,437 characters.
- `dag/nodes/sec-smooth-purity/lem-sp-finite-ring-action-local-constancy.json`: one new statement-only node, no Mathlib match. Its complete proof in words is below (under 2,000 characters).
- `citations.json`: one verbatim statement quotation for each cited node in each parent proof step.

## Attachments

None for the item. The project-wide tag and notion search under `lean/WeilConjectures/` found no finished declaration of all its clauses. The existing `lean/Sheaf/SecSmoothPurity/ScalarExtensionFunctor.lean` has sorry proofs for exactness, K-flat computation, constructibility/Tor, lines, Tate comparison and composition/coherence. Its definition alone does not attach the item.

The completed generic source theorem `CategoryTheory.Sheaf.exists_mem_forall_isConstant_over_of_forget`, `lean/WeilConjectures/CategoryTheory/Sites/ConstantForget.lean:110`, corroborates the finite-operation argument. I read its complete proof and helpers: it is for fixed-ring ModuleCat-valued sheaves and concludes local constancy, whereas the new statement explicitly supplies finite local models for internal modules over the constant ring sheaf. I have not claimed it directly states the new node; the finite action construction below treats the exact coefficient category and finite models explicitly.

## WANTED

None. All sources needed are present locally.

## Returned point repaired

The human returned the whole proof for being too coarse, with a total of 8,762 characters. The current repository still contains exactly that nine-step version. The sandbox initially contained only dispatcher marker files: no node, report or search log was retained. I copied the current item, read the prior Q73 report and preserved the item's entire statement, statement dependencies, existing Mathlib searches, Lean attachment, blueprint metadata and accepted route-error record. The initial required dry run exited because the sandbox had no report; no push occurred.

The repair isolates the arguments rather than hiding them in shorter prose. Former steps 2--3 now use the existing `lem-trf-site-derived-tensor-restriction` for the actual derived comparison. Former step 4 uses the existing `lem-pur-proetale-restricted-tensor-finite-local-constancy`, together with the already accepted stratum comparison, for the local tensor-cohomology calculation. Former step 5 becomes the new general-site finite-operation lemma. Former step 6 uses the existing equational criterion for flatness and a one-line local-basis factorization, followed by bounded-flat K-flatness. Former step 7 retains the previously split invertible-power/dual lemma, the independently proved finite Tate-line statements, and only the elementary root-tensor formula. Former steps 8--9 use `lem-sfb-successive-derived-quotient-normalization`, whose statement already provides the normalized derived compositor, naturality and agreement of iterated comparisons. I did not introduce duplicate nodes for any of these existing tools.

The new node remains statement-only, as the stage-1 delivery format requires; its short proof in words is supplied in this report as specifically requested by the repair brief. I have not moved the whole parent, or any entire parent clause, into that node: it mentions neither derived categories nor constructibility, Tor amplitude, Tate twists or scalar-extension composition.

## Proof in words: lem-sp-finite-ring-action-local-constancy

Work on a slice where the underlying set sheaf of F is the constant sheaf of a finite set M. Transport zero, addition, negation and each scalar action to that sheaf. For each input tuple in these finitely many operations, local representation from `lem-weil-pbc-site-sheafification-sections-local` (00WK) makes its value a constant element of M after a covering. Take successive common refinements for the finitely many tuples. Naturality then makes every operation on constant inputs a fixed table on each resulting slice.

If the slice is not covered by the empty sieve, two distinct elements of M have distinct images as constant sections: the local equality clause of the same cited lemma would otherwise give a covering on which these unequal elements of the constant presheaf are equal, forcing an empty covering. The module identities, which hold in F, therefore hold for the tables on M itself. This gives a finite Lambda-module on M. The set-sheaf trivialization respects these tables. Arbitrary sections of both the constant ring and the constant module locally come from constants, again by 00WK; thus the trivialization respects all ring-sheaf scalar sections and is an isomorphism of internal modules. On a slice covered by the empty sieve every sheaf is the unique sheaf, so use the zero module instead. Compose these refinements with the initial trivializing covering. This proves the statement for every object, with no point or connectedness assumption.

This expands Stacks 093S (`lemma-morphism-locally-constant`) by the finite-operation argument of the returned step 5, using 00WK (`lemma-sections-sheafification`) for both local representation and local equality. It also makes explicit why degenerate slices are harmless. No additional unproved theorem is used: finite refinement is an iteration of the covering axioms, and extension from constants is checked on a covering by the sheaf axiom.

## Review by Q37

I read AGENTS.md, GOAL.md, the worker brief and stage-1 document, the three-level route rule in SETUP.md, the chapter and current scalar-extension unit, delivery-errors B--E, the current main-20261015 item statement and all four proof paragraphs, and the prior Q73 report. The statement and the two already accepted corrections remain unchanged: ell invertibility is required only for the Tate example, and identity extension means the actual identity ring map. I retained the recorded failed use of lem-sf-flat-model for arbitrary finite rings and arbitrary schemes; this repair follows the already accepted stratified tensor route instead of reopening it.

For the new node I read Stacks sites-modules.tex 093S at `lemma-morphism-locally-constant`, sites.tex 00WK at `lemma-sections-sheafification`, and the complete generic finite-operation proof in the source library's ConstantForget.lean. I also opened every same-tag candidate listed below. Its statement introduces the site, constant ring, sheaf category, coverwise finite set models and slice sites; these notions have inline definition-node citations. It does not assert a fixed action table before refining. The proof handles objects covered by the empty sieve separately and never assumes enough points.

Step 1: I opened `lem-pur-derived-change-of-rings` and `lem-pc-kflat-resolution`. Their statements give an everywhere-defined exact functor valued in the target-ring derived category, canonical K-flat computation, and flat-term K-flat representatives, respectively. The site and coefficient categories are exactly those in the item, with the right-factor ring action; no flatness of B is introduced. I read the source at Stacks 06YS and 06YY.

Step 2: I opened `lem-trf-site-derived-tensor-restriction`, `lem-weil-pbc-restriction-derived-products` and `def-weil-proetale-tor-amplitude`. The first explicitly states the balanced derived comparison for an arbitrary ring-sheaf map and every target-module sheaf N in degree zero; this is precisely the Tor test needed here. The second states exact restriction and conservative underived restriction. Consequently cohomology vanishing is detected after restriction. The degree-zero sheaf Res(N) is an allowed A-module test; taking N=B_T tests boundedness of K_B. I checked 05V4's tensor identity and 0G7E's flat-term K-flat base change in the source. No bounded resolution or finite projective dimension is assumed.

Step 3: I opened the full statements of `lem-weil-pbc-constructible-stratification-intersection`, `lem-sp-stratum-scalar-extension`, `lem-pur-proetale-restricted-tensor-finite-local-constancy` and `lem-weil-proetale-constant-sheaf-stalk`. The refinement is an actual fibre-product stratum, not a factorization inferred merely from its underlying image. There are finitely many input nonzero cohomology sheaves. On each refined stratum their restrictions are locally constant with finite geometric stalks. Both inputs K and B_T[0] are bounded above, and the latter has finite local models since B is finite. The existing stratum node gives the coefficient and tensor pullback comparisons, while the restricted-tensor node gives the output's local constancy and finite stalks as an A-module. I read Stacks 094H at `lemma-locally-constant-tensor-product`, whose finite-type and Noetherian hypotheses are accounted for inside that existing theorem (A is finite). On an empty T keep an empty stratum; for zero K use the single stratum T. Pulling back a trivializing cover along the refinement retains the constant finite models.

Step 4: The constant-stalk statement identifies a local constant module value with its geometric stalk on a nonempty member, so it is a finite set; on an empty member use zero. The new finite-action statement then applies with Lambda=B to the actual B-module cohomology sheaf, not just its A-module structure. Its hypotheses concern only the underlying set sheaf, so that forgetful change is permitted. `def-weil-proetale-constructible-sheaf` explicitly defines constructibility by a finite stratification with locally constant finite stalks. Those are the same strata as step 3. I opened both statements and checked that no etale-only assertion is applied on the pro-etale site.

Step 5: I opened `lem-weil-pbc-site-flat-equational-criterion` and `lem-weil-pbc-independent-bounded-flat-kflat`. For a local basis e of L, write the finitely many s_i=b_i e, choose l=1 and t_1=e in the equational criterion; the basis makes sum a_i b_i=0. This verifies exactly that criterion, even for an empty relation or the zero ring. The degree-zero line complex is bounded above with flat terms, so the second cited statement applies. Step 1 then computes ordinary extension, and the local maps a tensor b -> f(a)b and b -> 1 tensor b identify its target with the rank-one free B-module. I checked Stacks 06YQ at `lemma-bounded-flat-K-flat`. This short basis argument needs no new node.

Step 6: I opened `det-def-sp-tate-twist-locally-free`, `def-pur-sheaf-tensor-product` and `lem-sp-invertible-tensor-scalar-extension`. Only the finite clauses of the first are used, taking E=Q_ell, with ell invertible on T. They provide invertibility, compatible roots and canonical Kummer exponent identifications for every finite coefficient ring killed by the common power. The displayed balanced root map and its inverse preserve those exponent maps: both routes take (z tensor a) tensor b to the image of z tensor f(a)b. The second generic theorem handles positive tensor powers, the unit and internal duals, including the ring-map iteration squares. Step 5 identifies these ordinary line computations with derived ones. No choice of root basis enters the canonical map. I checked r=0,1,-1 and the root-transition formula in the cited finite Tate statement.

Step 7: I opened `lem-sfb-successive-derived-quotient-normalization` in full. Its statement has arbitrary commutative ring sheaves and the actual K-flat derived change of rings; it explicitly states the comparison formula, inverse, naturality in the derived object and ring maps, and equality of iterated comparisons. It therefore supplies the derived naturality and associativity claimed here, not just an underived associator. For an identity second map its recorded formula is multiplication, the tensor unitor. This last identification is elementary from `def-pur-sheaf-tensor-product`; it does not mistake equal endpoint rings for the identity map. The theorem is a generic tool of another unit, declared in split_report.tool_uses; it is not a replacement geometric proof route.

Every step's cited statement was opened and read, and citations.json copies those actual statements verbatim so all used clauses are available to the checker. proof_deps is exactly the union of uses. I checked dependency closures for the newly reused tensor-restriction, stratum, restricted local-constancy, equational-flatness and normalized-composition tools; none depends on this item. The seven parent steps are each under 600 characters, and their total is 2,437. The only new proof, above, is under 2,000 characters. The earlier child's stratum and invertible-power statements are retained, not duplicated or edited.

## Edge cases and search audit

I tested the arguments with the empty scheme/site slice, zero complex, zero target ring, a singleton Tor interval, and the nonflat map Z/ell^2 -> F_ell. The Tor proof works because it tests B-module sheaves, not because B is A-flat. The finite-action proof covers nonconnected sites and empty-sieve-covered objects; it requires only a finite ring and finite local values. On a point site it reduces to the existing finite module. For arbitrary finite A, neither a DVR presentation nor ell invertibility is used outside the Tate example. The Tate tests r=0,1,-1 and changing exponent agree with the displayed root maps. Composition for identity maps and nonidentity Frobenius of F_4 distinguishes the correct unitor case. All statement corrections and the unit-route issue recorded by the previous delivery remain untouched.

I searched the whole DAG and blueprint for change of rings, restriction of scalars, finite underlying sheaves, module operations, scalar towers and the candidate new statements before writing. This found the two important generic existing nodes and the restricted finite local-constancy theorem, eliminating three contemplated duplicates. For the new action lemma I ran LeanFinder twice with distinct phrasings, Loogle, grep and LeanSearch through the required msearch.py. I read their results, including the condensed constant-sheaf APIs, finite-type generator API and topological IsLocallyConstant declarations; none proves this arbitrary-site finite-operation statement in one specialization. The generic fixed-ring module theorem found in the project is discussed above. Exact queries, actual top hits and verdicts are recorded in the new node and searches.jsonl. Searches for discarded candidate nodes remain in the log but are not falsely attributed to new nodes.

No SGA source was used. No Lean file was written and no compiler, Lake or build command was run. All writes were in the item sandbox. The repository and launcher were read only; the required delivery tools own their temporary worktrees.

## Not duplicates

- lem-sp-finite-ring-action-local-constancy vs lem-trf-finite-locally-constant-coherent: states coherence and stability of finite locally constant set sheaves on a finite-cover site, not constancy of an imposed module action.

- lem-sp-finite-ring-action-local-constancy vs lem-sfb-constant-realization-reflects-isomorphism-general: reflects isomorphisms of algebraic derived complexes; it does not construct local coefficient-action tables.

- lem-sp-finite-ring-action-local-constancy vs lem-sfb-constant-realization-reflects-isomorphism: identifies cohomology of constant derived realization and detects isomorphisms on a pro-etale slice, not module local constancy from finite underlying sets.

- lem-sp-finite-ring-action-local-constancy vs lem-sfb-bounded-constant-chain-map-local: locally algebraizes a map of bounded constant complexes over one fixed ring; it does not refine a new finite ring action on a set sheaf.

- lem-sp-finite-ring-action-local-constancy vs lem-sfb-constant-realization-detects-zero: proves injection of constant module elements on nonempty pro-etale objects; it does not construct a constant module structure from varying operations.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-sheaf-cokernel-local-image: describes local images and the cokernel of a morphism on a ringed space, not finite-action local constancy on a general site.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-module-constant-of-set-pullback: uses a nonempty connected scheme and etale inverse image; the new lemma has arbitrary sites and no connectedness or point hypotheses.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-site-constant-morphism-local: localizes an already linear map between constant modules of the same ring; the new lemma constructs a simultaneous action and finite module model from set trivializations.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-site-sheafification-sections-local: supplies local section representation and equality, used in the proof; it does not impose or locally trivialize module operations.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-constant-ring-sheaf-sections-locally-constant: represents sections of a constant ring on an etale site, not finite-operation tables on arbitrary sites.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-constant-module-sheaf-sections-locally-constant: represents sections of an already constant etale module, not a module whose set sheaf is merely locally constant.

- lem-sp-finite-ring-action-local-constancy vs new-r2-etale-abelian-kan-comparison-locally-surjective: proves local surjectivity of a specified etale Kan comparison; it makes no assertion about finite action tables.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-site-module-sheafification-lift-injective: proves that a locally injective module-presheaf map sheafifies to a monomorphism; it does not construct locally constant module structures.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-large-set-sheafification: identifies sheafification equivalences with local bijections in specified universes, not finite module local models.

- lem-sp-finite-ring-action-local-constancy vs lem-weil-pbc-site-sheafification-iso-locally-bijective: characterizes maps whose abelian sheafification is invertible, not finite-action local constancy.

- lem-sp-finite-ring-action-local-constancy vs lem-cbc-presheaf-sheafification-epi-local-lifts: characterizes epimorphisms by local lifting for set presheaves, not finite ring-action trivializations.

- lem-sp-finite-ring-action-local-constancy vs lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover: is restricted to etale covers of schemes; the new lemma applies to all small sites and explicitly yields finite constant module models.

- lem-sp-finite-ring-action-local-constancy vs lem-pod-lisse-module-sheaves-as-module-objects: is the etale scheme equivalence with finite locally constant module objects, not the general-site finite-table lemma.

- lem-sp-finite-ring-action-local-constancy vs lem-pod-module-local-constancy-of-finite-underlying: is an etale scheme assertion and explicitly makes no assertion on the finiteness of its constant module models; the new lemma has arbitrary sites and finite models.

## Unfinished work

No stage-1 argument is left unaccounted for. The new child is queued in the statement-only format with its complete proof in this report. Stage-2 signatures and stage-3 proofs remain outside this authorized repair.

## Delivery continuation, 2026-10-21

The required first dry run found one stale quotation: the live Tate-twist statement now explicitly defines the finite twist by its root tensor and uses actual newlines. I opened and read that current statement. Its finite clauses still give precisely the compatible root generators, canonical exponent-change isomorphisms and invertibility used by step 6; its added tensor definition agrees with the unchanged parent statement. I refreshed that entry of citations.json from the current statement verbatim. Comparison with the current live parent confirms its statement is unchanged and only proof, proof_deps and split_report differ: the retained repair reduces the proof from 8,762 to 2,437 characters and adds the one statement-only finite-action lemma. Prior searches, citations and review are retained.
