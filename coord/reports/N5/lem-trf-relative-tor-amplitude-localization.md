# N5 stage-1 delivery: lem-trf-relative-tor-amplitude-localization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-relative-tor-amplitude-localization.json`: existing statement, now split into seven steps; Mathlib searches found no match for the full relative unbounded-complex equivalence.
- `citations.json`: one verbatim statement extract for each step/node citation.
- `report.md`: this report and author's review.

There are **0 new nodes and 0 new Mathlib leaves**. The pre-existing item searches, statement, metadata, ancestry, and citations were retained, with the N5 search results appended. No earlier split/report was present in the sandbox; only brief marker files were present. No Lean or live-project file was written, and no compiler, Lake, build, or local delivery-check script was run.

## Attachments

None for the item. Searched the read-only `WeilConjectures/` source for the exact id and blueprint tag, Tor-amplitude/localization combinations, and related file names. The project's generic TorAmplitude and FlatModel declarations do not state this equivalence for a ring homomorphism and all source primes. The existing DAG already supplies the generic resolution and tensor-model statements used here; these are reused without editing or reattaching them. The upstream master checkout was used only as reference, never as evidence that a sorry declaration is proved.

## WANTED

None. The needed Stacks sources are present locally.

## What required repair

The item's statement faithfully states (1) iff (2) of Stacks 0B67 with A renamed R and B renamed A. It is true without flatness, boundedness, finite generation or finite presentation. Its proof was empty. The source explicitly omits (1) implies (2) and writes the tensor-localization identity without proof. The split supplies both gaps, rather than citing the item or a new restatement of either implication.

In particular an A-K-flat resolution of K need not be R-K-flat when A/R is not flat. I avoided that invalid inference by resolving each R-test module N and using an auxiliary resolution of K as an R-complex in a two-resolution computation, retaining the A-action on the unchanged K factor in C_N. The source-algebra and base-ring Tor-vanishing nodes concern modules in degree zero, so they cannot be applied to this arbitrary complex. Likewise the ring-only prime-localization injectivity node cannot detect vanishing of an arbitrary cohomology module; the proof instead gives the annihilator argument, citing the proper-ideal maximal-ideal theorem for its only existence input.

The chapter and unit records were read, including the current ancestry node's `blueprint_update`. This auxiliary algebraic input stays within the pre-existing 0DHY/0B67 branch recorded by `blueprint.from`; it changes no chapter, unit, ancestry or target statement. The three off-unit generic tools are declared in `split_report.tool_uses`: existence of unbounded K-flat module resolutions, computation on a supplied K-flat factor, and K-flatness after scalar extension. They do not replace a step of the contracting-correspondence unit.

## Not duplicates

No new nodes are proposed. For completeness the closest existing facts were distinguished as follows:

- Item vs `lem-pc-tor-vanishing-localized-algebra`, `lem-pc-tor-vanishing-localized-base`, `lem-pc-tor-localization-denominators`, `lem-pc-affine-sections-tor-bound-stalk`, and `lem-trf-tor-localization-on-spec`: those concern individual Tor groups of modules, notably the source algebra in degree zero, not both implications for an arbitrary unbounded A-complex. They cannot replace this item and were not duplicated.
- Item vs `lem-pc-derived-tensor-localization-cohomology` and the first/base/second-localization model nodes: these compare tensoring with a base-change algebra and specified cohomology models, not the quantified module-test equivalence. No duplicate of their comparison interfaces was created.
- `lem-pc-kflat-extension-of-scalars`, `lem-pc-source-module-kflat-resolution`, `lem-pc-source-kflat-module-tensor-model`, `lem-weil-pbc-localization-module-exact`, and `lem-weil-pbc-exact-functor-complex-cohomology` are reused verbatim for their generic statements.

Whole-DAG searches included 0B67, 00HN, Tor/localization keywords and candidate declaration names. Whole-blueprint searches included `relative tor amplitude localization`, `Tor amplitude` and `0B67`; none states this item in another form, so `same_as` remains []. The many sheaf Tor-amplitude entries concern different objects and coefficients.

## Review by N5

I read more-algebra.tex at `lemma-tor-amplitude-localization` (0B67), its displayed identity and omitted implications; `lemma-K-flat-resolution` (06Y4); `lemma-base-change-K-flat` (06Y1); and the ordinary derived tensor construction and signed flip following `definition-derived-tor`. I read algebra.tex at `proposition-localization-exact` (00CS), `lemma-characterize-zero-local` (00HN), and `lemma-Zariski-topology` (00E0), and homology.tex at `lemma-exact-functor` (010N). There are no new-node sources to review. I opened the statement of every cited existing node and checked each use against the actual assertion, not its proof or its informal title.

Step 1 uses `lem-pc-source-module-kflat-resolution` for resolutions of N[0] and of K restricted to R. Its arbitrary-complex and commutative-ring hypotheses apply over R. `lem-pc-source-kflat-module-tensor-model` computes the derived tensor using the R-K-flat resolution F of K. The explicit definition `def-pc-module-kflat-complex` supplies both quasi-isomorphisms from F tensor P, one to K tensor P and one to F tensor N. This verifies the computation with the test resolution without relying on a derived-symmetry assertion or on an A-K-flat replacement being R-K-flat. `def-pc-tensor-complex-sheaves` explicitly gives the direct-sum totalization and sign convention; ordinary modules are its one-point ringed-site specialization, also specified by the item's K-flat definition. The A-action acts on K and commutes with both differential terms.

Step 2 uses `lem-weil-pbc-localization-module-exact`, which states exactness of the fraction localization of arbitrary module sequences. Additivity is immediate from the stated fraction formulas. `lem-weil-pbc-exact-functor-complex-cohomology` then supplies exactly the cohomology isomorphism and preserves quasi-isomorphisms, with no bound on the complex. It is applied separately in the module categories of R and A. This is a theorem citation for homology preservation, not a deduction from the definition of flatness alone.

Step 3 uses `lem-pc-kflat-extension-of-scalars` for the unital ring map R to R_p; that node requires no flatness or injectivity. Step 2 preserves the augmentation under localization. The identification of termwise scalar extension and termwise fraction localization is proved by two inverse pure-tensor formulas, not assumed from a cited definition. The same tensor-model node and the two-resolution argument of Step 1 give the localized computation; the source-resolution node is explicitly cited again for the auxiliary R_p-resolution of K_q. The actual structural map sends r/t to phi(r)/phi(t), so its denominator condition follows from p = phi inverse(q).

Step 4 uses only `def-weil-pbc-module-localization` and the totalization formula of `def-pc-tensor-complex-sheaves`. I checked the two displayed inverse maps against the localization equivalence relation and R_p tensor balancing. The inverse denominator s phi(t) avoids q. Finite-support sums have a common product denominator, so localization and the unbounded direct sums are handled by the explicit maps, without an unmentioned infinite-product argument. Each differential retains the same K-degree r and therefore the same sign. This is an elementary tensor/fraction calculation, not a new comparison lemma moved to a node.

Step 5 combines only Steps 1--4. It records which A-module is being localized and keeps the contracted base-prime action explicit. Step 6 uses the fraction definition for N_p = L when L is already an R_p-module, with both inverse maps written out. Applying (1) to the restriction of this arbitrary L is legitimate; it does not assume every R_p-module descends as a finite module or a module with presentation.

Step 7 uses `lem-weil-pbc-proper-ideal-contained-in-maximal` only for its stated existence of a maximal ideal containing a proper ideal. The annihilator is introduced explicitly, and the maximal-ideal-is-prime argument is written out. The zero criterion for a localized element is exactly the quoted clause of `def-weil-pbc-module-localization`; it gives the required contradiction for each element. No finite-generation form of Nakayama or support theorem is used. Together these elementary arguments prove global vanishing from all the localized modules and finish (2) implies (1).

I tested K = 0, A = 0 (empty prime spectrum), R = A, a = b, a nonflat quotient R to A, and an unbounded complex. The nonflat quotient is particularly useful: only P_p is claimed K-flat over R_p, never K or an A-resolution over R. All fraction denominators and scalar actions are valid in these cases. No source or statement dispute was found. The seven step texts are all below 2000 characters; the only comparisons proved inline are the inverse tensor/fraction formulas and the two quasi-isomorphisms obtained directly from the definition of K-flatness, which are elementary calculations from the cited definitions. All non-elementary existence, K-flat stability, tensor computation and cohomology facts are cited existing nodes.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the files and sources. There is no new statement-only node, hollow data, duplicate, clause relabelling, imported-statement change, added hypothesis, SGA source, or circular dependency. The citations file quotes the cited statements verbatim. The Mathlib searches were made with msearch.py, including a second semantic phrasing; the returned types concern cohomological bounds, ordinary localization, support/free loci and cotangent results, not the full item. I read the relevant ordinary-localization source hits and did not mistake them for an exact match. No service failure was reported in this run.

## What could not be finished

Nothing in the mathematical split remains open. The initial server dry run passed at 20e736a66f. Final mathematical self-review then made the right-factor tensor computation explicit via two K-flat resolutions and added the corresponding definition citation; this is a clarification, not a change of statement. The final dry run is repeated before push.
