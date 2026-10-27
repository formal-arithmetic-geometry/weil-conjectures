# Stage-1 report: lem-sfb-relative-centre-multiplicative-base-change

Group Q13; 2026-10-24. Direct delivery, with the worker's own content review and the maintainer's independent review to follow.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-centre-multiplicative-base-change.json: statement, now split in seven steps; no Mathlib match.
- citations.json: one exact statement extract for every step/node citation (32 entries).
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

No new nodes and no new Mathlib leaves. The existing Noetherian centre theorem and eventual-reductivity theorem eliminate the need to create another centre construction or another approximation lemma. No Lean, unit record, repository file or launcher file was written, and no compiler was run. The fetched Conrad PDF and the five-page text extract are sandbox reading material only.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag, relative centre/center, schematic centre and reductive terminology. The project has field-group and Lie-algebra code, but no declaration proving this arbitrary-ring reductive-group statement. Its abstract special-linear-group centre results do not attach this item.

## WANTED

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Corollary 3.1.11 (printed pp.88--89), Theorem 3.3.4 and Definition 3.3.3 (pp.98--99), Appendix B.1 (p.280), for lem-sfb-relative-centre-multiplicative-base-change; archive in literature/conrad-reductive-group-schemes.pdf. The online PDF was read, including the actual proof. A copy was fetched only inside this item's sandbox. There is no local project-literature archive. The proof origin is honestly marked agent: this delivery assembles existing nodes by a written-out Noetherian reduction, rather than claiming that Conrad gives these seven steps verbatim.

## Corrections and scope

The mathematical statement is unchanged. A final source cross-check corrected step 4's auxiliary source tag from 00F4 to 00FP (lemma-Noetherian-finite-type-is-finite-presentation); its cited DAG node was already the correct theorem. I found no statement dispute. Conrad's extra assertion about the action on the scheme of maximal tori is not a clause of this item and is not used. The item needs no split torus, pinning, global root datum, reducedness or Noetherianity on A. I did not apply the existing Noetherian centre theorem directly to A: steps 1--3 construct a reductive Noetherian model first. That theorem expressly states arbitrary base change, so its use at A and A' does not impose a Noetherian hypothesis on those new rings.

The source's finite-presentation details are supplied by the existing Stacks nodes, rather than by assuming every closed subscheme is finitely presented over an arbitrary base. Finite presentation is proved for the centre over the Noetherian model and then base changed. The characteristic-p centre can be nonsmooth.

The item has blueprint.from.node=null in the live file. tools/blueprint_refs.py ancestor reports None; I preserved the inherited ancestor, exact place and via chain rather than inventing a blueprint id. Whole-blueprint searches for centre and reductive found no equivalent statement. I read the latest unit section and direct-image proof (3); this is the recorded subordinate reductive-model prerequisite, and changes neither the unit nor the chapter route. The four non-leaf tools in other units are declared under split_report.tool_uses, not in a new top-level approval field.

## Not duplicates

No new nodes. In particular, lem-sfb-relative-reductive-centre-weight-kernel already gives the Noetherian case and arbitrary base change, and lem-sfb-reductivity-eventual-ring-colimit already gives the needed structural descent. Both are cited instead of copied. The existing lem-sfb-affine-group-centre-base-change is field-only, so it cannot supply this reduction. lem-sfb-reductive-framed-noetherian-descent requires a given split maximal torus and a basis of root lines; I did not infer those missing hypotheses. lem-sfb-residue-marked-smooth-group-integer-model includes unnecessary marked residue-field data; the smooth-algebra model and the generic maps/equalities theorem supply exactly what is needed here.

## Mathlib searches

I ran msearch.py under Q13 and this item with LeanFinder, Loogle, grep and LeanSearch. The separate second phrasing of the centre query again returned abstract SpecialLinearGroup centre and diagonal scheme results. The exploratory Noetherian-model query found Algebra.Smooth.exists_finiteType, which is already represented by the cited Mathlib leaf lem-weil-pbc-smooth-algebra-finite-type-model; it does not descend a group law or reductivity. I read all displayed signatures. The item remains non-Mathlib. Every appended search record is copied from an actual searches.jsonl entry; inherited searches from the live node were preserved as inherited material. No unavailable service was recorded as a negative result.

## Review by Q13

I read Conrad's centre construction on pp.98--99: after a local split torus, the intersection of weight-character kernels is central by the smooth centralizer argument and contains every functorially central point. This is precisely the content already packaged by lem-sfb-relative-reductive-centre-weight-kernel; I checked its statement, including its Noetherian base hypothesis and unrestricted base-change conclusion, instead of borrowing unstated facts from its proof. I also read Corollary 3.1.11 and its proof on pp.88--89: it descends connected reductive fibres over the entire eventual model. No new node has a source to audit.

For step 1 I checked the statements of the affine smoothness equivalence and smooth-algebra finite-type-model leaf against Stacks 00TP, label lemma-finite-presentation-fs-Noetherian in algebra.tex. That source constructs a smooth algebra over a finitely generated subring, not a group. The step uses only that assertion here. The directed system is explicitly the set of finitely generated subrings containing the starting ring, and its union really is A. I checked the affine-limit, affine-qcqs, affine-morphism and smooth-base-change statements; they supply the index-system hypotheses that the next step needs.

For step 2 I read thm-pd-spreading-out and Stacks 01ZM, label lemma-descend-finite-presentation in limits.tex, clauses (2) and (3). The cited statement supplies arrows and eventual equality; it is not merely an existence-of-objects lemma. Multiplication, inverse and unit descend together, followed by the five group equalities at a common later index. The tensor-product finite-presentation and affine-fibre-product statements supply the product schemes, while the locally-finite-presentation definition and qcqs-permanence statement supply finite presentation as schemes. Thus every use of the maps/equalities theorem has affine transitions, qcqs bases and finitely presented source and target.

For step 3 I opened lem-sfb-reductivity-eventual-ring-colimit. It assumes a small nonempty directed system of nonzero rings, a smooth affine finitely presented group at one index and a reductive limit. All of those were established in steps 1--2; it does not demand a torus or flat transition maps. Its conclusion is reductivity on every point of every sufficiently late model. I checked Noetherian permanence in algebra.tex, Tag 00FN, label lemma-Noetherian-permanence. The elementary proof that integer ideals are principal is written in the step, so the base of that application is accounted for.

For step 4 I checked every hypothesis of the Noetherian centre theorem against G_0 and A_0. Its statement explicitly gives a closed multiplicative-type centre, flatness and arbitrary base change; no claim about a specified torus is used. The closed-immersion definition explicitly supplies a quotient of the coordinate algebra. Quotients preserve a finite list of algebra generators, and the existing finite-type-over-Noetherian finite-presentation leaf applies to that quotient. The lfp definition, affine-qcqs and qcqs-permanence statements then give finite presentation of the morphism, including quasi-separatedness. I checked that no finite-presentation assertion about a closed immersion over the original non-Noetherian A slipped into the argument.

For step 5 I checked the statements of the closed-immersion and flat base-change leaves, affine fibre products, affine morphisms, and qcqs-permanence clause (3). These are exactly the properties transferred to Z_0 times A. The closed centre is not inferred from pointwise commutativity alone: the cited Noetherian theorem identifies the centre functor after arbitrary base change.

For step 6 I read Stacks 021O, label lemma-fppf in topologies.tex, part (3), and the cited node's covering statement. It does allow an arbitrary change of base. The displayed group-algebra tensor maps are inverse on basis elements and respect all four Hopf operations; these operations are explicitly in the cited definition. I checked their compatibility on affine restrictions, so no unproved descent-of-multiplicative-type theorem is being used. The finite groups N_j may contain torsion and may differ on covering patches.

For step 7 the sole cited theorem explicitly says arbitrary base change. I verified that for an A'-algebra B the test extensions C are the very same B-algebras in both centre definitions. Consequently the comparison is the identity on the ambient G_0(B), not an unspecified isomorphism or a geometric-point argument. The zero A'-algebra is included.

I tested the statement and reduction on the trivial group, split and nonsplit tori, products over a disconnected base, an infinitely generated polynomial base, and nonflat specialization Z to F_p. For SL_p in characteristic p, the centre is mu_p: flat and finitely presented but not smooth, as allowed by the item. Nilpotent test algebras are retained throughout. These tests reveal why geometric points or tangent differentials alone would be insufficient; the delivered comparison uses all test algebras instead. There is no new statement to weaken on these cases.

Against delivery-errors B--E: the new-node requirements are vacuous; the item retains its statement and provenance. All 32 proof citations have verbatim statement extracts in citations.json. Each non-elementary step names the facts it uses; the finite group-diagram argument is an application of the existing maps/equalities theorem, not a concealed new structural lemma. No step exceeds 2000 characters. The source route is kept, no item clause has been moved into a new node, and no field-only or Noetherian-only input is applied outside its hypotheses. I read the full B--E sections, including the repeated migrated copy.

## Unfinished work

None at stage 1 for this split. Its existing unsplit dependencies remain their own queue items. Remote dry run and delivery results are recorded below when complete.

## Validation

The required deliver.py --no-push invocation exited 0 and printed OK (not pushed), preflight passed, at a10c37d1f33. The server ran its delivery preflight, including check_dag and review_split; no local checker or compiler was run. All seven proof steps are below 2000 characters. The subsequent push uses the same validated mathematical files.
