# Stage-1 delivery: lem-wf-exact-finite-gsets-forgetful

## Files written

- dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-exact-finite-gsets-forgetful.json: statement, now split in nine steps; no Mathlib match for the item. Its statement, statement dependencies, source, creation record and blueprint ancestry are unchanged. Existing searches are retained and seven genuinely executed searches are appended.
- citations.json: one entry for every step-node citation, using literal excerpts of the existing node statements.
- report.md: this report. searches.jsonl is the search command's actual log; write_split.py is sandbox-only preparation, not a DAG delivery file.

New nodes: 0. New Mathlib leaves: 0. One existing Mathlib leaf is reused.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 checkout for the item tag, finite G-sets, continuous actions and fibre/fiber functors. The project declarations concern finite etale schemes or their fibre functors, not the exact assertion about an arbitrary topological group and arbitrary exact finite-valued H. Mathlib declarations are not project attachments. The item's imported record has no Lean declaration or open sorry frontier to incorporate.

## WANTED

None. Both source arguments used are present locally.

## Findings and changes

Read Stacks pione.tex, label lemma-second-fundamental-functor (Tag 0BMV), including its entire proof. The imported statement agrees with it, with H in place of F and the direction of the natural isomorphism made explicit. No statement dispute or correction is needed. The two passages marked “details omitted” required actual arguments: compatibility of the pointwise construction, and passage from regular quotient actions to all finite actions. Steps 6 and 8–9 supply those arguments.

Read the chapter and sk-d-geometry unit records. This item is a foundational tool below def-wf-fundamental-representation, not that unit's key statement: no realized fields are changed. Read the current main-20261015 definition at its paragraph “After the usual transport of the stalk from Phi_X(xbar) to xbar”. This item supplies precisely the uniqueness-of-exact-functor input in the finite-cover transport proof, retaining its blueprint ancestry. The generic finite-set inverse-limit tool does not replace the unit's geometric route.

Searched the whole DAG by Tag 0BMV and by the finite inverse-system/cofiltered section concepts. Also ran blueprint_refs ancestor and searches for “0BMV” and “finite continuous”, and examined the inverse-limit matches. Found the existing lem-trf-cofiltered-finite-sets-section, which directly states exactly the compatible-choice result needed. The existing lem-galois-inverse-limit-surjective was also read; it has an unnecessary surjectivity hypothesis for this use, so the more directly applicable existing Mathlib leaf is cited instead. No duplicate node is created. The category of finite actions, open action kernels, and the finite-set universal-property arguments are written explicitly, not introduced as unnecessary elementary nodes.

Executed msearch with LeanFinder in two phrasings, Loogle on ContAction and FintypeCat, LeanSearch on the exact finite-valued functor, and three grep queries in CategoryTheory/Galois. All services answered. Read the returned Mathlib candidates in Galois/Examples.lean:80–105 and Galois/Basic.lean:83–101. They establish a fibre-functor structure for the standard forgetful functor on abstract group actions, or require an existing Galois-category/fibre-functor structure; they do not give a one-line specialization of this item's uniqueness theorem for arbitrary topological G and merely exact H. Read CofilteredSystem.lean:79–81 to confirm the reused leaf's match. The seven new mathlib_searches entries reproduce the tool/query strings in this sandbox's searches.jsonl and report the actual hit summaries. Imported historical searches are preserved separately as inherited evidence.

## Not duplicates

No new nodes; no new/existing same-tag pairs require justification. The existing Tag 086J leaf is reused without editing it.

## Review by N8

I reviewed B–E of delivery-errors.md against the node and the open source, including the universal-property arguments and every cited statement. The proof follows the actual 0BMV argument: nonemptiness, regular-action cardinalities, compatible elements, and the induced natural isomorphism. The only non-elementary ingredient is the compatible-section theorem, already a Mathlib leaf. There is no shifted restatement of this item in a new child.

Step 1 cites def-galois-exact-functor. Its statement defines preservation by sending a limit cone or colimit cocone to one, and defines exact as preserving both finite limits and finite colimits. This licenses exactly the preservation claims. I checked the concrete finite action constructions: invariant subsets retain their stabilizers, finite products intersect them, and quotient-class stabilizers contain representative stabilizers. These are open subgroups, which proves continuity on the discrete finite actions without a Hausdorff or profiniteness assumption. Empty constructions cause no representative-choice problem because they have no points. Their equivariant universal properties are explicit.

Step 2 uses the same definition to preserve the displayed singleton pushout; nonempty X makes its source pushout a singleton, whereas an empty H(X) would give two points. Thus H cannot annihilate a nonempty action. Step 3 again uses that preservation statement, now for a surjection's kernel-pair coequalizer and pullback. I wrote the fibrewise factorization and equivariance argument rather than citing a definition of epimorphism or asserting that an arbitrary functor preserves surjections. In sets the coequalizer is literally a quotient, so it is onto. Both cases A=B=empty and nonempty B are covered.

Step 4 uses exactness for the explicit orbit decomposition of Q_N times Q_N. I checked normality in the formulas, finiteness of both cardinals, and positivity before cancelling n. Step 5 cites only lem-trf-cofiltered-finite-sets-section. Its statement gives a compatible family for every small cofiltered diagram of finite nonempty sets and explicitly requires no surjective transitions. I verified all of these hypotheses: the index is a set of subgroups, G itself is an object, intersections give refinements, there are no parallel-arrow obstructions, and step 2 gives nonemptiness. Read the full statement and its source, Stacks categories.tex Tag 086J, label lemma-nonempty-limit; also checked its recorded Mathlib declaration. Thus the quote in citations.json is exactly the conclusion used, with all its hypotheses checked in the step.

Step 6 needs no further lemma: the kernel is the finite intersection of the open point stabilizers, is normal, and has finite index through the finite permutation group. The formula f_N,x(gN)=gx is well defined because N acts trivially. Intersecting two choices makes their maps literally equal after projection, and the already chosen compatible elements make the H-values equal. The naturality equation is written for every equivariant map. I checked X=empty separately and do not use a large colimit of all finite actions.

Step 7 cites exactness to preserve the explicitly empty equalizer of distinct right translations. This proves distinct images of gamma_N, with bijectivity then following from the previously proved finite cardinal equality. Step 8 cites exactness for finite coproducts and invokes the fully written earlier argument that H preserves surjections. Its cover is indexed by the actual finite set X, not an infinite collection of orbits; each summand maps onto its point via the identity coset. Naturality and the regular bijections then give surjectivity on every action.

Step 9 cites exactness only for the kernel-pair pullback already explained in step 3. I checked that R is again a finite continuous action, so step 8 applies to R without any circular appeal to injectivity. The equality of the two H(q)-images supplies an element of H(R); its preimage under t_R, followed by injectivity of t_Y, proves equality of the original points. The last displayed equation proves naturality of the inverse rather than silently transporting it. This repairs the second omitted passage in 0BMV in full.

Small-case tests: for trivial G, all regular quotients are singletons, and the construction on a finite set is its singleton-coproduct identification; for connected topological G the same conclusion holds because every finite continuous action is trivial. For X empty, H(X) is empty and its component is the unique bijection. For finite discrete G, N={e} gives the usual chosen torsor point; the regular translation argument and descent along the finite cover work directly. No freeness is assumed for a general action and no finiteness, compactness or profiniteness is assumed for G itself. Nonempty indexing is supplied by N=G even when no proper open finite-index subgroup exists.

I checked C1 and C4 by opening both cited node files. citations.json records their verbatim statements, never a proof-only fact. No new theorem nodes conceal elementary arguments, no source tags stand in for an unstated non-elementary theorem, and no statement contains a proof sketch. Every proof step is below 2000 characters (largest: 1006), so there is no long-step hidden-lemma issue. No node, unit or chapter outside this item is edited, and no Lean code or build tool is used.

## Unfinished work

None in the requested one-level split. Required server validation and delivery are recorded below after the tool completes.

## Validation

The required deliver.py --no-push exited successfully: `OK (not pushed) deliver/N8/lem-wf-exact-finite-gsets-forgetful at 1355650bec: preflight passed`. Server preflight included the required DAG and split checks. No mathematical files changed after this successful dry run; this receipt line is the only subsequent report addition.
