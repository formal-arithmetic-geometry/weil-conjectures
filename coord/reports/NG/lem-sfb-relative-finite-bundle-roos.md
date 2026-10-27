# Stage-1 report: lem-sfb-relative-finite-bundle-roos

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-finite-bundle-roos.json: item, statement; split into eight proof steps, no full Mathlib match.
- citations.json: 21 step/node entries, each quoting the cited statement verbatim.
- report.md and searches.jsonl: report and actual search journal.

No new DAG nodes; zero new Mathlib leaves. No Lean files, compilation, repository writes or direct git commands.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, relative finite-bundle/Roos terminology and related continuous-bundle terminology. The general Roos declarations concern other sites or categories and do not state all clauses of this item. No finished declaration was substituted for the split.

## WANTED

None needed for this delivery. The cited paper and the Stacks sources used here are present. The paper's Lemma 1.2.7 ends by referring to another proof; this delivery does not claim to have read that absent reference. Its relative argument is explicitly agent-written.

## What needed repair

The item had no proof. Its source is a motivating result for torsion constructible sheaves, not a verbatim theorem about an arbitrary topological ring and a profinite slice. I supplied the actual argument and kept proof_origin.by = agent. The statement is unchanged and no STATEMENT-DISPUTED correction was needed.

In particular, fixed-ring Mathlib CondensedMod R is not internal modules over the varying section-ring sheaf C(-,T). Nor may a pro-etale-scheme product theorem simply be applied to Prof/P. The proof now derives exact products on the actual slice from finite-cover lifting over Stonean domains. All-small derived products are proved using arbitrary-small K-injective products; a countable-only derived-product node would not cover that clause.

I considered extracting relative exact products and a solution-space assertion, but the former would repeat a clause of the item and the latter is the specific compactness argument of this item. Both are written out as steps instead. Existing general lemmas give all their non-elementary inputs. There is no new node whose proof has merely received the item's work.

## Sources and searches

Read Ruimy–Tubach–Wolf, proetale-motives-solid-rigidity_arXiv-2601.07358.pdf, Lemma 1.2.7 and its proof (printed p. 14). Its reduction to an extremally disconnected closed-point space explains the mechanism, but its final reference omits the finite-bundle details here. Read Stacks topology.tex at Tags 08YN (proposition-projective-in-category-hausdorff-qc), 08ZU (theorem-tychonov), 005C (lemma-closed-in-quasi-compact), 005D (lemma-intersection-closed-in-quasi-compact); sites-modules.tex at 03CN (lemma-abelian-abelian), 03DA (lemma-abelian), 03DB (lemma-limits-colimits), and 03CO (lemma-limits-colimits-abelian-sheaves); derived.tex at 0BK6 (lemma-product-K-injective) and 07KC (lemma-products). No SGA source is used.

Read the current blueprint/latest chapter/unit and det-sf-comp-coherence-cocycle proof. The inherited ancestor's refinement-isomorphism paragraph leads through the closed-fibre comparison chain to this auxiliary finite-bundle input. No compactification unit route is replaced and no unit realization file is changed.

DAG/blueprint reuse searches included the Stacks tags, exact products, finite locally constant bundles, continuous sections, Roos, Tychonov, K-injectives and ringed topoi. The useful matches were opened and their full statements read. The existing sectionwise-limit, exact-forgetting, compact-product, finite-intersection and K-injective-product statements suffice; no new fact with these statements was created. same_as remains []: the scheme-site product nodes and finite abelian-group Mittag--Leffler node do not state this relative finite-bundle result.

Actual msearch.py calls used LeanFinder, LeanSearch, Loogle and grep, followed by a different full-item phrasing. The logs are preserved. I read the returned signatures and Mathlib/Condensed/AB.lean:43–67. Condensed.instAB4StarCondensedMod is about a fixed ordinary ring, and LightCondensed has a countable small-site variant. SheafOfModules limits and projective profinite presentations supply only components, not the item. Support searches also found Profinite.pi, Pi.compactSpace and Stonean projectivity, which were already represented by existing DAG tools. No full-item Mathlib leaf is claimed.

## Not duplicates

No new nodes; no duplicate pairs to justify. Existing generic tools are cited rather than recreated. The inherited mathlib_searches were retained and actual full-item searches from this session were appended.

## Review by NG

I checked B1--B10: there are no new nodes or unsupported leaf assertions; all eight proof steps are arguments rather than statements-only placeholders. The item retains its imported metadata and exact statement. The internal-module/sectionwise-module comparison uses the canonical sheafified tensor, not a private coefficient category; smallness and the monoidal sheafification condition are explicitly discharged in step 1. Every cited node file was opened and its statement read, and citations.json contains the exact statement text used by each step.

Step 1 uses def-sfb-continuous-map-condensed-ring for the actual continuous-function sheaf, lem-weil-pbc-sheaf-tensor-closed for exact monoidal sheafification and closed tensor, def-weil-pbc-internal-abelian-sheaf-module-equivalence for the section-preserving equivalence, and lem-weil-pbc-module-sheaves-colimits-forgetful for faithful exact forgetting and sectionwise limits. These hypotheses hold on the size-controlled slice, and commutativity follows from the given topological commutative ring. The reconstructed multiplication is exactly pointwise multiplication.

Step 2 takes local lifts from lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective, after exact forgetting. It takes a section of the continuous surjection from the full statement of det-pe-stonean-projective, not from a definition of projectivity. The finite coproduct is compact Hausdorff, so its hypotheses hold; the section is over P because it is over S. The sheaf gluing over disjoint clopen summands is written out. det-pe-stonean-cover explicitly supplies an extremally disconnected profinite cover of every test object. Empty test objects and empty covers cause no exception.

Step 3 uses the sectionwise products supplied by lem-weil-pbc-module-sheaves-colimits-forgetful and the lifting conclusion already proved in step 2. It writes out simultaneous coordinate choices and the kernel calculation. It proves exactness for every small family, without assuming the ring constant or the base extremally disconnected. This is an argument, not an application of a new node restating exact products.

Step 4 uses lem-weil-pbc-ring-sheaves-grothendieck on the actual small ringed site, lem-sfb-grothendieck-k-injective for resolutions of arbitrary unbounded complexes, and lem-pc-ringed-space-product-kinjective, whose statement explicitly allows an arbitrary set of factors and gives the derived product. The product quasi-isomorphism is justified by the displayed kernel/image/cohomology calculation from exact products, not by an uncited assumption of enough K-injectives in a different category. The equivalence of step 1 transports these facts to the internal category. Its projections are preserved.

Step 5 invokes only the full statements of lem-weil-pbc-tychonoff-product-quasi-compact and lem-weil-pbc-closed-in-quasi-compact as non-elementary compactness inputs. F_k really is Q times_P E_k, not E_k or a fibre over a point with the wrong base. The finite clopen local descriptions, closed equal-base conditions, closed equation loci, and inherited clopen basis give every compactness, Hausdorff and total-disconnectedness hypothesis. I checked continuity of addition in the finite bundle charts and of the given transitions; no continuity of a choice of solutions is assumed.

Step 6 again uses the compact-product statement and the full finite-intersection property in lem-sfb-compact-closed-finite-intersection, including its empty-index convention. Its finite backward recursion solves every finite set of equations even when the transitions are zero or nonsurjective. Each fibre is a nonempty finite group and hence compact. The index sets and products stay within the fixed profinite/indexing universe. There is no stabilization index, uniform Mittag--Leffler hypothesis or hidden limit-of-surjections assertion.

Step 7 uses the exact local-epimorphism criterion already cited, exact faithful forgetting, and lem-weil-pbc-module-sheaves-limits-sectionwise, whose statement explicitly identifies compatible tuples with the limit and its scalar action. Coordinate projections on the constructed Z_y give actual continuous sections on a single allowed cover. The kernel is computed before forming the derived category and is R_T-linear by the assumed module-linearity of transitions.

Step 8 uses lem-weil-pbc-complex-ses-triangle, whose statement gives a distinguished triangle from a degreewise short exact sequence in any abelian category, and def-weil-category-product for equality of maps tested after every projection. The latter citation is used only for its universal property. Step 4 already establishes the product comparison. The middle arrow is verified by its formula pr_k - t_k pr_(k+1), so no unspecified comparison changes the Roos endomorphism.

I checked C1--C8: all non-elementary inputs have cited nodes; no proof of a cited node is borrowed; the cited tools are generic facts, with off-unit uses declared in split_report.tool_uses. D1--D5 are addressed by the eight explicit arguments and no relabelled helper nodes. For E1--E7 I tested empty P, the one-point base, trivial/zero groups, identity and zero transitions, and fibre sizes varying in both k and p. The empty base makes every module zero; at a point the construction is the usual finite-group compactness proof; zero transitions give x_k=y_k. I also checked arbitrary, potentially non-Hausdorff T: descent of continuous functions uses the compact-Hausdorff quotient source, not a separation assumption on T. No finite/free scalar or surjective-transition condition was introduced. Every step is below 2000 characters, and the solution-space construction remains specific to the stated tower, with no independent lemma hidden in a long step.

## What remains unfinished

Nothing in the stage-1 split. This is a natural-language proof delivery; it does not claim a Lean proof. Required server dry run and direct push follow this review.
