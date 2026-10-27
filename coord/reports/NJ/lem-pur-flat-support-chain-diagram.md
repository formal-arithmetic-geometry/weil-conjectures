## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-pur-flat-support-chain-diagram.json` (statement; split; no Mathlib match), `citations.json`, this report, and the search log produced by msearch.py. No new nodes or Mathlib leaves. The statement and its statement dependencies are unchanged. All inherited sources, searches, blueprint provenance and created record are retained.

Attachments: none. Searches under `lean/WeilConjectures/` for the exact blueprint tag, flat_support_chain, flatSupportChain, supportChainDiagram and support/tensor/kernel terminology found no declaration stating this diagram. Tor and tensor-support declarations cover different objects. No Lean was written or compiled.

WANTED: none. The required sources are available locally.

What needed repair: the item had no proof. Its source Tag 093X proves surjectivity of restriction for injective module sheaves, not the arbitrary-cochain comparison in this item. I retain that provenance and explicitly use it only as motivation for the optional epimorphism hypotheses. The new proof is agent-written, using the existing exact-filtered-colimit and cochain-comparison nodes. In the retained parent report Q107, returned Step 3 omitted the inverse comparison c_{Q,I}^{-1}; the current item already has this type-correct factor, and I retain it throughout. No statement dispute or change is needed.

What remains: nothing in the stage-1 split. The cited unsplit termwise-adjunction node remains its own independent work item. Formal Lean proofs are outside this brief.

## Sources and searches

I read `literature/stacks-project/sites-modules.tex`, Tag 03DA (module sheaves, sectionwise kernels), Tag 03DB, lemma-limits-colimits (all colimits and exact filtered colimits), and Tag 03ER, definition-flat (3). I read `sites-cohomology.tex`, Tag 07A4, lemma-pullback-tensor-product (the actual total cochain tensor comparison in its proof), and Tag 093X, lemma-restriction-along-monomorphism-surjective. I also read the current main-20261015 purity-transport unit and thm-pur-rational-and-qbar-purity proof, plus the retained returned proof in `coord/reports/Q107/lem-pur-etale-kflat-support-comparison.md`. This is the Locality prerequisite for coefficient transport, not a replacement of smooth purity by a trace argument. No SGA source is used.

Mathlib searches for the item were run through msearch.py: LeanFinder with two phrasings, Loogle, LeanSearch and grep. Their exact queries/results are in the node and searches.jsonl. All services answered. I read the Flat/CategoryTheory.lean hits: lTensor_shortComplex_exact and rTensor_shortComplex_exact concern single modules, not the open-adjunction cochain diagram. The Loogle hits construct degreewise split complex triangles, not the stated kernel diagram; the LeanSearch hits define scheme open immersions. The three grep hits concern finitely supported tensor products and local-ring module support. None gives every clause of the item, so it is not a Mathlib leaf. The GrothendieckCategory/Basic.lean AB4 instance corroborates the elementary finite-subsum argument, but is not an uncited additional premise: the proof derives direct-sum exactness explicitly from the cited module-sheaf theorem.

I searched the whole DAG for direct-sum exactness, kernels/tensor and Grothendieck module categories, and used blueprint_refs.py search for coproduct exact, exact coproducts, kernels, flat tensor, support chain and tensor kernel. These led to the existing constant-ring etale-module Grothendieck-abelian node. The scheme O_X-module Grothendieck result has the wrong coefficient/site category and was deliberately not substituted. The countable-derived-sum node assumes exact sums and only describes a derived coproduct, so was not cited for sheaf exactness. The ancestor command prints null; the inherited null blueprint.from.node and its explicit finite-stage transport place are retained. No new blueprint duplicate was found.

## Not duplicates

No new nodes are proposed. The proof cites existing ambient-category and tensor-comparison nodes directly.

## Review by NJ

I checked the proof against delivery-errors B through E with the sources and every cited statement open. There is no statement-only child carrying a clause of the item and no new node needing a separate search or source. All seven arguments remain in the item, with each step shorter than 800 characters. The sources explain the ambient inputs; the chain identities are written out rather than attributed vaguely to Tag 093X.

Step 1 uses the sectionwise-kernel clause of def-weil-sheaf-of-modules-category and clause (a) of lem-weil-pbc-termwise-adjunction-homotopy, which really gives a natural unit on actual complexes. I checked d preserves the kernel using r d = D(d) r, and proved d squared, functoriality and the chain equations by cancellation. No epi or injective assumption enters.

Step 2 cites lem-weil-pbc-module-sheaves-grothendieck-abelian, whose statement explicitly gives all small colimits and exact filtered colimits for Mod(Lambda_T) on the SMALL ETALE site for every scheme and commutative ring. Taking T=P and Lambda=A checks every hypothesis; this is not a pro-etale or O_P-module specialization. The finite subsets of the integer-indexed bidegrees form a small nonempty filtered poset, including the empty finite subset. The universal property identifies their colimit with the direct sum, and componentwise finite kernel/cokernel calculations prove finite-sum exactness. Thus no unrecorded AB4 theorem is used.

Step 3 uses the exact-functor definition in def-pc-flat-sheaf-modules and the explicit direct-sum terms, signs and functoriality in def-pc-tensor-complex-sheaves. The definition has flatness on the right, so the proof explicitly swaps ordinary tensor factors to cover Q^p on the left. An exact functor preserves the kernel row even if r_I is not epi; only the final right exactness uses that hypothesis. The equality of the two differential components is the chain-map equation for s and r. This is an application of the exactness definition, with the required infinite-sum argument written separately in Step 2, not an unstated theorem that K-flat implies flat terms.

Step 4 uses the full statement of lem-pur-cochain-pullback-tensor-coherence, which supplies the cochain isomorphism, its bidegree formula and naturality for arbitrary unbounded complexes of module sheaves on ringed topoi. The constant-A inverse-image adjunction in the item is identified with module pullback by prop-weil-pbc-inverse-image-modules-exact. Clause (a) of the termwise-adjunction node gives the actual cochain adjunct, with no localization involved. I checked the type of h includes c_{Q,I}^{-1}. The formula on every inclusion iota_{p,q} follows from naturality of eta; it does not require j_* to preserve sums.

Step 5 cites exactly that tensor-comparison naturality and termwise adjunction. Its displayed computation takes both ordinary transposes and applies epsilon_{j*I} j*eta_I = identity and the same identity at J. These are the adjunction triangle identities, not an unsupported assertion about equality of objects. This proves equality of the specified chain maps, including their signs.

Step 6 uses the actual sectionwise kernel universal property already cited and tensor functoriality. The equation r_J a(1 tensor s_I)=0 follows from Step 5, without surjectivity. Factoring degreewise defines u; composing the chain equation with the next-degree kernel inclusion proves it, and its monicity proves uniqueness. This verifies every clause of strictness.

Step 7 uses naturality in both arguments from the cochain comparison and the unit/counit naturality in the termwise adjunction. I wrote the equation for h before taking adjuncts, then wrote the equation after composing the kernel square with s_{J'}. This checks naturality for independently varying I and J with the required relation g a = a' (1 tensor f); it is not restricted to functorial injective replacements. The induced kernel maps were constructed in Step 1.

I tested small cases: j=identity gives r=identity, S=0 and v=a; U empty gives C=C'=0, S(I)=I, S(J)=J and u=a; Q=0 gives the zero diagram. For Q concentrated in degree p the proof gives the expected (-1)^p sign on the other differential. With infinitely many nonzero degrees the finite-subsum argument still applies and no product totalization is introduced. When r_I or r_J fails to be epi, the kernel map and naturality persist and the proof only withholds the corresponding terminal short-exactness claim, exactly as the statement says. No B-action, boundedness or K-flatness was introduced. I checked citations.json quotes are verbatim substrings of the cited statements. Generic tools outside the unit are declared in split_report.tool_uses with their purpose; no chapter or unit route was changed.

## Validation

Required server dry run and direct push are performed after this report is written; their terminal output is the delivery evidence.

The first dry run stopped before preflight because the tensor-functoriality quotation was shorter than the gate's 40-character minimum. I expanded it to the full tensor statement and expanded the cochain-comparison quotation to include its actual isomorphism and naturality. No proof or statement changed.
