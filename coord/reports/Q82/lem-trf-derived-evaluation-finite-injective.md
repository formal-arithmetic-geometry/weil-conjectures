# Stage-1 report: lem-trf-derived-evaluation-finite-injective

1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-finite-injective.json`: split statement, unchanged mathematical statement, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-canonical-map.json`: new unsplit statement, no Mathlib match; construction and signed triangle compatibility of the general comparison, without an invertibility assertion.
- `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-pseudocoherent.json`: new unsplit statement, no Mathlib match; Stacks 0A68 (2).
- `citations.json`: verbatim statement excerpts for every step/node pair.

2. Attachments: none. I searched `WeilConjectures/` in the read-only slopmaster2 checkout for the blueprint tag and for derived evaluation, biduality, finite injective dimension and internal Hom. The project has ordinary sheaf biduality and homotopy internal-Hom infrastructure, but no declaration with all three hypotheses and the unbounded evaluation conclusion here. The upstream master is reference material only.

3. WANTED: none. The source used here is present locally.

4. The earlier sandbox was retained and compared against the current unsplit repository item. Its dry run rejected three semantic-query records because their text did not match the actual search log. I replaced those records with the exact logged queries, read the logged hits, and retained the prior item records and searches.jsonl. Additional genuine searches with second phrasings and LeanSearch were run and read. Unknown-identifier Loogle answers are now marked unavailable, rather than evidence of absence. The grep queries now give the actual query text; the searched directory is recorded separately in results.

The item agrees with Stacks `more-algebra.tex`, Tag 0A69 (`lemma-internal-hom-evaluate-isomorphism-technical`), including finite injective dimension of both targets, finite Tor dimension of RHom(L,M), and pseudo-coherence of every upper good truncation. No statement dispute or hypothesis correction was needed. I read Tags 0A67 (`lemma-internal-hom-evaluate`), 0A60 (`lemma-evaluate-and-more`), 0A68 (`lemma-internal-hom-evaluate-isomorphism`), 0654 (`lemma-tor-amplitude`), and 064J (`lemma-derived-tor-exact`), the injective-dimension definition, the Hom-complex definition, and `sites-cohomology.tex` Tag 08JC (`lemma-RHom-triangulated`). Tags 05RS/05RT and Remark 08J5 in `derived.tex` supply the cohomology and truncation interfaces used by the existing nodes.

The earlier tail helper quantified c after n; that is insufficient to pass to arbitrary degrees. The proof now fixes c=max(-a,u-v) before choosing n. The earlier triangle-gluing helper claimed an isomorphism from one lower vanishing range, and included proof text in an unsplit statement. For a fixed n, vanishing only below n-c does not control higher cohomology. For example take a comparison of triangles 0→V→V→0 and 0→0→0→0 with nonzero V supported above n-c: the first map is invertible and both tails vanish in the asserted range, but the middle map is not invertible. I removed this undelivered helper and wrote the degreewise argument in the item. I also removed the unnecessary tail helper: the tensor bound follows in a few lines from the existing flat-model and K-flatness nodes, and the double-Hom bound follows directly from the Hom-complex formula with bounded injective representatives. No source error is alleged: Stacks' argument requires, and admits, a uniform constant.

The original blueprint ancestry was restored on the item. Each remaining helper now has the full via chain with this item prepended. This preserves the algebraic duality subbranch serving the ancestor, and does not replace the ancestor's current contracting-correspondence proof. I searched all DAG nodes by evaluation/Hom and the Stacks tags, and ran blueprint_refs searches for evaluation, derived evaluation, internal-hom-evaluate, pseudo-coherent, finite injective dimension and truncation tail. None states either new input. Existing perfect-only and biduality-only results have a narrower comparison or additional hypotheses. The generic algebra and truncation tools from other units are declared in split_report.tool_uses.

5. Nothing remains unfinished for this one-level split. The two new nodes are statement-only obligations, not split themselves. Their searches return general exact-functor, t-structure, projective-resolution and ordinary module duality results, which do not provide these derived evaluation theorems in one line.

## Not duplicates

lem-trf-derived-evaluation-canonical-map vs lem-trf-derived-evaluation-finite-injective: the helper constructs the general map and its triangle compatibility with no finiteness assumptions and no isomorphism conclusion; the item proves its invertibility under three finiteness assumptions.

lem-trf-derived-evaluation-canonical-map vs lem-trf-complete-local-coherent-duality: the latter is coherent biduality over a complete Noetherian local ring with a dualizing complex; it does not construct the three-object evaluation comparison for an arbitrary ring.

lem-trf-derived-evaluation-pseudocoherent vs lem-trf-derived-evaluation-finite-injective: the helper assumes K itself pseudo-coherent and only L bounded below, whereas the item allows K unbounded above with all upper truncations pseudo-coherent and needs additional finite-injective and finite-Tor hypotheses to control the tail.

lem-trf-derived-evaluation-pseudocoherent vs lem-trf-complete-local-coherent-duality: the helper is the general three-object pseudo-coherent evaluation theorem of 0A68 (2); the latter concerns the dualizing-complex biduality map over a complete Noetherian local ring.

lem-trf-derived-evaluation-canonical-map vs lem-per-relative-bidual-triangles: states the same-target bidual map A→RHom(RHom(A,L),L); the new comparison has arbitrary distinct L,M and source RHom(L,M)⊗K, which cannot be obtained by simply specializing that bidual statement.

lem-trf-derived-evaluation-canonical-map vs lem-weil-pbc-ringed-complete-element-addition: states closure of a derived-completeness predicate under addition of coefficient elements; it constructs no three-object evaluation map.

lem-trf-derived-evaluation-canonical-map vs lem-weil-pbc-ringed-complete-element-multiplication: states closure of a derived-completeness predicate under multiplication by a coefficient; it has no evaluation comparison.

lem-trf-derived-evaluation-canonical-map vs lem-weil-pbc-ringed-internal-hom-exact-restriction: gives tensor-Hom currying, restriction and exactness, but does not give the three-object evaluation transformation or its compatibility on the connecting map. Those extra construction assertions are what the new node supplies.

lem-trf-derived-evaluation-canonical-map vs lem-coef-rational-bidual-triangle-compatibility: uses the coefficient-unit double dual and its scalar localization; it does not give the comparison with two arbitrary targets L,M.

lem-trf-derived-evaluation-canonical-map vs lem-sf-double-hom-cone-comparison: gives explicit cone and shift isomorphisms for Hom(-,I) iterated with the same I, without constructing the evaluation transformation with two targets and tensor source.

lem-trf-derived-evaluation-canonical-map vs lem-sf-etale-generic-hom-triangle: concerns the inverse-image internal-Hom base-change comparison on an etale site, not the tensor-to-double-Hom comparison over a ring.

lem-trf-derived-evaluation-canonical-map vs lem-sf-even-line-hom-shift: concerns a single internal-Hom comparison with a shifted rank-one line and an even shift; no double Hom with arbitrary L,M is stated.

lem-trf-derived-evaluation-canonical-map vs lem-pur-external-rhom-cone-pairing: pairs two global derived Hom objects after pullback to a product setting with bounded-flat test complexes; neither its objects nor its pairing are the arbitrary ring-module tensor-to-double-Hom comparison.

lem-trf-derived-evaluation-canonical-map vs lem-per-localization-dual-boundary-pairing: the existing node identifies a boundary transpose with a cup product and evaluation for a finite locally free sheaf on an etale open immersion with bounded Rj_*; it does not construct the arbitrary three-object tensor-to-double-Hom comparison over a ring or its triangle naturality. This node arrived between the successful dry run and the attempted push, and I opened its complete statement before recording this distinction.

## Review by Q82

I reviewed the resumed split against delivery-errors B–E with the node statements and the source open. The two new nodes are self-contained statements with empty proofs and proof dependencies. The canonical-map statement now writes the correct three-factor evaluation composite (the earlier search description had an incorrect source), introduces F and G, and explicitly includes exactness and compatibility on the connecting map. Its source is 0A67 and the signed construction of 0A60, with exactness from 064J and 08JC. This is a construction obligation, not the item's isomorphism claim. The pseudo-coherent node is exactly the commutative-ring instance of 0A68 (2): K pseudo-coherent, L bounded below, M represented by a bounded injective complex. It asserts invertibility of that same map. In particular it does not require finite injective dimension of L or finite Tor dimension of RHom(L,M), so it is not a relabelling of the item.

Step 1 takes both exact functors and the natural comparison from the canonical-map node's explicit statement; it does not infer triangle compatibility from bare naturality. Step 2 uses clause (2) of the existing bounded-below injective representative node, the standard t-structure's representative characterization, and clause (1) of the general heart/truncation theorem. Bounded complexes I,J satisfy its bounded-below condition; the latter two statements really give the truncation triangle and a representative B_n supported in degrees at least n+1. L is bounded below because J is bounded. This is an elementary instantiation of those stated facts.

Step 3 applies precisely the pseudo-coherent helper, with K=A_n and every hypothesis verified: pseudo-coherence is hypothesis (iii), bounded-below L was checked in Step 2, and finite-injective M is hypothesis (i). Step 4 cites the ring-module flat-model equivalence, rather than a scheme-only finite-Tor definition, and the ring-module bounded-flat K-flatness theorem. The first really gives P supported in [a,b]; the second really makes it K-flat. The total tensor definition then gives the support calculation r=i+j≥a+n+1. These are the needed existing statements, not facts taken from their proofs.

Step 5 uses only the actual product formula and K-injective-target computation in the derived-internal-Hom definition, with I,J already made K-injective in Step 2. It writes both index inequalities: r≥n+1 and r+s≤u force s≤u-n-1; then s+t≥v forces t≥n+1+v-u. Thus c=max(-a,u-v) works for both tails independently of n. The argument is the routine degree count on the very complexes that define these objects; no additional comparison or vanishing theorem is hidden in it.

Step 6 uses canonical-map triangle compatibility, exactness of the cohomology sequences, their naturality from the existing cohomology-ladder node, and the existing all-degrees cohomology isomorphism criterion. With d fixed and n≥d+c, the tail H^(d-1) and H^d vanish, so each horizontal map from the truncated value to the full value is an isomorphism. The commuting square conjugates H^d(e_A_n) into H^d(e_K). No all-degrees conclusion is taken from a single lower range. Naturality belongs to the same fixed canonical map throughout.

I tested zero K, zero L, zero M and the zero ring, all giving the unique map between zero objects. Over a field with L=M=R[0], the estimates reduce to both tails starting in degree n+1. Shifting L and M so that J is in degree u and I in degree v gives the expected n+1+v-u bound; this checks the signs and shift convention. Non-Noetherian rings are allowed: no finite-generation characterization of pseudo-coherence is used. Unbounded-above K is the reason n varies, and no boundedness of K was inserted. All six steps have fewer than 2000 characters. The report and citations were revised after removing the two unnecessary/incorrect undelivered helpers; previous searches remain in the append-only log.
