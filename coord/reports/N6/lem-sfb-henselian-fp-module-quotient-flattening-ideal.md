# Stage-1 delivery: henselian quotient flattening

Group N6; item lem-sfb-henselian-fp-module-quotient-flattening-ideal; 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-henselian-fp-module-quotient-flattening-ideal.json: item, split in seven steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-henselian-pointed-devissage-chart.json: statement-only supporting chart; unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-fp-quotient-flatness-directed-limit.json: statement-only limit-preservation input; unsplit, no Mathlib match.
- citations.json contains one verbatim statement quote for every step/node pair. searches.jsonl is the search tool's unmodified log.

## Attachments

None. Searches of lean/WeilConjectures by the item's blueprint tag, flattening, devissage, and the related RingTheory and Mathlib/RingTheory quotient-flatness terms found no declaration stating the item or either new node. Existing proved module algebra remains usable through existing DAG nodes. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are in literature/stacks-project. No SGA source is used.

## Corrections and route

The item statement is correct and unchanged. Tag 05PG is more general: its local test functor examines the primes containing the sum of the two maximal-ideal images after base change. For A/J this is just the maximal ideal of B/JB. Its localization is B/JB itself, so the source really does test the entire quotient module, without assuming B finite over A. In particular J=m works because the base is a field, forcing I inside m.

The supplied item was statement-only, with no prior sandbox split/report/search log. The preexisting item searches are preserved. The latest blueprint read was literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/{_section.md,sk-thm-sf-ctf-stability.proof.md}, especially the compactification/direct-image paragraph. The inherited null blueprint ancestor is confirmed by tools/blueprint_refs.py ancestor. No chapter, unit, target or route was changed. The algebra is the already recorded supporting chain through 0AT3/0AT4 to 05PG.

The existence proof uses the source's devissage induction, but retains global projectivity of each tail at its own flattening quotient. This replaces the source's 05I4 freeness and 05PF isomorphism-locus invocation by a split sequence and the explicit 05PE coefficient ideal. The final finite-generation argument is precisely 05PG's final paragraph via 05MN(2). In particular no finite-over-A hypothesis has been inserted. The tempting assertion that the kernel image E is finitely presented over T_i was not used; that would need an argument over a non-Noetherian base.

## Not duplicates

lem-sfb-henselian-pointed-devissage-chart vs lem-trf-complete-algebra-devissage-etale-existence: the existing 05I1 node expressly forgets pointing and allows changing the base by an elementary etale map; it gives no intermediate marked primes or unique-prime conditions. The new node fixes the henselian base and retains the intermediate singleton fibres needed to compare localized modules. It states a chart, with no flattening ideal conclusion.

lem-sfb-henselian-pointed-devissage-chart vs lem-sfb-henselian-fp-module-quotient-flattening-ideal: the new node is only the first 05PG preparation (existence of a pointed algebra chain and a faithfully flat local comparison). It supplies neither an ideal nor a flatness equivalence nor finite generation. Steps 2--6 construct the ideal and prove its property; step 7 proves finite generation.

lem-sfb-fp-quotient-flatness-directed-limit vs lem-sfb-henselian-fp-module-quotient-flattening-ideal: the new node requires an already flat limiting quotient and only descends flatness to one member of a given directed family. It neither constructs a universal ideal nor assumes henselianity. No existing source-tag match for 05MN, 05MK or 05LT was found.

The existing lem-sfb-flat-integral-free-surjection-iso-locus concerns a finitely presented target of a sheaf surjection on a flat integral-fibre family. Our E=image(alpha mod K) has no such finite-presentation hypothesis at that point, so that node does not state the coefficient calculation needed here. The coefficient calculation is written out as an elementary step, not created as a new lemma. Searches of all DAG nodes by the tags and key words and blueprint_refs search for 05PG, 05HZ, 05I1, 05HY, 05MN, pointed devissage, henselian flattening and directed flatness found no replacement.

## Review by N6

I read flat.tex 05PG in full, including its finite-generation paragraph, then read 05HZ/05I1 for the new pointed chart, 05I3 for generic-basis subtraction, 05FT for projectivity without Noetherian hypotheses, and 05PE for the coefficient construction. For the limit node I read 05MK, 05MN(2), and more-algebra.tex 05LT and its hypotheses. For the henselian chart I also read algebra.tex 04GG, including the etale-neighbourhood retraction clauses: these explain why the elementary base change in 05I1 can be pulled back to the original henselian base. This chart combines only preparation inputs, not the conclusion of 05PG. The input B may be essentially finite type; the finite module and its finite generators first descend to a finite-type chart. Localizing the etale chart produces a flat local, hence faithfully flat, extension; the retained singleton fibre gives the required pointed intermediate primes. Smooth algebras in the chain are flat of finite presentation. Their geometrically irreducible smooth fibres are geometrically integral; they are nonempty at the closed point, and the smooth open image over a local base then contains every prime. These facts are stated explicitly in the new node, not silently taken from the weaker unpointed existence node.

For Step 1 I opened each of its five cited statements. The new chart supplies exactly D, N and the chain. Faithfully-flat base change supplies B/JB to D/JD even for non-finitely-generated J; the descent statement allows an independent base A/J. The 00EA node is applied only to finite T_i to S_i with the unique prime actually supplied by the chart. The surjection C to S_1 first identifies the corresponding stalk. Right exactness and the displayed pure-tensor formula give quotient comparison, with no flatness of a quotient map assumed.

Step 2 sets up both induction assertions before use, including the zero terminal cokernel and the length-zero case. The projective definition really includes a split embedding in an arbitrary free module; no finiteness of its basis is needed. The global module in the invariant is M_i/I_i M_i, not merely its marked localization.

For Step 3 I read the actual statement of lem-trf-local-generic-basis-universal-injective: it gives BOTH universal injectivity and localized cokernel flatness from localized source flatness. Its local base, finite-presentation flat algebra, integral fibres, finite module and generic residue isomorphism have all been checked after A/J. The existing devissage-base-change statement gives the tensor chain and generic isomorphism; it does not promise pointing, so the proof obtains the marked primes directly by quotienting the primes containing m. The flat-base-change statement concerns the module T_i, and is used exactly for that.

For Step 4 the projective-quotient splitting node applies to the exact image/cokernel sequence as written. The 05FT projectivity node has no Noetherian assumption and matches T_i/KT_i over A/K. Taking finitely many copies of its split-free maps constructs F's split-free embedding explicitly. The ideal L is generated by all coefficients of all kernel vectors. There is no assertion that E, the kernel, or the free basis is finite over A/K.

Step 5 uses only the quoted tensor right-exactness and tensor universal property, and the already chosen split maps. I checked both directions: zero coefficients kill the image of the whole tensor kernel, while injectivity of v_H forces every kernel vector to vanish and hence every coordinate to vanish. Tensor of the split sequence remains split by its explicit maps, requiring no unquoted flatness assertion. This is elementary with those cited statements, as was the existing 05PE coefficient step in the live iso-locus split.

For Step 6 I added the existing field-module-flat node so that flatness at J=m is an actual citation. The converse first establishes projectivity at exactly I_i using the split decomposition. The scalar-extension node then applies to each projective summand, and the direct-sum node gives projectivity of the whole module. Projective-flat and base-flat localization statements then give the marked flatness for every larger J. Thus no unproved converse of the one-way generic-basis node is used. This stronger invariant supplies the tail projectivity needed at the preceding stage without introducing a new free-devissage lemma. All uses are of statements, not of the proofs of cited nodes.

For Step 7 the new directed-limit node applies because B is essentially finitely presented and P is finitely presented over B as given. The directed set is a set of ideals of A; it is nonempty, its union is I, and every member lies in m. The already established equivalence forces I contained in the chosen finitely generated subideal, giving equality. The node does not demand finite presentation over A. No limit-preservation claim is inferred just from a definition of flatness.

I checked small cases: P=0 gives I=0 and allows a zero-length chart; a field base has only J=0 and every module is flat; B=A and P=A/(a) gives I=(a); if a is a unit P=0 gives I=0 rather than the improper ideal. For A=k[epsilon]/(epsilon^2), P=k the ideal is (epsilon), so the coefficient criterion must detect nilpotents and indeed does. The chart over a field may use a finite-type etale neighborhood rather than claim the original algebra is smooth. The limit node includes a one-member family and J=m; it does not claim that an arbitrary flat module over a colimit is flat at a stage. Arbitrarily generated J are permitted throughout. Zero rings do not create an extra local closed-point case, since the usual local ring convention excludes the improper maximal ideal.

I checked delivery-errors B--E: both new nodes are self-contained statement-only records with inline meanings for essentially finite type, directed union and JP; definition references are explicitly listed. TeX is written once and source labels were checked in tags/tags. All search entries were run through msearch.py and read, with two semantic phrasings for each new node. The returned Henselian definitions, smooth/etale presentation lemmas, local flatness criteria and factorization of maps into an already flat module do not state either new node. No Mathlib leaf is claimed. Existing off-unit citations are generic ring/module algebra; split_report.tool_uses declares them without changing top-level tool_uses. They replace no trace, duality or six-functor proof step. I checked the seven steps for concealed lemmas: their lengths are all below 1200 characters; the only new non-elementary preparation and limit argument have their own statement nodes. Nothing remains unfinished in this one-level split; the two new unsplit nodes join the queue.

## Validation

Server review_split passed before the report was written. The required deliver.py --no-push exited successfully: OK (not pushed), commit ff16697af5d, preflight passed. The search-log, duplicate, verbatim citation and server DAG/split gates all accepted the delivery. A read-only dependency-closure check also found no cycle through any cited node. The final report is gated once more before the direct-delivery push. No local maintainer check, Lean compiler, Lake or build command was run.
