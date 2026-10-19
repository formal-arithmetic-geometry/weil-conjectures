# Q125: ordinary smooth-functorial resolution

## Files written

- dag/nodes/sec-trace-formula/lem-trf-smooth-functorial-ordinary-resolution.json: item, split; original statement and statement dependencies retained.
- dag/nodes/sec-trace-formula/lem-trf-embedded-resolution-ambient-comparison.json: statement, unsplit; no Mathlib match. This is the embedded algorithm input, including its invariant synchronization and comparison under a change of ambient embedding.
- citations.json: one verbatim statement quotation for each proof-step/node citation.
- searches.jsonl: searches performed by msearch.py, retained with their actual results.

## Attachments

None for the item or the new node. Searches in WeilConjectures/ for the exact blueprint tag, desingularization, Hironaka, Bierstone, and resolution/singularity vocabulary found no declaration providing characteristic-zero resolution. Existing blowup declarations do not resolve singularities. The master checkout is not evidence of a finished proof and was not used as such.

## Wanted literature

WANTED: Bierstone, Milman and Temkin, *Q-universal desingularization*, Asian J. Math. 15 (2011), 229–250, Theorem 6.1, its Addendum, and section 6.3, for lem-trf-embedded-resolution-ambient-comparison: the embedded construction, ambient independence, and synchronization invariant. The available ILO exposé VIII 2.3.11 and 2.3.13 explicitly point to this input and the synchronization correction; the detailed paper is absent locally. I did not download it or claim to have read it. Its detailed construction, including the labeled formulation, remains work on the new unsplit input. The item's proof_origin is agent, since the supplied local-to-global argument expands the available discussion rather than reproducing a proof of ILO's quoted theorem.

## Audit of the imported item and route

ILO VIII Theorem 2.3.10 is a quoted desingularization theorem, not a proof. Simply introducing the same theorem for quasi-excellent schemes and restricting to finite type would move the entire item to a new node. The split instead uses an embedded theorem and carries the intrinsic ordinary-blowup identification, reduction of arbitrary smooth maps to smooth ambient maps, synchronization on overlaps, stagewise gluing, independence of covers, and the comparison and composition laws in the item's proof.

The new input is not a clause of the item: it concerns a reduced closed subscheme of a smooth separated ambient scheme, ambient blowups, and strict transforms, with a synchronized invariant. It neither states an algorithm on arbitrary nonseparated schemes nor gives functoriality under an arbitrary smooth morphism of the reduced schemes. Those are derived in steps 1–6. The synchronization labels are essential mathematical input, not independently assigned stage numbers; omitting them would make the local comparison and gluing argument invalid. No global quasi-excellent resolution theorem is introduced as a renamed item.

The statement needs no correction. Ordinary regular centers must not be confused with the centers in the normalized algorithm: ILO 2.3.12(ii) warns that the latter can even fail to be reduced. No normalization is taken here. The unit sk-i-curve-zero in the current blueprint has already changed to contracting correspondences; the assigned node is a historical descendant of the nearby-duality/alteration branch through toric resolution and fan resolution. This split preserves that ancestry and changes no unit or chapter route. The item is not the unit key node, so no unit file is written.

## Searches and duplicates

I searched all DAG statements for resolution of singularities, desingularization, principalization, marked ideals, embedded resolution, and invariant synchronization, and read the neighboring toric and fan resolution statements. I ran blueprint_refs.py ancestor and searches for desingularization, embedded, resolution invariant, and ambient. There is no blueprint node giving this embedded algorithm input. The ordinary, toric-normalized, and fan-resolution nodes concern different categories and none states the embedded theorem. Existing strict-transform and flat-base-change nodes were reused instead of recreated. No new node carries a Stacks tag shared with an existing node; the local embedded-resolution theorem has no Stacks tag.

The msearch commands used the exact queries in searches.jsonl. Natural-language searches were tried in two phrasings for both the item and the new input. LeanFinder and LeanSearch returned only smoothness, immersion, reduced-open and base-change declarations. Loogle's first two-string query was invalid; it is recorded as invalid, and valid substring searches for desingular and blowup were run. Grep found no desingularization, embedded resolution, Bierstone or principalization theorem. No new Mathlib leaf or unrun search is asserted.

## Not duplicates

lem-trf-embedded-resolution-ambient-comparison vs lem-trf-smooth-functorial-ordinary-resolution: the former is an embedded ambient algorithm and its invariant comparison; the latter is intrinsic resolution of arbitrary finite-type reduced schemes, including nonseparated schemes and arbitrary smooth maps between them.

lem-trf-embedded-resolution-ambient-comparison vs lem-trf-toric-normalized-desingularization: the latter concerns normalized toric towers and torus actions, not ordinary embedded resolution or ambient independence.

lem-trf-embedded-resolution-ambient-comparison vs lemma-nagata-strict-transform-ambient-closed: the latter identifies a given strict transform with a blowup and supplies no resolution algorithm; it is cited directly in step 1.

## Review by Q125

I read ILO exposé VIII printed pp.87–95, especially 2.1.3–2.1.9, 2.3.1, 2.3.4–2.3.5, Theorem 2.3.10, Remarks 2.3.11–2.3.13, and the contrast between ordinary and normalized centers. For the new node I read the available discussion of the Bierstone–Milman input and its synchronization correction in 2.3.11 and 2.3.13, and the bibliography identifying *Q-universal desingularization*. The detailed reference and the stronger labeled formulation are explicitly left as the new unsplit task, with the missing source reported above.

Step 1 uses the embedded input for its ambient tower, regular centers, stopping condition, labels and ambient comparison, and lemma-nagata-strict-transform-ambient-closed for the actual identification of each intrinsic step with a blowup. I opened that node and its blueprint proof; it states precisely the closed-immersion strict-transform identification. The two definition citations give the polynomial presentation and the closed immersion resulting from its surjection. No project theorem merely about normalized blowups is substituted.

Step 2 uses exactly the affine-chart conclusion of lem-weil-pbc-smooth-locally-standard-smooth, the arbitrary-ideal quotient lift of lem-weil-pbc-standard-smooth-quotient-lift, and standard-smooth implies smooth from lem-weil-pbc-standard-smooth-is-smooth. I opened all three statements and read Stacks 01V7 (morphisms.tex, lemma-smooth-locally-standard-smooth), 00T7, and the equation lifting in 07CK (smoothing.tex, lemma-lift-once). I use only the quotient-lift statement, not the nilpotent-I hypotheses of the different full 07CK result. I corrected an initial formulation that silently asked the local-chart node to keep a preselected target affine: the final proof instead embeds the affine target chart actually supplied by that node. The embedded input covers open smooth ambient schemes, not just affine spaces, which is required to compare these new embeddings with the original ones.

Step 3 uses the embedded input's labels and local ambient comparisons, plus the flat blowup base-change theorem and its defining comparison. I opened both base-change statements: the definition supplies the map under flatness and the theorem says that map is an isomorphism. The argument checks labels and ideals on a covering and then inducts on the ordered labels; equality of contracted local towers with independently renumbered steps would not suffice. Smooth maps are flat, so this use satisfies the map's hypothesis.

Step 4 uses the finite-cover clause of def-weil-finite-type-morphism and open (therefore flat) blowup base change. The proof itself gives the inductive gluing of ideals and next spaces and the triple-overlap condition. The two overlap maps into the disjoint union are smooth even when they lie on different components. Affine intersections are not presumed affine. Equal ideal subsheaves glue by the sheaf definition; no fpqc descent theorem with extra hypotheses is hidden here.

Step 5 uses the embedded input for coherent centers and regular final charts. Regularity, coherence, nowhere denseness and being the unit ideal can be checked on these Zariski covers. Nonemptiness is checked on the whole covering family, not on every component. The comparison of two covers uses their union and the overlap argument: a label empty on one entire cover would be empty everywhere, a contradiction. This verifies cover independence and handles mixed-dimensional disjoint unions without unsynchronized choices.

Step 6 uses the already established embeddable comparison and flat blowup base change. A finite affine cover of T subordinate to h's inverse images exists because T is finite type and quasi-compact; each component maps smoothly to its chosen target affine. At each level a unit ideal is detected on all charts. Step 7 checks composition on the actual affine tensor identifications and on ideal extension, and checks surjective nondeletion by base-changing h at each level. These are elementary verifications from the cited comparison map, not an invocation of unspecified naturality.

I tested empty schemes, regular inputs, zero-dimensional reduced inputs, open smooth maps missing a center, surjective covers, disconnected mixed-dimensional inputs, and nonseparated schemes. Empty and regular inputs have length zero; unit stages may disappear for an open restriction; a nonempty global center survives a surjective pullback even if it is empty on some components. Nowhere dense refers to a closed subset with empty interior on the scheme at that level. I checked all citation quotes against the literal statements and preserved the imported statement and metadata. No proof step exceeds 2000 characters. The only new node is a genuine non-elementary embedded theorem and has no proof or proof dependencies. No compiler, Lake, local DAG validator, agent, live-tree write, or manual git command was used.

## Unfinished mathematical work

The embedded-resolution input is intentionally statement-only and unsplit, as required for new nodes. It is not claimed proved or present in Mathlib. In particular its invariant synchronization must be checked against the detailed reference when that node is split. No part of the assigned item's conditional reduction is left as an uncited non-elementary fact.

## Final citation repair

The first dry run passed at 196a4585b6. A further reading of the steps identified two implicit interfaces, so I added their existing nodes rather than leaving them implicit: the affine ring/scheme smoothness equivalence and smooth composition in step 2, and smooth implies flat in step 3. I read their full statements; the affine equivalence applies to the actual Spec map, composition applies to Q → affine space → Spec Q, and smooth-flat supplies exactly the hypothesis of blowup base change. The coherent-module definition is now a statement dependency of the embedded input. Step 4 also writes out why its open overlap maps are smooth directly from the formal-smooth definition. I regenerated the verbatim citations and reran the dry run for this corrected delivery.
