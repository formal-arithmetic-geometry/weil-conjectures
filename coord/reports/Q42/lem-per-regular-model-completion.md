## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-model-completion.json`: item, statement unchanged, split into eight steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-closed-point-criterion.json`: statement-only, unsplit; Stacks 02IT; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-closed-fibre-stalk-completion.json`: statement-only, unsplit; Stacks 0BG5 specialized to a Noetherian local base; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each node used by each numbered step.

Attachments: none. Searches in the read-only slopmaster2 `WeilConjectures/` for both node tags, regularity/completion and closed-point regularity found no declaration giving the item or either new statement. `AlgebraicGeometry/Regular.lean` gives stalk regularity, smooth/etale consequences and connected regular integrality, but does not give this completion theorem or the closed-point criterion. The upstream master is not used as evidence of a finished proof.

WANTED: none.

The earlier attempt had the item, one new node, citations, `write_split.py` and ten logged searches, but no report. I retained that work and compared its item with the current repository: the statement, source, statement dependencies, ancestry and original search records still agree. Since no report was present, the brief's instruction to start with deliver.py when both item and report exist did not apply. I read the existing searches instead of repeating their questions. Five additional logged searches concern only the newly extracted 0BG5 lemma; all five returned successfully. No failed service is represented as a negative search.

What needed repair: the earlier proof inferred absolute quasi-separatedness of T from a node about relative quasi-separatedness; it now uses the exact locally Noetherian scheme theorem. The flat-morphism criterion for every pair of affine opens was replaced by the existing exact flat-ring-map/affine-morphism equivalence. The 0BG5 local comparison was a substantial standalone lemma marked elementary; it is now a genuine unsplit dependency. Its earlier quotient-by-powers argument is retained below as a takeover aid, outside the new node's statement. The local Noetherianity justification now cites affine stalk localization and Noetherian localization explicitly. The generic-field step cites the existing affine fraction-field theorem. No statement dispute was found. No Lean, compiler, build or git command was run, and nothing in the shared repository or launchers was edited.

Unfinished work: no part of this one-level split; the two unsplit mathematical dependencies deliberately remain for later workers.

## Sources and blueprint

Read `resolve.tex`, the full statements and proofs of 0BG5 (lemma-iso-completions), 0BG6 (lemma-port-regularity-to-completion), the third paragraph of 0BGI (lemma-regular-alteration-implies-local), and the first paragraph of 0BGM (lemma-existence-implies-existence-by-normalized-blowing-ups). These give precisely the completion passage needed by the parent normalized-resolution node. Read `properties.tex` 02IT (lemma-characterize-regular) for the new closed-point criterion and the locally Noetherian quasi-separatedness proof; read `more-algebra.tex` 07NY (lemma-completion-regular). The source's argument requires neither excellence nor dimension two for this item. Its regular proper birational model hypothesis is retained.

Read the chapter and unit records, the current main-20261015 ancestor proof `lem-per-artin-gabber-affine-curve.proof.md`, and the item's current ancestry. This is a technical input to the existing potential-dualizing surface branch, specifically the passage to completion in 0BGM's first paragraph. It changes no unit step or chapter route and is not the unit key node. Searches of the full imported blueprint for `regular.*closed`, `regular local ring`, `closed point`, `0BG5` and `completed local`, together with full-DAG searches for 02IT, 0BG5 and completed-stalk keywords, found no node giving either new statement.

## Not duplicates

lem-per-regular-closed-point-criterion vs def-weil-regular-scheme: the definition gives the all-stalk characterization, not sufficiency of testing closed points.

lem-per-regular-closed-point-criterion vs rem-pc-regular-normal: that statement gives normality and the disjoint-component/irreducibility conclusions, not the closed-point regularity test.

lem-per-regular-closed-point-criterion vs lem-per-rational-surface-point-blowup-resolution: this is a surface resolution-existence theorem under vanishing hypotheses, not a criterion for regularity of an arbitrary locally Noetherian scheme.

lem-per-regular-closed-point-criterion vs lem-trf-smooth-geometrically-normal: smooth schemes over fields are geometrically regular/normal/reduced; it does not test regularity at closed points.

lem-per-regular-closed-point-criterion vs lem-per-regular-etale-direct-image-base-change: this is a derived etale exchange theorem for regular morphisms, not the 02IT criterion.

lem-per-regular-closed-point-criterion vs lem-trf-regular-perfect-field-smooth: this proves smoothness from regularity over a perfect field and local finite type; it does not establish regularity from closed stalks.

lem-per-closed-fibre-stalk-completion vs lem-weil-pbc-flat-local-completion-iso: the latter assumes a flat local homomorphism, equality of extended maximal ideals and equality of residue fields between Noetherian rings. The new statement gives the completed-stalk comparison for an arbitrary scheme over a Noetherian local base, without Noetherianity of its stalks. Even in the finite-type case, verifying the flat-local hypotheses is additional geometry, not a one-line specialization. The direct 0BG5 quotient calculation does not require those hypotheses.

lem-per-closed-fibre-stalk-completion vs lem-trf-completed-stalk-isomorphism-etale: that theorem assumes an isomorphism of completed stalks and deduces etaleness, under local finite type; it does not supply this comparison.

lem-per-closed-fibre-stalk-completion vs lem-trf-etale-completed-local-ring-iso: this assumes an etale morphism of locally finite type schemes over an algebraically closed field. The base-completion projection in our lemma is not assumed etale or of finite type and has no field-base hypothesis.

Neither new node is a clause of the item: one is a general regularity test, and the other compares stalk completions for arbitrary X, without properness, integrality or regularity. The item's steps still prove global regularity, global sections, normality, integrality, properness and birationality.

## Review by Q42

I reviewed B through E of delivery-errors against the actual statements and sources. Both new nodes introduce their own objects and every hypothesis, state no proof, carry complete blueprint ancestry, cite tag and source label, and record only searches actually in searches.jsonl. I checked the existing Mathlib hits: Noetherian/integral/reduced schemes and categorical regular epimorphisms do not prove the regularity criterion; relative normalization, power series and resolutions of complexes do not prove the item. The additional 0BG5 searches return stalk maps and fibre constructions, equivalences for rings already complete, or Laurent-series completions; none compares these two completed stalks. There are no Mathlib leaves.

Step 1 uses the completion-Noetherian, local-completion-local-ring, mod-ideal and faithfully-flat nodes for exactly their stated conclusions: Noetherianity, maximal ideal and nonzero residue field, completeness, flatness and spectrum surjectivity. The separated-finite-type base-change node gives both properties after any base change. Universal closedness follows directly from its definition and iterated fibre-product universality. The one-affine-cover definition and spectrum quasi-compactness establish Noetherianity of both bases; finite-type-over-Noetherian then applies to T and Y. The locally-Noetherian-quasi-separated node states the absolute property required for global sections. This repairs the earlier relative/absolute mismatch.

Step 2 uses locally-finite-type implies locally-finitely-presented over the now checked locally Noetherian base, and the exact separated birational dense-open isomorphism theorem. Integral schemes have one generic point/component, so both finiteness hypotheses hold; the assumed induced function-field isomorphism is the generic-stalk isomorphism required there. Hence the generic fibre is Spec Frac(A), not merely a scheme with an abstractly isomorphic function field.

Step 3 uses the domain-spectrum and normal-localization statements to check that the base is integral and normal. The proper-normal-geometric-connectedness node requires properness, base normality and integrality, source reducedness, the generic-point image condition and equality of generic-fibre global sections. All are checked using hypotheses and step 2. Its structure-sheaf conclusion, not only connectedness of fibres, gives Gamma(T)=A. The exact flat-ring/affine equivalence turns A->C into a flat morphism, and the qcqs global-sections node gives its actual tensor-product comparison. Step 1 checked both qcqs hypotheses. The resulting equality Gamma(Y)=C is as C-algebras.

Step 4 applies precisely the new 0BG5 statement to X=T and the projection p. A point over the closed point of Spec C maps to the closed point of Spec A because mC contracts to m (step 1's residue-field isomorphism). No regularity of C is assumed. I read 0BG5's proof, not merely its reference in 0BG6.

Step 5 first uses closedness of the proper map to put every closed point of Y in its closed fibre. The definition of regularity gives regularity of the original stalk. Both stalks are Noetherian by local Noetherianity, affine stalk localization and the localization-Noetherian theorem. Applying the regular-local-completion equivalence twice across the comparison from step 4 is therefore legitimate. The new 02IT criterion says exactly that these closed-stalk tests suffice. It imposes no Jacobson hypothesis.

Step 6 uses regular-normal only for normal domain stalks, then the existing finite-product-of-normal-domains global-sections theorem with U=Y. Y is locally Noetherian and quasi-compact, as required. The finite product is nonempty since C has nonzero residue field. If it had two factors the displayed complementary idempotents would both be nonunits in a local ring, a contradiction. This proves normality and domainhood of C without assuming them in the global-sections comparison.

Step 7 proves nonemptiness and connectedness directly by sections and idempotents in the nonzero local ring C. The regular-connected-integral theorem then applies with both nonemptiness and connectedness verified. Step 8 base-changes the actual isomorphism over V, lifts a point of V using the stated spectrum surjectivity, and uses integrality, open-stalk invariance and the affine fraction-field statement to identify generic stalks through f_C. This proves the induced function-field isomorphism, rather than an unrelated field isomorphism.

I tested the item on a field (m=0), on the identity model of a regular local ring and on a regular surface model: the argument uses no dimension bound and includes zero-length resolutions. It excludes the zero ring because A is a domain and its residue field is nonzero. The new 02IT statement includes the empty scheme, a non-Jacobson local spectrum with just one closed point, and disconnected regular schemes; none needs a field-base hypothesis. The 0BG5 statement is vacuous for X empty, works for X=Spec A and m=0, and does not require finite type. Its closed-fibre hypothesis is essential: for A=Q[t]_(t), C=Q[[t]], X=Spec A, the generic stalk completions are Q(t) and Q((t)), and the induced inclusion is not surjective. I did not extend the comparison to that generic fibre or silently assume all completion maps regular. All steps are shorter than 2000 characters. The extracted comparison was the only standalone hidden lemma I found in the retained argument.

Generic tools from other units are declared individually in split_report.tool_uses with their roles; none replaces a unit step. I read every cited node's statement and generated a verbatim quotation for every step/node pair. No definition node is cited for an unstated substantive theorem.

## Retained proof plan for the new completed-stalk node

This is a takeover note, not a split of the new node. Follow 0BG5: on an affine neighbourhood Spec B put B'=B tensor_A C and let p,q be the corresponding primes. Completion mod powers gives B/m^n B = B'/m^n B'. The images of p,q are the same prime in this common quotient, since both are inverse images of their corresponding prime modulo m. Quotient further by its nth power to get B/p^n = B'/q^n, using m^n B subset p^n and m^n B' subset q^n. Localize at p and q to compare the stalks modulo powers of their maximal ideals. All maps come from B->B' and commute with the quotient transition maps, so the isomorphism is induced by the projection on the inverse limits. This is the earlier attempt's explicit local calculation, retained while extracting its independent statement.
