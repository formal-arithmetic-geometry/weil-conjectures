## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-square-zero-etale-extension-criterion.json: existing statement, split in five steps; no exact Mathlib match.
- citations.json: one verbatim statement quote for each cited node in each proof step.

Attachments: none for this item. The already attached, closed theorem Algebra.exists_etale_coefficientLift (lean/WeilConjectures/RingTheory/EtaleAlgebraLift.lean:74) supports the existing node lem-exc-etale-algebra-lift, which is reused rather than recreated.

WANTED: none.

The imported statement agrees with Stacks Tag 05YT, algebra.tex, lemma-lift-etale-infinitesimal. Its explicit canonical comparison correctly specifies what the source's equality of kernels means. No statement correction was made. The empty imported proof is replaced by the source's lift-and-compare proof, with its balancing and exact-row arguments supplied. The tensor-product definition was added to statement dependencies. All inherited citations and searches were retained. Searches made during this attempt are recorded exactly from searches.jsonl; its completed leanfinder results were read from that log after a provider interruption removed the local session. None asserts the entire criterion. Related hits supply formal lifting, not the extra algebra-construction and kernel-comparison argument of this item.

I searched all project WeilConjectures sources for the blueprint tag and for square-zero etale and lifting terminology, and inspected the relevant RingTheory results. No project declaration states this criterion with all its hypotheses and conclusion without sorry. The quotient-lifting theorem found is a supporting theorem, not an attachment for this item.

## New nodes

None. Zero Mathlib leaves created. The existing nodes already provide every substantive input.

## Not duplicates

No new-node pairs. The whole DAG searches for Tag 05YT and lemma-lift-etale-infinitesimal found the item and its two citers, not a reusable proof of the item. Blueprint searches for 05YT, lift etale, formally smooth, flat ideal, etale ring, and infinitesimal lift were inspected. The lift-etale search found lem-exc-etale-algebra-lift, so I reused it. Further statement/title searches located the existing affine criterion, lifting, flatness, conormal comparison and tensor-product definition. No duplicate was created.

## Route and blueprint

I read SETUP.md's chapter/unit/node distinction, GOAL.md, the chapter and unit records, and the current latest blueprint sk-thm-sf-ctf-stability files, including its direct-images proof. This is a lower algebra tool on the inherited deformation/alteration branch, not a replacement for a unit argument. The existing long blueprint.from.place and via chain are retained. blueprint_refs.py ancestor reports blueprint.from.node = None for this item, already present in the live record; there is no invented ancestor. The split_report explains the precise algebra use of Tag 05YT in Tag 05ZT. lem-exc-etale-algebra-lift is the generic quotient-lifting tool from another unit; its use is declared in split_report.tool_uses. The remaining theorem inputs are existing Mathlib leaves, and no new off-route theorem is introduced.

## Review by Q134

I read algebra.tex Tag 05YT (lemma-lift-etale-infinitesimal), its preceding lemma-lift-etale (Tag 04D1), Tag 031J (proposition-characterize-formally-smooth), and Tag 00U2 (lemma-etale), including clause (6). I also read morphisms.tex Tag 02GJ (lemma-etale-characterize) and Tag 0473 (lemma-conormal-functorial-flat), including its affine proof. The online Tag 05YT agrees with the local text. For the reused lifting theorem I opened both the node statement and the project declaration Algebra.exists_etale_coefficientLift, including its arbitrary quotient, etale and finite-presentation conclusions, and the specified reduction isomorphism. There are no new nodes needing a source review.

Step 1 uses exactly the final sentence of lem-exc-etale-algebra-lift, which gives a lift for every etale finite-presentation quotient algebra without nilpotence restrictions. The existing affine criterion says that scheme etaleness is equivalent to the finite-presentation/H1/Omega ring criterion; it gives the required input and translates the output. The identification A+/ker(p) with A is written by classes and lifts, using surjectivity, not assumed to be an equality of rings. The quotient isomorphism is an A-algebra isomorphism, so r v = u p is established for the given u.

Step 2 uses the affine criterion's actual H1 and Omega vanishing clauses and lem-weil-pbc-smooth-ring-map-square-zero-lifting, whose statement I opened. This latter node requires H1 = 0 and projectivity of Omega, not merely an etale label: Omega is zero and its projectivity follows from its unique lifting maps. The target algebra is B+ with structure map u+; commutativity q u+ = u p verifies linearity of r after identifying B+/J with B. Its square-zero hypothesis is precisely J^2 = 0. No splitting of p or q is assumed.

Step 3 uses lem-weil-pbc-etale-algebra-flat, which explicitly applies to the etale map of spectra already obtained, and the flat clause of lem-weil-pbc-ideal-cotangent-flat-base-change-ring. I opened both statements and checked the latter map is the actual multiplication comparison, rather than an unspecified abstract isomorphism. Products of the ideal generators give (IC)^2 = 0. Its cotangent quotient therefore reduces to I tensor over A+ with C mapping isomorphically to IC. The remaining change of tensor base is elementary: its two maps on pure tensors and the independence of lifts are written in the step. In particular i tensor v(i_k)c_k equals i_k i tensor c_k, hence is zero; this uses I^2, not J^2. def-weil-pbc-module-tensor-product supplies exactly the balanced bilinear universal property and generation by pure tensors.

Step 4 is an elementary calculation from steps 2-3 and the assumed beta. It computes phi(theta(i tensor b)) = u+(i) phi(c), and q(phi(c)) = b shows that this is beta on the specified generator. Thus the isomorphism is the restriction of this phi, not an unrelated isomorphism between its kernel modules. Changing the lift in B+ uses J^2 = 0. The tensor definition cited here gives equality from equality on pure tensors. This checks C4 for the only citation in this step.

Step 5 is the explicit two-row argument: a kernel element lies in IC and hence vanishes; a preimage modulo J can be corrected by an element of IC. It uses no five-lemma node, finiteness condition, Nakayama lemma or Noetherian assumption. The inverse ring map is justified by injectivity, so the isomorphism respects the specified A+-algebra maps. Substituting this identification into etaleness of C, and using the already quoted affine criterion, gives the requested spectrum statement. This is elementary use of an isomorphism, not a hidden rigidity theorem.

I checked delivery-errors B through E against these files. There is no new statement-only node or proof sketch to audit, no relabeling of the item into a new lemma, no appeal to the proof of a cited node, and no omitted non-elementary source input. Every use has a quote in citations.json, copied from the current statement. I checked the dependency direction: the cited flatness, conormal and lifting statements do not depend on this criterion. No proof step exceeds 2000 characters. I corrected the potential ambiguity in the source's final sentence by comparing the actual kernel map and proving surjectivity directly, so the proof does not assume J = IB+ before establishing it.

Edge cases checked: I = 0 forces J = 0 by the assumed comparison, and the proof reduces to the given etale quotient map. If B is the zero ring, J = J^2 forces J = 0, hence B+ is zero; the proof still works. For a split extension A+ = A plus a square-zero module I and the base-changed extension B+ = B plus (I tensor_A B), the theta/beta formulas give precisely the usual scalar-extension map. The necessity of the comparison is visible in k -> k[epsilon]/epsilon^2 over the identical quotient k -> k: I = 0 and J nonzero, so beta is not an isomorphism and the map need not be etale. Neither finiteness of I or J nor finite type of the base is used.

What changed after this reading: I retained the item statement, reused the already existing lifting and conormal nodes instead of creating new ones, supplied explicit balancing formulas and the kernel compatibility calculation, and expanded the last isomorphism assertion into injectivity and surjectivity. Nothing mathematical remains unfinished at this one-level split.
