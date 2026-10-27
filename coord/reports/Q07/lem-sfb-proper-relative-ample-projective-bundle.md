# Q07 stage-1 delivery: lem-sfb-proper-relative-ample-projective-bundle

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-relative-ample-projective-bundle.json: item, statement, split into five steps; statement and statement dependencies unchanged; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-very-ample-finite-type-realization.json: new statement-only unsplit lemma; no Mathlib match. It replaces an arbitrary quasi-coherent very-ample realization by a finite-type one, without assuming properness.
- citations.json: nine verbatim node-statement quotations for the nine step/node citations.
- searches.jsonl: actual msearch records retained; no invented or unavailable-as-negative search.
- report.md: this report.

## Attachments

None. Searched the project source under lean/WeilConjectures both for the exact blueprint tag and for relative ampleness, very ampleness, projectivity and the finite-type realization. The affine-base theorem exists_isImmersion_projectiveSpace_of_isAffineOpen in AlgebraicGeometry/ProjectiveSpace/OfAmple.lean requires an affine base and does not state this item or the new qcqs-base lemma. In AlgebraicGeometry/Morphisms/Projective.lean, IsProjective is H-projectivity plus quasi-compactness; it is not the finite-type quasi-coherent projective-bundle convention of this item. Hence that class provides no attachment.

## WANTED

None. All source text used is present in literature/stacks-project. The inherited coord/dag-sync.md reference points to a file absent in this live repository; this delivery follows the explicit live-repository/direct-delivery brief instead.

## Audit of the imported item and blueprint

The item's statement agrees with Stacks 0BCL(1) and Definitions 01VW(1), 01VH and 01W8(1). It is true without Noetherianity and without the resolution property on the base. I kept it verbatim. The item had no proof and no Lean audit giving a finished declaration. The essential point missing from a naive one-line ample-to-very-ample argument is that the module in a very-ample realization need not be of finite type. The new proper-free lemma records precisely the finite-type approximation in the proof of 07RM, after the initial passage to a very ample power. Properness is then used in the item's own argument to close the immersion.

The current blueprint unit file in main-20261015 and the recorded chapter/unit were read. This is a subsidiary scheme-theoretic tool in the modification-tower branch already fixed by the item's blueprint.from.place and via chain, not a replacement of a six-functor argument or a change of the unit statement. tools/blueprint_refs.py ancestor reports blueprint.from.node = None for the item. The inherited null ancestor is retained and the new node prepends this item to the existing via list. Blueprint searches for quasi-projective, 07RM, open projective, very ample, finite type realization, projective bundle, 01VU and 01VR found no blueprint node stating the new lemma. The curve/field very-ample and quasi-projective results are insufficient over an arbitrary qcqs base.

The live DAG also contains lem-per-proper-relative-ample-projective-bundle with the exact same statement as the item, currently unsplit. I have not created a second version of it, changed its file, or used it as a one-step restatement of the conclusion. This existing duplication is flagged for maintainer deduplication. Its eventual merge is outside this worker's ownership.

## New lemma and search review

lem-sfb-very-ample-finite-type-realization follows the construction in morphisms.tex, Tag 07RM, lemma-quasi-projective-open-projective, starting immediately after the replacement by a relatively very ample power and ending at the immersion r_{L,psi_i}. I also read 01VR (lemma-relatively-very-ample), 02NP (lemma-very-ample-finite-type-over-affine), and properties.tex 01PK (lemma-directed-colimit-finite-presentation) to check that the stronger intermediate statement with a fixed very ample module is supported. The quotient-compatible pullback of O(1) is supplied by the projective-bundle quotient construction, not by a new properness assertion.

The new node is not split. For the next worker, the source argument to expand is: put F=f_*N, use quasi-coherence for the quasi-compact and quasi-separated f, write F as a directed colimit of finite-presentation quasi-coherent modules on qcqs S, and lift simultaneously the finite affine-local collections of sections giving the immersions. At a common index the evaluation quotient to N is surjective. Its induced map to P(E_i) is an immersion locally on S: the lifted local sections give the known projective-space immersion, with the comparison from P(E_i) taken on the open where those sections generate the tautological quotient. The image of X is contained in that open. This supplies finite type, not local freeness, and pulls O(1) back to the original N. This discussion belongs in the report only; the new node has no proof or proof dependencies.

For this node, ran msearch leanfinder and leansearch with two different phrasings, Loogle with AlgebraicGeometry/VeryAmple, and grep for very ample/relative ample/quasi-projective. Read all returned signatures. Ordinary Proj construction/properness, quasi-affine immersions, finite generation of invertible modules and general generating-section predicates do not give an immersion into a finite-type relative projective bundle. Loogle and both relevant grep queries returned zero hits. For the item also ran a proper-relative-ample leanfinder query, a separate proper-relative-ample leansearch query, Loogle AlgebraicGeometry/IsProjective, and a second grep phrasing. These return only properness or closed-immersion constituent facts, already represented in the DAG. All new recorded queries match searches.jsonl exactly. The item's pre-existing Q28 search records were retained rather than fabricated anew.

## Not duplicates

lem-sfb-very-ample-finite-type-realization vs lem-trf-relative-ample-very-ample: the existing lemma produces a very ample power and permits an arbitrary quasi-coherent realizing module; the new lemma starts with a fixed very ample N and makes the realizing module finite type over a qcqs base.
lem-sfb-very-ample-finite-type-realization vs def-trf-relatively-very-ample: the definition imposes no finiteness on the realizing module; the new result proves finite-type realization using finite type of f and qcqs of S.
lem-sfb-very-ample-finite-type-realization vs lem-sfb-proper-relative-ample-projective-bundle: the new lemma assumes no properness, starts with very ampleness and concludes only an immersion; the item derives closedness from properness and only assumes relative ampleness.
lem-sfb-very-ample-finite-type-realization vs lem-per-proper-relative-ample-projective-bundle: the same distinction applies; that pre-existing item is the proper/ample criterion, not finite-type realization of a fixed very ample module without properness.
lem-sfb-very-ample-finite-type-realization vs lem-trf-proper-fibrewise-ample-projective: that node assumes Noetherian schemes, properness and one-dimensional geometric fibres with positive degrees; none is assumed by the new lemma.
lem-sfb-very-ample-finite-type-realization vs lem-pc-very-ample-descends: that lemma descends very ampleness along a field extension and does not construct a finite-type module over a general qcqs scheme.

No existing node with source Tag 07RM was found by the whole-DAG source/tag searches. The delivery tool's further same-tag pairs, if any, will be checked before push.

## Review by Q07

I read the item against morphisms.tex 0BCL, including its reference to the open-projective factorization in 07RM, and checked the proper and projective definitions rather than treating H-projectivity as interchangeable. The added lemma was checked against the actual intermediate finite-type construction of 07RM and the auxiliary source passages named above. Its statement introduces f, X, S, N, E, r and the structure morphism, states every base and finite-type hypothesis, uses the actual degree-one twist, and cites definition nodes for its notions. It is a non-elementary approximation lemma, not an elementary rearrangement or the item's own conclusion.

For step 1 I read def-weil-proper-morphism, whose statement explicitly includes finite type, and def-weil-finite-type-morphism, which includes quasi-compactness; taking these conjuncts is elementary. I corrected the source tags from the section tags 01W0/01T0 to the actual definition tags 01W1/01T1.

For step 2 I read lem-trf-relative-ample-very-ample: it explicitly assumes finite type of the morphism and quasi-compactness of the base and gives a positive relatively very ample power. These hypotheses are exactly available from step 1 and the item. def-trf-relatively-very-ample explicitly says its module is invertible, so N satisfies the next lemma's invertibility hypothesis without an uncited tensor-power lemma.

For step 3 I checked the new node's statement supplies a finite-type quasi-coherent E and an immersion over S, including pi_E r=h. Quasi-separatedness is used here together with quasi-compactness of S; it is not silently replaced by separatedness or affineness of intersections. The passage from arbitrary quasi-coherent E to finite type is not hidden in step 2 or claimed from a coherent-pushforward theorem requiring a Noetherian base.

For step 4 I read lem-trf-projective-bundle-separated in full. Its statement applies to an arbitrary quasi-coherent E, so certainly applies to this finite-type E. I also read lemma-nagata-proper-to-separated-target: its statement is exactly the proper-over-base, separated-target-over-base triangle used with T=X, Y=P_S(E), B=S. The triangle commutes by step 3, and h is proper by hypothesis. These are generic tool lemmas; the two non-Mathlib off-unit tools (relative ample/very ample and projective-bundle separatedness) are declared in split_report.tool_uses with their specific purpose.

For step 5 I read lem-weil-pbc-proper-immersion-closed. It requires precisely properness and an immersion and concludes a closed immersion, as needed; I did not merely cite a definition of properness for this implication. Its source 01IQ together with 01W6 was read. The final application of def-trf-projective-bundle-morphism uses the same E, known finite type and quasi-coherent, and the same commuting factorization. It proves projectivity in the bundle convention and claims no embedding into a finite projective space.

I checked small cases before finalizing the new statement: an empty source has the unique immersion and unique invertible module; an empty base forces the source empty; a field base reduces to a finite collection of homogeneous sections giving a usual projective-space immersion. For A^1 over a field with its very ample trivial bundle, the immersion into P^1 is open and need not be closed, illustrating why the new node does not subsume the properness part of the item. Over non-Noetherian qcqs bases the module E need only be finite type, not coherent or locally free. I have not used a uniform vector-bundle presentation or the resolution property. Dropping finite type of f was not attempted. No statement dispute was found.

Against delivery-errors B through E: the single new node contains a statement only, all its objects and definitions are specified, sources have verified Stacks tags/labels, all searches actually ran and were read, and all blueprint/DAG/source searches precede creation. Every non-elementary fact in the five-step item proof has an explicit node citation whose statement supplies that fact; citations.json copies these statements verbatim. No step cites a definition for an unstated theorem. The only elementary step is extraction of defining conjuncts. The remaining proof is a sequence of genuinely smaller results, with the properness-to-closedness argument carried by the item. Each step is shorter than 500 characters, so no long step hides an auxiliary comparison. No SGA source, Lean writing, compiler, Lake, local project checker, or repository mutation was used.

## Unfinished work

The new finite-type realization lemma is intentionally statement-only, as required for a one-level split. No part of this item's natural-language proof remains unwritten. Server preflight and delivery results are recorded below after the required checks.
