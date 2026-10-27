## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-finite-kernel-cone-translates.json: statement, split; unchanged statement; no exact or one-line Mathlib match.
- citations.json: the single proof citation with a verbatim statement excerpt.
- report.md: this report. searches.jsonl is maintained by the required search command.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. The project source has no declaration with the item's blueprint tag, nor a matching finite-kernel cone-translate declaration under the concept searches. The existing Sheaf/Paper/GordanRationalCone.lean is a different, lattice-only theorem and its proof is sorry; it is not an attachment for this item.

WANTED: none.

The imported node had no proof. Its statement is correct and unchanged, and its existing statement dependency def-weil-pbc-free-module is retained. The existing lem-trf-gordan-rational-cone-finite already states the exact lattice finite-translate assertion needed. It must be reused rather than recreated. No statement dispute arose. The historical ancestry points to local-term locality, but the latest blueprint now proves that theorem through contracting correspondences: this auxiliary algebra fact belongs to the older nearby-duality/alteration chain recorded in the node, not to an argument actually written in the newest local-term proof. I have preserved that ancestry and recorded the distinction in split_report.blueprint.

Nothing remains unfinished for this one-level split. The reused lattice lemma is already split and reviewed, but its Lean proof remains sorry; this delivery claims a stage-1 proof only.

## Not duplicates

No new nodes. In particular, lem-trf-gordan-rational-cone-finite is reused, not duplicated. Its statement assumes the ambient group is a lattice; the item allows a finite kernel and torsion in G, and its proof explicitly lifts the lattice result. The old item itself is not a Mathlib leaf: the equalizer version AddSubmonoid.fg_eqLocusM does not give translates by the specified monoid in one line. The search hits on fibres only give the elementary fibre bijection, which is written out in Step 2 rather than made into a new node.

## Review by Q62

I read coord/brief-stage1.md, stages/1-dag.md, the three levels and tool-use requirements of SETUP.md, GOAL.md, the worker role, and delivery-errors.md B--E. I read the chapter and unit records and the current blueprint proof of lem-trf-local-term-locality. I checked that no released stage-1 repair note exists. There was no prior sandbox split or report to preserve.

For the item source I read ILO, Expose VIII, Lemma 3.2.9 and its proof, printed page 104 (PDF page 110). It states finiteness of the saturated toric morphism but does not supply the lattice/finite-kernel argument. The expansion is therefore honestly marked proof_origin.by=agent. There are no new-node sources to review. I also read the existing Gordan node in full and its Lean file, and read def-weil-pbc-free-module to check that the statement dependency really defines a basis/free module. Its definition includes empty bases. No SGA source is used.

Step 1 uses only lem-trf-gordan-rational-cone-finite. I checked its statement, not merely its proof: it allows a finite list with r=0, assumes a free abelian group with a finite integer basis, defines the same rational cone and natural-combination monoid, and supplies a finite E in C intersect L with precisely the required translate equality. Here v_i=pi(p_i), L has exactly that basis hypothesis, and the canonical lattice embedding is the same. The equality P_L=pi(P) is established by writing both expressions explicitly. citations.json quotes the actual finite-translate sentence verbatim. The node is in the same unit, so no off-unit tool declaration is required.

Step 2 cites no external statement: for each of the finitely many e choose a preimage a_e, possible by the item's surjectivity. The explicit inverse maps k -> a_e+k and g -> g-a_e identify the fibre with K. Thus the full inverse image F is a finite union of images of the finite K. Its containment in Q follows from E contained in C. This is a few-line elementary argument, not a hidden lemma. Taking the full fibres, rather than choosing just one lift of each e, is essential to absorb torsion and all residual kernel elements.

Step 3 cites no new fact: the natural-number coefficients from Step 1 lift to p=sum n_i p_i; f=g-p has image e and so belongs to F. For the reverse inclusion I checked closure by adding the nonnegative rational coefficient expressions, so there is no unsupported appeal to saturation or to generation of G. This proves both inclusions with the actual given generators. Every non-elementary fact used is the one cited lattice statement; the union of all uses is exactly proof_deps. Each step has fewer than 2000 characters.

I tested r=0: C={0}, P={0}, Q=K and the construction gives F=K. With rank L=0, Q=G=K is finite; taking all fibres still works even when the p_i are torsion. For G=Z plus Z/2 and generator (2,0), the two parity remainders in L must each be lifted through both torsion values, which our construction does. For L=Z^2 and the sole generator (2,0), the generators do not span L or G, yet the cone points have second coordinate zero and finite remainders still suffice. For v=(1,-1) in Z, the cone contains a line and P_L=Z; the proof makes no positivity or pointedness assumption. For pi=id and v=(2), the two remainders 0 and 1 give the familiar decomposition of N modulo 2. Zero and dependent generators change none of the steps.

I searched the whole DAG by cone/Gordan/finite-translate terminology and searched the blueprint with blueprint_refs.py (including rational cone and finite kernel); the ancestor command confirms lem-trf-local-term-locality. I searched project Lean by tag and concept. Mathlib searches were run only through msearch.py: two semantic phrasings, LeanSearch, Loogle and grep, all logged without invented queries. The grep found the equalizer Gordan lemma at GroupTheory/Finiteness.lean:628, which I read with its hypotheses; its conclusion is finite generation of an equalizer, not this specified-translate cover. Semantic hits concern number-field fundamental cones, cone preimages, semilinearity, affine monoid generation or additive fibres, and do not state the full item. No Mathlib declaration was promoted to a leaf based on its name alone.

I checked delivery-errors B--E against the resulting files: no new statement-only-node issue or missing definition; unchanged statement and correct source; no unrun search, circular dependency, unsupported citation, clause moved to a new node, or long hidden argument. The only correction needed was to the initial plan: once the existing lattice lemma was found I reused it and removed the need for a fresh bounded-coordinate argument.
