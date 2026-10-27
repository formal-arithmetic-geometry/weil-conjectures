# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adequately-affine-composition.json: item, statement unchanged, three-step split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcqs-composition-affine.json: statement-only support, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcqs-algebra-direct-image.json: statement-only support, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-algebra-pushforward.json: statement-only support, unsplit; no Mathlib match.
- citations.json: verbatim statement quote for every node used by each of the three proof steps.
- report.md and sandbox-only search-results.json/searches.jsonl retain the actual searches and their answers; search.py, write_split.py and write_report.py are sandbox scratch scripts.

## Attachments

None. Searched WeilConjectures/ for the blueprint tag, adequately affine, adequatelyAffine, AdequatelyAffine, universally adequate, and the supporting concepts. There is no project declaration stating either clause; unrelated scheme quasi-coherent pushforward results do not attach this stack theorem. Existing Sheaf/ quotient placeholders are neither WeilConjectures declarations nor this theorem.

## Literature requested

WANTED: literature/alper-adequate-moduli-spaces-arXiv-1005.2398.pdf, Proposition 4.2.1(1),(2) and Lemma 4.1.7, for lem-sfb-adequately-affine-composition and lem-sfb-adequate-algebra-pushforward. The local PDF is absent; the primary HTML/PDF at https://arxiv.org/html/1005.2398v3 and https://arxiv.org/pdf/1005.2398v3 were read online, without downloading. Accordingly the assembly is recorded with proof_origin.by = agent. New nodes contain statements only.

## Problems found and corrections

The item had no proof. A tempting application of g's definition directly to f_*A to f_*B is invalid: the latter is universally adequate but need not be surjective. Alper 4.1.7 supplies the correct stronger preservation input. I made that an independent node about arbitrary algebra maps, rather than moving the composition conclusion to a new node. None of the new nodes asserts adequate affineness of a composite or of an affine map.

The big-fppf versus smooth-etale distinction matters: Stacks stacks-cohomology.tex, section-pushforward-quasi-coherent, gives a counterexample to naive big-fppf direct image preserving quasi-coherence. The new direct-image statement instead uses the quasi-coherent right adjoint and explicitly identifies only its smooth-test restriction with the section formula. It does not assert arbitrary base change or naive big-fppf quasi-coherence. Source Tags 077A, 0GQQ and 0GQR give exactly this distinction.

The supplied three-level route and current latest blueprint proof (3) were read, including the adequate-product-affinization parent. This item is a supporting input, not the unit's key statement. No unit realization is changed. The ancestor command returns None for this inherited created-node chain, and blueprint.from.node is already null; I preserved it and the full concrete from.place rather than inventing a blueprint id. Whole-blueprint searches for adequately affine, universally adequate, 4.1.7, 077A, 050W, quasi-coherent pushforward, quasi-compact composition and adequat found no same statement. The missing historical coord/dag-sync.md is not a mathematical dependency.

## Unfinished work

No unfinished part of this item's assembly. The three new nodes deliberately remain unsplit for later workers, as required by a one-level stage-1 split. No Lean was written or compiler invoked. No repository or launcher file was modified.

## Review by Q14

I read Alper Proposition 4.2.1(1),(2), its proof, Definition 4.1.1 and Lemma 4.1.7, especially the proof of (2) implies (1) before its Noetherian variants. The source's proof itself concludes preservation of universally adequate algebra maps. I chose precisely that weaker consequence for the new adequate-algebra-pushforward input, avoiding the separate adequate-homeomorphism notion and avoiding a finite-presentation assertion. This input is about arbitrary algebra homomorphisms over one adequately affine map, rather than a clause of the item about composition of maps of stacks. It is not a two-line consequence of the definition: the source uses the image factorization and an injective descent/equalizer argument.

For the new compactness input I read stacks-morphisms.tex lemma-composition-quasi-compact (050W), lemma-composition-separated (050K), including its quasi-separated clause and diagonal factorization, lemma-characterize-representable-quasi-compact (050T), lemma-representable-quasi-separated-diagonal-quasi-compact (04YT), definition-affine (0CHQ), and morphisms.tex lemma-affine-separated (01S7). The source applies to general algebraic stacks, whereas the nearby separation nodes either assert separatedness alone or only treat Deligne--Mumford stacks. A representable affine map is quasi-compact on scheme tests and has a closed-immersion diagonal; hence it meets the specified stronger stack quasi-separated convention. This node is a geometric compactness/separation input, not adequate affineness disguised as a new node.

For the new direct-image input I read stacks-cohomology.tex proposition-direct-image-quasi-coherent (077A), lemma-direct-image-quasi-coherent-over-flat (0GQQ), remark-direct-image-quasi-coherent-tensor (0GQR), and lemma-quasi-coherent-check-exact (0GQF). The first is the QCoh right adjoint, the second gives equality of its sections with naive direct image on flat, hence smooth, tests, and the third supplies multiplication. Their algebra form gives the commutative-algebra right adjoint. Its composition is the unique right adjoint to composite tensor pullback. Exactness can be checked on flat surjective scheme charts, which accounts for the surjection comparison on smooth-etale tests. No global quasi-compactness of either stack is added. I separately reread the whole statement of the existing lem-sfb-stack-affine-algebra-direct-image: it explicitly promises preservation of surjections for affine maps and the smooth-chart characterization, not merely an adjunction.

Step 1 uses the definition's qcqs requirement and universal-adequacy condition, the compactness node's composite clause, and the direct-image node's QCoh and smooth-test clauses. Both f and g meet qcqs before that node is applied. The arbitrary quotient algebras need not be finite type. Step 2 uses the new adequate-algebra-pushforward statement with g as its adequately affine map and C to D as its universally adequate input; surjectivity of C to D is not required. The direct-image node supplies the functorial algebra composition identification, so the target map is genuinely h_* of the original surjection. The definition then concludes adequate affineness. Step 3 uses the compactness node's affine clause, the existing affine direct-image node's exact surjection clause, and the new smooth-test surjection comparison. On an etale cover a genuine lift, with exponent 1, satisfies the definition of universal adequacy. Each cited statement was opened in full and its actual sentence is copied verbatim into citations.json; no step imports a fact from a cited node's proof.

I tested the new statements on identity maps, empty source/empty stack (the zero ring is allowed), arbitrary affine algebras with infinitely many generators, and characteristic p quotients where a power lift exists but a section lift fails. The qcqs and QCoh statements have the required relative, not absolute, hypotheses. The preservation lemma allows noninjective and nonsurjective maps, as in its source; it imposes no common exponent or Noetherianity. In particular a group-stack example with nonaffine absolute diagonal is not excluded. The affine clause only needs exponent 1, while the composite clause makes no such claim. These checks exposed no statement dispute. No source error, SGA dependency, route departure, or hollow construction was introduced.

I reviewed delivery-errors B--E: new nodes are self-contained statement-only inputs with definition dependencies, source places and real logged searches; all uses are stated citations; no cycles through the parent are introduced; none of the new nodes merely restates an item clause. Mathlib candidates were read: QuasiCompact.lean:156 and QuasiSeparated.lean:116 are about schemes, Modules/Sheaf.lean:231 is scheme pushforward composition, and Sheaf/Quasicoherent.lean:329,340 needs preservation-of-colimits or a left-adjoint site functor with an isomorphic ring map. These hypotheses do not provide general stack QCoh direct image or its chart comparison. Tilde.lean:567 even records a relevant scheme-level TODO. All three new inputs therefore remain unsplit, with zero Mathlib leaves. The item proof is 1924 characters total; no step exceeds 2000 characters or hides a separate standard lemma.

## Not duplicates

lem-sfb-stack-qcqs-composition-affine vs lem-a1-etale-affine-finite-fibre-refinement: the existing statement refines an etale scheme cover over affine schemes, not qcqs composition for algebraic stacks.

lem-sfb-stack-qcqs-composition-affine vs lem-sfb-stack-separation-compactness-permanence: the existing statement gives separatedness under base change/composition, not quasi-separatedness and quasi-compactness for general stack morphisms.

lem-sfb-stack-qcqs-composition-affine vs lem-sfb-dm-etale-atlas-calculus: the existing statement is about etale atlases and etale morphisms of DM stacks, not arbitrary qcqs morphisms of algebraic stacks.

lem-sfb-stack-qcqs-composition-affine vs lem-sfb-space-integral-qcqs-permanence: the existing statement is about integral morphisms of algebraic spaces and absolute compactness, not general stack composition.

lem-sfb-stack-qcqs-composition-affine vs lem-sfb-etale-stabilizer-preserving-affine-moduli: the existing statement concerns stabilizer-preserving etale maps in a specific finite-flat quotient situation, not arbitrary stack qcqs composition.

lem-sfb-stack-qcqs-composition-affine vs lem-sfb-stack-separation-composition: the existing statement gives separatedness for DM stacks, not qcqs for arbitrary algebraic stacks.

lem-sfb-stack-qcqs-composition-affine vs lem-sfb-stack-qcqs-atlas-affine-diagonal: the existing statement assumes a scheme target and a specified qc atlas with affine diagonal, not a general composite with a stack target.

lem-sfb-stack-qcqs-composition-affine vs lem-weil-pbc-affine-morphism-permanence: the existing statement concerns affine scheme maps, not general algebraic-stack compactness/separation.

lem-sfb-stack-qcqs-composition-affine vs lem-weil-pbc-finite-over-separated-finite-type: the existing statement concerns finite and separated finite-type scheme maps, not arbitrary qcqs stack maps.

lem-sfb-stack-qcqs-composition-affine vs lem-weil-pbc-etale-limit-tail-open-geometry: the existing statement concerns inverse systems and etale scheme geometry, not arbitrary qcqs stack maps.

lem-sfb-stack-qcqs-algebra-direct-image vs lem-sfb-stack-affine-algebra-direct-image: the existing statement requires an affine map and supplies exactness, while the new statement allows arbitrary qcqs maps and supplies only the QCoh right adjoint, composition, and smooth-test comparisons; the exact affine case is reused in step 3.

lem-sfb-adequate-algebra-pushforward vs lem-coef-lax-cartesian-classification: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-relative-symmetric-monoidal-localization: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-many-object-operad-accessibility: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-infinity-essentially-small-cocones: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs def-coef-integral-derived-coefficients: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-combinatorial-localization-presentability: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-infinity-pointwise-cocartesian-transport: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-system-localization-universal: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-cocartesian-horn-completion-comparison: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs def-coef-presentable-infinity-category: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-joyal-presentable-monoidal-localization: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-small-monoidal-full-subcategory: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-infinity-small-full-subcategory: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-locally-small-infinity-size-calculus: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs lem-coef-infinity-cocartesian-composition-initiality: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

lem-sfb-adequate-algebra-pushforward vs def-weil-pbc-small-proetale-site: the existing statement has different hypotheses/conclusion and does not assert preservation of universally adequate algebra maps under an adequately affine pushforward.

The parent adequate-product-affinization uses the present item; it does not state or prove the new preservation, compactness, or QCoh inputs. The existing adequately-affine affine-target-base-change and affine-target-adequacy-criterion nodes are different assertions and cannot replace any new input. No whole-blueprint duplicate was found.
