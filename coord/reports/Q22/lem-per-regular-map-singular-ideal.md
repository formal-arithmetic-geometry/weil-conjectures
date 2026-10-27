# Q22 stage-1 report: lem-per-regular-map-singular-ideal

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-regular-map-singular-ideal.json: item split into five proof steps; statement and statement dependencies retained. Mathlib verdict: no exact match after both natural-language phrasings, Loogle, LeanSearch and source grep.
- citations.json: twelve verbatim statement quotations, one per step/node citation.
- report.md: this report. searches.jsonl is the search command's unchanged log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project Lean tree for the blueprint tag and absolute singular-locus names. There is no project declaration for this item. Existing relative Popescu singularIdeal declarations concern the nonsmooth locus of a finitely presented algebra, which is a different notion and does not attach this absolute comparison.

## WANTED

None for this proof. The inherited source place mentions a wanted archival copy of Rotthaus (1979), but this split uses the locally available Stacks sources exclusively and makes no claim to have read Rotthaus. That inherited provenance is retained without using it as evidence.

## Problems found and changes

The item was statement-only. Its statement is true as written, including the absence of a global faithful-flatness assumption. No statement dispute, hypothesis addition, or weakened conclusion was needed. No prior sandbox item or report existed.

The proof now isolates the distinction between equality of underlying singular loci and equality of their defining ideals: the latter needs reducedness of S/s(R)S, not just the primewise equivalence. The regular-base-change theorem available in the DAG assumes finite type of the base change; R to R/s(R) meets this requirement even though the original regular map need not have finite type. Quotient Noetherianity and radical/reduced-quotient implications are written out directly rather than left as uncited facts.

Read the chapter/unit records and latest blueprint ancestor proof, especially lem-per-artin-gabber-affine-curve Step 3. This node lies far below that ancestor through the existing singular-ideal patching chain; its generic commutative-algebra comparison changes neither chapter nor unit. Stacks-based tools from other units are declared in split_report.tool_uses. No SGA source is used.

## Not duplicates

No new nodes were needed. The existing local-regularity, base-change, reducedness, tensor-quotient and radical-intersection nodes cover all inputs. Searched the whole DAG by tags 07QK, 07C0, 07C1, 031E and 00OF and by regular-map/localization/radical/singular-ideal keywords; blueprint_refs searches for regular homomorphism, singular ideal, and radical found no exact blueprint statement of this item. Reused lem-weil-pbc-zero-locus-eq-iff-radical-eq rather than creating a second radical/vanishing-ideal node.

## Review by Q22

I read More on Algebra's regular-map definition and locality lemma (07BZ and 07C0), finite-type regular base change (07C1), and reducedness ascent (07QK), in literature/stacks-project/more-algebra.tex. I also read Algebra's flat local descent (00OF), flat local ascent with regular closed fibre (031E), and the Zariski radical/intersection statements (00E0) in literature/stacks-project/algebra.tex. The proof is my explicit assembly of these Stacks results; it does not purport to be a verbatim proof from an unavailable paper. There are no new-node sources to review.

For Step 1 I opened the statements of lem-weil-pbc-regular-local-maximal and lem-weil-pbc-localization-noetherian. The former gives exactly regularity of the induced map at each target prime, with Noetherian target, and the latter gives Noetherianity of both localizations. I checked def-weil-pbc-g-ring: regular maps are flat and their fibres are geometrically regular; choosing the trivial finite purely inseparable extension gives ordinary regularity of the closed fibre. def-weil-pbc-localization-at-prime supplies the local rings, maximal ideals and fibre-as-quotient description. The fraction formula verifies localness, so no unstated local-map assumption enters Step 2.

For Step 2 I opened lem-weil-pbc-flat-over-regular-with-regular-fibre and lem-weil-pbc-flat-under-regular. They respectively give the forward and reverse regular-local implications, under precisely the flatness, Noetherianity and localness just established. The reverse implication is local descent, not global faithfully-flat descent. The resulting equivalence at every prime is exactly the set-theoretic singular-locus assertion.

For Step 3 I opened lem-weil-pbc-zero-locus-eq-iff-radical-eq. It explicitly states both the intersection-of-containing-primes formula and equality of zero loci for equal radicals. Closedness of Sing(R) gives V(J); the cited formula identifies s(R) with sqrt(J). Radicality of an intersection of primes and the equivalence IS contained in q iff I contained in f^{-1}(q) are proved from the definitions in the text. They are elementary steps, not new lemmas. This proves Sing(S)=V(IS) without assuming the singular locus of S was already closed.

For Step 4 I opened lem-weil-pbc-regular-base-change, lem-weil-pbc-tensor-quotient-base-change, lem-exc-regular-map-reduced-target, and def-weil-pbc-noetherian-ring. The base-change theorem is used only for the quotient R/I, a finite-type R-algebra; its result is regularity, exactly what 07QK needs. The tensor-quotient node states the B-algebra isomorphism and both pure-tensor formulas, so it identifies the actual base-change map with R/I to S/IS, not merely their underlying modules. I checked the source and target quotients are Noetherian by projecting finite generators of inverse-image ideals, and proved R/I reduced using radicality. Consequently 07QK applies. The final power test in S/IS proves IS radical, covering the ideal-theoretic clause rather than assuming it. This step uses no theorem merely hidden in a definition.

For Step 5 I reread the same radical-intersection node: its formula computes s(S) from the already established V(IS), and Step 4 removes the radical. I checked the empty-intersection convention and the zero-ring case explicitly. A non-surjective regular map, such as a localization, needs no extra hypothesis: each target prime is compared only with its contraction. For a field base with nonzero regular target the source singular ideal is the unit ideal, consistently giving empty singular locus in the target. For a singular base the identity map preserves its radical ideal, and the argument still applies. The closedness assumption is used in Step 3 and is not dropped.

Against delivery-errors B--E: the statement introduces every object and retains its definition dependencies; no new elementary, duplicate, or clause-restating node was made. Every non-elementary step cites an opened statement, and citations.json copies those actual statements verbatim. The two elementary steps include their prime/ideal arguments. Every step has a source and a Boolean elementary field, proof_deps is exactly the union of uses, and no step exceeds 2000 characters (lengths 783, 472, 629, 787, 541). No circular use of the parent patching lemma occurs. Search records were appended from the real log with exact query text; the hits were read and rejected because regular sequences and relative smooth loci do not state this absolute regular-map assertion. In particular I read Mathlib's Smooth/Locus.lean definitions and RegularLocalRing/Defs.lean definitions, not just result names.

## Unfinished work

None in this one-level split. Independent maintainer review remains the project delivery process.
