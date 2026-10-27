## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-regular-trait-modification-graph-tower.json: statement, split; Mathlib searches found rational-map representations and properness of Proj, but no point-blowup resolution. Eight proof steps, all under 2000 characters.
- citations.json: one verbatim statement quote for every cited node in every step.
- No new nodes, no Mathlib leaves, no Lean files.

## Attachments

None. Searching lean/WeilConjectures for the exact blueprint tag, regular-trait wording and modification/point-blowup terminology found no declaration proving the item. The existing resolution node has a Sheaf Lean statement, which is not an attachment and is used only through its DAG statement.

## WANTED

No additional document is needed for this split. The inherited source record mentions de Jong Lemma 3.13 and an archival PDF request; this delivery uses the local Stacks sources exclusively for the actual proof. No SGA source is used.

## Corrections and route

The mathematical statement is unchanged. The original citation def-weil-geometric-fibre was the wrong notion for the ordinary generic and special fibres; replaced it with def-pc-scheme-fibre. The statement assumes local dimensions at most two, not scheme dimension exactly two. The proof now derives dimension two before applying the existing theorem. Properness and the nonempty generic fibre force a nonempty special fibre, which supplies a dimension-two closed point. The chain formula gives the upper bound and identifies the supremum of local-ring dimensions with scheme dimension.

The proof applies lem-sfb-surface-rational-map-point-resolution over C, not merely over Spec A: this yields the required equality p a = h directly, rather than only an equality on generic fibres. It does not reconstruct that theorem's graph or principalization proof. The null blueprint ancestor is inherited: tools/blueprint_refs.py ancestor prints None. The full via chain and explicit direct-image/alteration prerequisite place are retained. The current main-20261015 unit text and its direct-images proof were read, along with the recorded chapter and unit. This is below their alteration prerequisite; neither chapter nor unit is changed.

## Not duplicates

No new node is created. DAG searches by 0C5H, 0AGR, 01WE and modification/point-blowup wording, plus blueprint_refs searches for point blowup, regular surface, 0C5H, H-projective and modification, led to reuse of the existing resolution, geometry, affine-base projectivity and H-projective composition nodes.

## Tool uses

The split_report declares four generic tools from other units: lem-trf-h-projective-composition (01WE), lem-kun-projective-implies-proper (01WC), lem-sc-scheme-stalk-dimension-generalization-chains (02IZ), and pqf-lem-affine-open-locnoeth (Noetherian affine charts). Their statements give exactly the generic facts needed here; there is no same-unit general replacement. Definitions and Mathlib leaves are used with their ordinary meanings.

## Review by Q141

I read Stacks resolve.tex Tag 0C5H (lemma-extend-rational-map-blowing-up), including the 0AHI argument immediately preceding it, and Tags 0AGQ/0AGR (lemma-blowup and lemma-blowup-regular). I read divisors.tex Tag 02NS (lemma-blowing-up-projective), morphisms.tex Tags 01WC, 01WE and 087S, properties.tex Tag 02IZ and its preceding dimension argument, algebra.tex Tag 00PD, and schemes.tex the reduced closed subscheme and standard open material. No new node needs a separate source review. The proof is marked agent-origin because the trait application and its bookkeeping are written here from those statements.

Step 1 uses the DVR definition to choose a nonzero uniformizer and to obtain a Noetherian local domain. The cited unit-times-power node then proves that inverting the uniformizer gives F and that the only nonzero prime is the maximal ideal. The cited principal-localization theorem gives the open immersion; base change identifies its inverse image with Z_F. The integral-scheme definition supplies irreducibility, so the nonempty generic open is dense. This does not assume flatness, excellence or perfection.

Step 2 uses exactly the H-projective composition and projective-proper statements to make Z -> T proper. The proper-morphism definition supplies closedness of its image. Since the image contains the generic point it contains the entire trait. The fibre definition identifies the special fibre with a closed subspace. The minimal-closed-subset node and sobriety node give a closed point in that nonempty fibre by the written argument. That point satisfies the assumed local-dimension hypothesis.

Step 3 cites the full chain formula, not just a dimension definition. Its codimension equality and sobriety identify every irreducible-closed chain with a chain based at its smallest generic point. The topological dimension definition therefore gives the stated supremum, bounded above by two and attained at the point from step 2. This checks the exact-dimension hypothesis of the resolution theorem.

Step 4 uses projective-proper only for p. I read the resolution node's full statement: it allows an arbitrary base S, needs a proper target over S and an integral regular Noetherian surface X of dimension two with dense open U, and gives an S-morphism on the tower. Here S=C, and the inverse of p_F composed with r_F is a C-morphism by the base-change identities. Thus its conclusion gives a C-morphism a, all intermediate scheme properties and the generic isomorphism. No property is taken merely from that node's proof.

Step 5 uses only base-change and fibre definitions to locate all centres over the unique closed point of T. Step 6 has an explicit base case and induction step. The geometry node assumes an integral regular Noetherian scheme and a closed point with local dimension two; those hypotheses hold at each centre by the induction invariant and step 4. Its statement gives both properness/off-centre isomorphism and dimension two at closed exceptional points. Properness sends a closed point to a closed point, so the off-centre case is covered by the induction hypothesis. A closed point of the special fibre is also closed in the whole level because this fibre is closed. This distinction is checked before applying the geometry node.

Step 7 reads the actual ideal-sheaf definition, which explicitly states quasi-coherence and the affine ideal description. The affine-open Noetherian theorem and definition of Noetherian ring give finite generation of those ideals. The affine-base blowup theorem assumes an H-projective source over an affine Noetherian base and a finite-type quasi-coherent ideal; the induction supplies the source condition, and A is Noetherian from step 1. Its statement gives both relative and absolute H-projectivity, rather than only projective-bundle projectivity. Step 8 uses the definition of a C-morphism for p a = h and H-projective composition for h. Generic isomorphism is composition of the two specified isomorphisms.

I checked B--E: all objects and hypotheses remain explicit, no new statement contains a proof, no duplicate or elementary node was created, every step's non-elementary input is a cited statement, proof_deps is the union of uses, and citations.json copies the full statements verbatim. I inspected the Mathlib hits: PartialMap, RationalMap, representatives and toPartialMap at Mathlib/AlgebraicGeometry/Birational/RationalMap.lean describe rational maps but give no point-blowup resolution. The second LeanFinder phrasing returned the same kind of representatives. The initial blowup grep returned no hits; the subsequent grep located the actual rational-map definitions in the renamed Birational directory. All new searches are copied from searches.jsonl without invented calls.

The length-zero tower satisfies every universal assertion, with no centre obligation. The empty scheme is excluded by the nonempty generic fibre. A hypothetical missing special fibre is ruled out by proper closed image; no separate flatness assertion is used. The argument permits arbitrary DVRs and imperfect residue fields. Each proof step is under 2000 characters and has no hidden independent comparison lemma. No statement dispute or source error was found.

## Unfinished work

None for this one-level split. The existing cited unsplit nodes remain their own queue items.
