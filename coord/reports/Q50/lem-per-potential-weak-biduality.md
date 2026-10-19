# Worker report

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-potential-weak-biduality.json: item, split into eight proof steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-potential-scalar-rigidity.json: statement-only input, ILO XVII Theorem 5.1.1; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-potential-dual-constructibility.json: statement-only input, ILO XVII Proposition 6.2.3.1; no Mathlib match.

citations.json records a verbatim statement for every citation of every item step. Searches from the interrupted attempt were retained in searches.jsonl and read; their actual tools, query strings, leading hits, dates and verdicts were transferred without inventing results. The additional scalar homothety Loogle search was run in this continuation. No Mathlib leaf is claimed.

## Attachments

None. I searched WeilConjectures in the read-only slopmaster2 source for the exact blueprint tag and for weak biduality, biduality, potential-dualizing and potential scalar/Hom concepts. Ordinary finite locally free module biduality and point-perfect biduality are different statements. SixFunctors/Etale/Derived/Dualizing.lean has sorry declarations for finite-type-over-a-field Verdier duality; it does not prove this item for arbitrary excellent Noetherian schemes and ordinary constructible sheaves. The exact upstream master source was not treated as proof evidence.

## WANTED

None: the proof uses the available ILO volume and existing DAG statements. No prohibited source is used. ILO XIII 3.7.2 supplies the existing finite-open-constant generation node; ILO XVII 6.3.1 supplies the weak-reflexivity route.

## Corrections and scope

The original node was unsplit. Its source statement agrees with ILO XVII 6.3.1. I corrected only the literal missing backslash in $eta_M$ to $\eta_M$; all hypotheses, quantifiers and conclusions are unchanged. There is no mathematical statement dispute. In particular this item does not claim positive-degree biduality, bounded cohomological dimension of the scheme, finite Krull dimension, or finite Tor amplitude of the ordinary sheaf M.

Two source inputs must not be taken from the proof of an existing node: the scalar-rigidity assertion is proved inside lem-per-potential-dualizing-uniqueness but is missing from that node's statement; the constructibility assertion is one clause of the full duality theorem whose proof depends on this item. I made the former a separate earlier theorem input and the latter its independent ILO 6.2.3.1 input. Citing the full duality theorem instead would be circular.

## Not duplicates

lem-per-potential-scalar-rigidity vs lem-per-potential-dualizing-uniqueness: the existing statement gives pinned existence/uniqueness, bounded constructibility and Tor amplitude, but does not assert negative self-Ext vanishing or the scalar endomorphism-sheaf identification; its proof cannot be used as a statement citation.
lem-per-potential-scalar-rigidity vs lem-per-normal-pinned-extension: that statement includes scalar rigidity only for a normal integral scheme with generic dimension value zero and a particular perverse extension construction; the new statement is for any excellent Noetherian scheme and any dimension function.
lem-per-potential-scalar-rigidity vs lem-per-finite-modification-pinned-gluing: the existing statement assumes rigidity on three pieces in a finite-modification square and concludes it on their glued scheme; the new input is the unconditional general theorem.
lem-per-potential-scalar-rigidity vs lem-per-potential-weak-biduality: scalar rigidity concerns derived endomorphisms of K, and proves only the coefficient-sheaf base case of the item; the finite transport, open-closed cancellation, generator argument and coefficient filtration remain in the item's proof.
lem-per-potential-dual-constructibility vs lem-per-gabber-local-duality-general: the latter also asserts full biduality and depends on this item; the new independent input is only preservation of bounded constructibility, established before weak biduality in the source.
lem-per-potential-dual-constructibility vs lem-per-potential-local-duality: the latter is full finite-field duality with scalar extension, and also depends on the general theorem above; the new input works for prime-power coefficients and does not assume biduality.

The whole DAG was searched by statement concepts, by the source places 5.1.1 and 6.2.3.1, and by scalar/negative self-Hom and constructible-dual keywords. The whole blueprint was searched with blueprint_refs.py for potential weak biduality, weak biduality, potential dualizing, scalar rigidity, potential scalar, potential dual, self Hom, duality constructibility, preserves bounded constructible, devissage and finite pushforward. Existing lem-per-constructible-finite-open-constant-generation is reused, not recreated. The finite bidual comparison, relative triangle compatibility, coefficient restriction and coinduction are likewise reused. No new node has a Stacks tag shared with an existing node: these are specifically ILO potential-duality results.

## Review by Q50

I read the available ILO text at XVII Theorem 5.1.1, Proposition 6.2.1.1, Proposition 6.2.3.1 and the whole statement and proof of Proposition 6.3.1 (printed pages 284, 294, 295–297), together with XIII 3.7.2 (printed page 203). The item matches 6.3.1 in degree zero and every nonpositive degree. The coefficient integer is specialized to ell^r, which is already the item's convention. The two new statement-only nodes match exactly the scalar assertion of 5.1.1 and the preservation assertion of 6.2.3.1. They introduce X, ell, r, the coefficient ring, dimension function and K, and cite definitions for every specialized notion. They assert neither full biduality nor an injective-dimension bound.

For Step 1 I opened the derived-internal-Hom definition and both new statements. Hom from the free rank-one coefficient sheaf is the identity, so its evaluation transpose is the scalar-action map, exactly the map in the new rigidity statement. Preservation is used only to keep successive dualizations in D^b_c. I did not infer scalar rigidity from pinned uniqueness of morphisms alone, which would miss negative cohomology.

For Step 2 I opened lem-weil-heart-short-exact-triangles, lem-per-relative-bidual-triangles and lem-sf-derived-homology-long-exact. Their statements respectively supply the triangle of a short exact sequence, the natural morphism to its double-dual triangle including the connecting square, and the cohomology exact sequence. The step writes the cancellation diagram argument: when C is weak, negative terms for A and E agree and the kernel in degree zero is A. In the extension direction surjectivity onto H^0 B(C) follows by naturality from the actual surjection E to C, so no unjustified vanishing of H^1 B(A) is used. Additivity proves the finite sum and summand assertion directly. This is the substantive formal argument of the item, not a renamed child lemma.

For Step 3 I opened the finite-pullback and finite-bidual-comparison statements and the excellent-finite-type-algebra lemma. The finite comparison explicitly assumes preservation on both schemes, which the new constructibility node supplies; I checked that hypothesis rather than silently applying it. Finite sources are Noetherian, excellent and still have ell invertible; the finite compactification is immediate. Finite residue extensions have transcendence degree zero, giving precisely delta_Y=delta_X composed with p as required by the comparison. Its statement includes cohomology comparison, exactness, conservativity and identification of the specified evaluation biduality maps. Consequently the weak condition transports in both directions even when p is not surjective. The same argument applies to a closed immersion.

For Step 4 I opened lem-weil-pbc-open-closed-short-exact, including its explicit module-sheaf clause. Applied to the coefficient sheaf it gives the written sequence. The source Y and its closed complement are in the permitted excellent class; their potentials are supplied by the finite exceptional pullback already handled in Step 3. The quotient is weak by finite transport from its coefficient sheaf. Cancellation in Step 2 proves the open extension weak. This does not assume that open extension commutes with biduality, which is not one of the cited statements.

For Step 5 I opened lem-per-constructible-finite-open-constant-generation and read its source ILO XIII 3.7.2. Its statement has the same ordinary small etale site and a finite coefficient field, and exactly the finite sums/extensions/summands closure used here. No quotient closure, semisimplicity, division by a cover's degree or finite-type-over-a-field hypothesis is slipped in. Every generator is weak by Step 4 and finite transport, so finite induction applies.

For Step 6 I opened the statements of potential-hom-coefficient-restriction, potential-coinduction and the new preservation input, and reread XVII 6.2.1.1. The former makes K_1 potential with the same dimension function. Coinduction is the right-adjoint comparison, not tensor reduction. Its statement explicitly specifies evaluation at 1; composing the evaluation pairing with that map shows that both double-dual comparisons carry the same transpose of the same symmetric pairing. The second comparison is applied to D_{K_1}N, which is in D^b_c by preservation, so its D^+ hypothesis is met. This supplies weak reflexivity over Lambda for all constructible sheaves killed by ell without assuming the conclusion for general Lambda.

For Step 7 I opened thm-constructible-serre. Images are kernels of cokernels of scalar multiplication, so its stated kernel/cokernel closure makes every filtration term and quotient constructible. Each quotient is killed by ell, and the finite filtration starts at ell^r M=0, so Step 2 proves exactly the needed extension induction. For Step 8 I reread the truncation adjunction in the heart-triangle node and the standard-t-structure definition. M is in D^{<=0}; the factorization exists in the correct direction and agrees on nonpositive cohomology. Its source and target vanish above zero, hence it is an isomorphism. Positive cohomology of B(M) remains unrestricted.

Small cases checked: X empty and M zero use empty sums and the unique zero maps; a geometric point with any dimension-function shift reduces the scalar assertion to End(Lambda)=Lambda; r=1 invokes the finite-field generator argument without any coefficient reduction; r>1 uses the finite length-r ell-adic filtration, which also allows repeated equal terms; the open U empty or U=Y gives respectively the zero or constant generator; a nonsurjective finite map still has conservative pushforward on its source. No finite-dimensionality of X or cohomological-dimension bound is needed. All eight steps are shorter than 2000 characters. The new nodes carry no hidden proof sketches or proof dependencies, and neither restates the entire item. Off-unit algebra, heart-triangle, long-exact-sequence, open-closed and Serre tools are declared in split_report.tool_uses; none replaces the inherited unit's route.

B–E self-check corrections: avoided the C3/C4 trap of reading scalar rigidity from an existing proof; avoided the C6 cycle through the full local-duality theorem; reused the existing generation node instead of duplicating it; supplied the finite comparison's preservation hypotheses; and wrote the cancellation and coefficient evaluation arguments explicitly instead of calling them standard. No Lean file, compiler, Lake command, live node or launcher file was modified.

## Unfinished work

None in the one-level split. The two newly stated independent inputs remain unsplit by design and join the DAG queue after delivery. Required server checks and final delivery are run with the prescribed launcher tools.
