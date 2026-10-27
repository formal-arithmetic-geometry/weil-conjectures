## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-pur-adjoint-projection-tensor-transfer.json` (item, split), `citations.json`, and this report. The item has seven explicit steps; the longest has 867 characters. No new nodes and no new Mathlib leaves. Statement, statement dependencies, original searches, provenance and ancestor are preserved. The six actual searches of this session are appended to the original searches, with their logged results retained verbatim as JSON. No Lean was written or compiled; the shared repository and launcher were only read.

Attachments: none. Searches of `lean/WeilConjectures/` for the blueprint id and for conjugate/projection/transpose names found no declaration giving this item's full clauses. The project projection-map compatibility and monoidal conjugation lemmas concern specified monoidal functors and different projection data; they do not attach to this general statement.

WANTED: none. This is an agent-written categorical calculation making explicit the blueprint's normalization argument, not a purported quotation of a missing textbook theorem.

Errors or gaps found: the item was statement-only, and its source path was an older blueprint snapshot. Its mathematical statement is correct as written. The proof now points to the latest blueprint, and its proof origin is explicitly agent. The original source metadata is preserved as provenance. Neither the item nor its ancestor's statement was changed. No unfinished argument remains.

## Source and route

Read `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md`, Step 1 (etale normalization makes the tensor map the identity), and `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.proof.md`, Step 1, last paragraph (co-projection compatibility), together with the ancestor statement. The item's abstract formulation is the formal calculation isolated by Q98 from the tensor normalization proof, not a theorem explicitly stated in the blueprint. Read its live parent `lem-pur-etale-sum-right-adjoint-tensor`, including the earlier independent review explaining the same formula. The unit and chapter records were read: this is an auxiliary categorical tool for the given purity route, and does not replace the diagonal/DNC/vector-bundle route. No SGA source is used.

Read `Mathlib/CategoryTheory/Adjunction/Mates.lean` lines 275–306: conjugation, its counit equation and unit equation. Read the adjunction conventions in `Adjunction/Basic.lean` and the Hom-naturality signatures. Read the monoidal-adjunction search candidates in `Monoidal/Functor.lean`: the candidates assume monoidal or oplax/lax structures absent from this item. Read the four existing nodes cited by this proof, including their full statements. Those are the sources for its general categorical operations.

## Searches and existing nodes

Blueprint-wide `tools/blueprint_refs.py search` was run for `conjugate`, `projection.*counit`, and `tensor transpose`; the conjugate search found 28 blueprint nodes but none states this full projection/unit transfer. The other searches found none. DAG searches for adjunctions, transposes, conjugates and counits found the existing `lem-pur-adjunction-mate-transpose`, which is used instead of creating a special case. Read and rejected the more specialized normalized-square, conjugate-unit-equation, unary-counit and adjunct-open-factor nodes as replacements for the full item. The existing mate and conjugate definitions are Mathlib leaves, and the monoidal definition is also a Mathlib leaf.

Actual Mathlib queries and hit lists are in `searches.jsonl` and in the item's appended records. Two semantic phrasings were tried. The generic conjugation lemmas supply only the adjunction comparison, not the full tensor identity. The semantic results on monoidal adjunctions require extra functor structures. The grep for projection formula names was empty. All services used in this session returned results; no unavailable service was misreported as absence. Original Q98 searches were retained, not presented as newly executed Q21 searches.

## New nodes

None. The tensor substitutions are elementary consequences of the hypotheses, not reasons for new nodes. The only nontrivial auxiliary transpose theorem already exists.

## Not duplicates

No new nodes. The general mate-transpose node is reused; no clone of its identity-functor specialization was created.

## Review by Q21

I checked the statement against the latest locality proof Step 1 and composition-coherence proof Step 1, and re-derived the formula without assuming that any of F, S, G or T is faithful or monoidal. The evaluation hypothesis is needed only at T(1), exactly as stated. In particular it is not an unproved evaluation formula for arbitrary objects.

Step 1 uses the conjugate node's actual isomorphism-preservation statement and the mate node's transpose characterization with both intervening functors identities. This gives ev S(rho)=epsilon d^{-1}, in the correct direction; multiplying by d gives the requested equation. Uniqueness follows from the inverse Hom bijection at (GK,K), so no faithfulness claim is hidden. I checked rho:G→T, not T→G, and that rho at 1 has domain W.

Step 2 uses the complete statement of `lem-pur-adjunction-mate-transpose`, not its proof: its right square is rho, its left mate is d^{-1}, its two intervening functors are identities, and b has precisely the theorem's domain FN. This proves the Hom identity and supplies its use in Step 6. This node lies outside the item's unit; it is declared in split_report.tool_uses as a general categorical tool, not an alternate geometric route.

Step 3 uses just naturality of d and the assumed P/p square. I checked both inverse equations have domain SN, N=TK tensor W. The cited monoidal node explicitly defines tensor maps and their bifunctorial composition. These substitutions produce the first claimed expression, rather than assuming a projection map is canonical. Step 4 first uses Step 1 at 1, then naturality of p in its first variable at R:W→T1. Its inverse equation has domain S(W tensor TK), and composing the actual evaluation hypothesis with p^{-1} gives the displayed formula. No outside theorem is hidden in either substitution.

Step 5 uses the symmetry naturality explicitly assumed in the item's statement, with the pair (1_TK, eta), followed by the explicitly assumed lambda sigma=r equation. I checked that a_K has domain T1 tensor TK and that the final composite has domain TK tensor W. Thus u is used precisely to define eta=uR, and no symmetry of the functor S is assumed. The monoidal node supplies the tensor bifunctor/unitors, while symmetry is inline data of the item itself.

Step 6 uses the inverse Hom/counit convention of the mate node, with the Hom bijection already part of the hypotheses. Applying it to Step 5 and then using Step 2 gives rho tau=h, not merely an isomorphism of objects. Step 7 writes the three naturality equations whose composition proves q natural; I checked their domains at each successive factor. Naturality of the assumed Hom bijections then proves tau natural. Unitor naturality gives h natural, and d^{-1} gives naturality of qd^{-1}. This checks equality of natural transformations without an unstated identification or cancellation through a functor.

Small cases: for identity functors with standard tensor/unit comparisons all equations reduce to the unitor-symmetry identity; for an identity functor on vector spaces with d=c times identity (c nonzero), rho=c^{-1} times identity, eta=c^{-1}, and both sides of rho tau=h have that same scalar. This detects the direction of the inverse in conjugation. The calculation also works in the terminal category and for the zero object in additive examples, since it never divides a morphism except the isomorphisms explicitly supplied. No nonemptiness, additive, exactness, smallness, finite-dimensionality or rigidity hypothesis was used. There are no new statements requiring additional edge-case tests.

I checked delivery-errors B–E with the cited node statements open: no unsupported notion, no new unsplit proof, no fabricated search, no new leaf, no duplicated clause node, no circular dependency, and no step exceeding 2000 characters. The new dependency is a generic tool whose own proof depends on mate pasting, not on this item. All nine citation entries quote literal text of the live cited statements. The only corrections made during this reading were to make the inverse projection equation and the symmetry-to-right-unitor substitution explicit; the statement itself required no correction.
