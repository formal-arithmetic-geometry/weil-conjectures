# Worker report: lem-sfb-fibre-product-algebra-flat-presentation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fibre-product-algebra-flat-presentation.json: split the unchanged statement into seven proof steps, following Stacks 08KQ.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-module-fibre-product-patching.json: statement; unsplit, no Mathlib match; Stacks 0D2I(1),(2).
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-module-fibre-product-patching.json: statement; unsplit, no Mathlib match; Stacks 0D2H.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-fp-module-fibre-product.json: statement; unsplit, no Mathlib match; flat-ambient case of Stacks 08KP.
- citations.json: verbatim statements backing every proof-step citation.

## Attachments

None. The blueprint tag and searches for fibre-product algebra, Milnor and patching in lean/WeilConjectures yielded no project declaration proving the item. In particular, tensor-pushout and scheme-pullback declarations do not assert patching over a ring pullback.

## Literature wanted

None. Sources read locally: literature/stacks-project/more-algebra.tex, Situation 08KH; 07RU; 0D2H; 0D2I and its proof; 08KP and its proof; 08KQ and its proof, especially Ad (1)--(3). Also literature/stacks-project/algebra.tex, 00R2 and 0519.

## Findings and changes

The saved sandbox contained the unchanged, unsplit item and searches.jsonl, with no report, citation file or running deliver.py. I continued it, retained its statement and inherited searches, and read the logged results before selecting the module inputs. No dry run or push was interrupted. There was no stage-1 repair note for this item.

The original statement agrees with 08KQ(2),(3) and the final flat-algebra assertion. No correction or statement dispute is needed. In particular A' -> A is an arbitrary surjection: the theorem is not limited to nilpotent ideals or Noetherian rings. The algebraic isomorphisms used in the forward implications must be the canonical base-change maps, not just abstract isomorphisms; step 1 spells out the maps.

The current blueprint source read is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). The item is an inherited supporting input on the stable-curve/infinitesimal-pushout branch, reducing 07RX to 08KQ. I read the recorded unit and chapter and changed neither. blueprint_refs.py ancestor returns None for this existing imported chain, so the new nodes retain that exact null ancestor and extend the inherited via list by this item; their places name the supporting module inputs. Whole-blueprint searches for fibre product, module-over-fibre-product, Milnor, presentation-independent, relative finitely presented, 08KP, 0D2H and 0D2I found no blueprint statement that supplies these module lemmas. same_as remains [].

The DAG search by source tag, title, statement concepts and declaration names found the existing lem-sfb-patched-module-base-change, lem-weil-pbc-finite-presentation-surjection-kernel-fg, lem-weil-pbc-flat-module-base-change, lem-weil-pbc-finite-presentation-base-change-composition, and lem-trf-finite-presentation-surjective-module-kernel. The last four are Mathlib leaves. Thus I created no new presentation-kernel or scalar-extension leaf. The three new module statements are proper inputs, not copies of algebra clauses: they allow arbitrary modules with no algebra multiplication. The relative presentation input is about modules over an independently given flat ambient algebra, not about finite presentation of the patched algebra over R.

## Searches

All new-node queries are actual entries of searches.jsonl, reused without repeating the interrupted turn's completed searches. Each has LeanFinder (two phrasings), LeanSearch, Loogle, and grep. I read the recorded hits and the relevant Mathlib source: RingTheory/Flat/Tensor.lean (flat tensor criteria), RingTheory/FinitePresentation.lean (lines 298 and 372), and Algebra/Module/FinitePresentation.lean (lines 191 and 214). Flat.of_flat_tensorProduct assumes a faithfully flat extension, which is absent here; stable-under-base-change statements give only the forward implications. Algebra.IsPushout.cancelBaseChange and the tensor associativity declarations concern a pushout, not the pullback patching theorem. instFinitePresentationTensorProduct is scalar extension, not gluing. Module.Finite.of_exact cannot infer the missing finiteness over R from modules finite over the two different coefficient rings. Consequently none is a one-line match for the new nodes. The additional searches in this resumed turn confirmed presentation-kernel declarations, then the DAG search found their existing leaves; these extra log entries create no nodes.

## Review by Q145

I checked 08KQ against the item with both the source and node open. Its B' is the item's R, and its D' is E. The source's system is precisely the given algebra isomorphism D tensor_B A -> C'/IC'. Its parts (2),(3) are the two iff assertions, and its final assertion is the canonical map for every flat L. No equivalence-of-categories clause is required by this item. Every ring may be zero.

Step 1 uses the statement of lem-sfb-patched-module-base-change, which explicitly gives both canonical projection tensor maps as isomorphisms without flatness. Multiplicativity and preservation of 1 follow from their displayed formulas. I did not take a construction from that node's proof.

Step 2 uses lem-weil-pbc-flat-module-base-change for the flatness of both recovered algebras, and part (1) of lem-weil-pbc-finite-presentation-base-change-composition for algebra finite presentation under the two arbitrary ring maps. Both statements allow the base changes at issue.

Step 3 uses the new flat-module node, whose first clause asserts flatness of the actual module fibre product and whose second clause asserts bijectivity of the canonical reconstruction map for an arbitrary flat module. The extra ring assertion is justified by the two components preserving multiplication and 1. This does not assume L is finitely presented.

Step 4 is elementary given the definition of a finite algebra presentation and the recovery of step 1. I checked the surjection E -> D comes from the quotient C' -> C, not from a nonexistent surjection B -> A. Only finitely many tensors are needed to express the finitely many chosen generators of C'. The v_k therefore generate C' as an algebra, even though E -> C' need not be surjective.

Step 5 applies the new finite-module node to the polynomial square, not directly to finite-type algebras mistaken for finite modules. The polynomial square is coefficientwise cartesian and the A' polynomial map remains surjective. The evaluation maps are surjective, so D and C' are cyclic modules over P_B and P_A'. Their reductions respect the prescribed variable values: the compatibility is exactly e_i in E. The node's statement then supplies finite generation over P. Adding its finite module generators to the variable list gives an actual surjective polynomial map P -> E; the explicit expression sum f_j(e)w_j explains this step. There is no hidden finite-type-composition theorem.

Step 6 invokes the existing 00R2 Mathlib leaf for the kernels of the two surjective polynomial presentations. Its statement says every such presentation has finitely generated kernel, under the finite-presentation assumptions on D/B and C'/A'. A finite generating list gives a presentation of the cyclic quotient module, using the exact-sequence definition in def-sc-finitely-presented-module. Polynomial flatness is explained directly via its monomial direct-sum decomposition and the definition of flatness; no finiteness of the monomial index is used.

Step 7 applies the new relative-presentation node with S=P, whose flatness was established, not S=E before finite presentation has been proved. D and C' retain flatness over B,A' and have the module finite presentations of step 6. The cyclic evaluation map P -> E is surjective by step 5. The existing lem-trf-finite-presentation-surjective-module-kernel states exactly that a surjection from a finite module to a finitely presented module has finite kernel; its source P is generated by 1. Thus the resulting finitely generated ideal is a finite algebra relation list, as required by the finite-algebra-presentation definition. This proves the algebra conclusion rather than renaming it as a new node.

For the three new nodes I checked the exact source statements and their hypotheses. 0D2I needs only the surjection and compatible modules plus the asserted side flatness; it also gives reconstruction for flat modules. 0D2H needs finite generation only, with no flatness. For 08KP I retained its two relative flatness assumptions and its two finite module presentations; its factorization condition (3) holds with D''=D'=S and the identity finite-presentation map. The new node intentionally states this flat-ambient case, sufficient at S=P. Each statement introduces every ring and module, cites its tensor/flat/finite-presentation definitions, and has empty proof and proof_deps. Their statements contain no proof sketches.

I tested I=0 (A'=A, all fibre products reduce to the B side), B=A (all reduce to the A' side), A=0 (a product of rings, with compatible reduction zero), and zero modules. For arbitrary modules in the flat lemma, zero and free modules satisfy the stated reconstruction. For the relative lemma, S=R and S=0 specialize correctly. None of these tests requires nonzero rings, a nilpotent I, or a Noetherian hypothesis. No edge case exposed a missing assumption. I corrected the potential circular choice S=E to S=P in the presentation argument, and explicitly enlarged the polynomial generator list after obtaining finite generation as a P-module. No non-elementary step exceeds 2000 characters.

## Not duplicates

- lem-sfb-flat-module-fibre-product-patching vs lem-sfb-fibre-product-algebra-flat-presentation: the new node concerns arbitrary flat modules and module reconstruction, without finite projectivity or algebra multiplication; the item proves flatness and finite presentation of an algebra over the base pullback using polynomial presentations.
- lem-sfb-flat-module-fibre-product-patching vs lem-sfb-patched-module-base-change: the existing node gives the two projection scalar-extension isomorphisms only; the new node asserts arbitrary flat modules and module reconstruction, without finite projectivity or algebra multiplication.
- lem-sfb-flat-module-fibre-product-patching vs lem-sfb-fibre-product-finite-projective-patching: the existing node assumes finite projective modules and gives their category equivalence; the new node concerns arbitrary flat modules and module reconstruction, without finite projectivity or algebra multiplication, which does not follow by specializing finite-projective patching.
- lem-sfb-finite-module-fibre-product-patching vs lem-sfb-fibre-product-algebra-flat-presentation: the new node concerns finite generation of arbitrary patched modules, without flatness or projectivity; the item proves flatness and finite presentation of an algebra over the base pullback using polynomial presentations.
- lem-sfb-finite-module-fibre-product-patching vs lem-sfb-patched-module-base-change: the existing node gives the two projection scalar-extension isomorphisms only; the new node asserts finite generation of arbitrary patched modules, without flatness or projectivity.
- lem-sfb-finite-module-fibre-product-patching vs lem-sfb-fibre-product-finite-projective-patching: the existing node assumes finite projective modules and gives their category equivalence; the new node concerns finite generation of arbitrary patched modules, without flatness or projectivity, which does not follow by specializing finite-projective patching.
- lem-sfb-relative-fp-module-fibre-product vs lem-sfb-fibre-product-algebra-flat-presentation: the new node concerns finite module presentation over a separate flat ambient algebra, retaining relative flatness over the two base rings; the item proves flatness and finite presentation of an algebra over the base pullback using polynomial presentations.
- lem-sfb-relative-fp-module-fibre-product vs lem-sfb-patched-module-base-change: the existing node gives the two projection scalar-extension isomorphisms only; the new node asserts finite module presentation over a separate flat ambient algebra, retaining relative flatness over the two base rings.
- lem-sfb-relative-fp-module-fibre-product vs lem-sfb-fibre-product-finite-projective-patching: the existing node assumes finite projective modules and gives their category equivalence; the new node concerns finite module presentation over a separate flat ambient algebra, retaining relative flatness over the two base rings, which does not follow by specializing finite-projective patching.

## Unfinished work

No part of this one-level split is left unfinished. The three new statements are intentionally unsplit queue items, not proofs claimed complete. Server dry run and delivery results follow below.
