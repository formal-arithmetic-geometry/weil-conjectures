# Stage 1 report: lem-sfb-complete-algebra-devissage-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-complete-algebra-devissage-base-change.json`: item split into eight steps; no Mathlib match for the complete devissage assertion.
- `citations.json`: 26 verbatim statement quotations, one for every step/node pair.
- `report.md`: this report. The required search commands also produced `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. All mathematical inputs already exist in the DAG. The short generator, quotient-prime, contraction, and balancing calculations are proof steps, rather than new nodes.

## Attachments

None. Searches in `lean/WeilConjectures/` by the blueprint tag, devissage/dévissage, and geometric irreducible fibre terminology found no declaration stating this algebra devissage result. The existing constructible-sheaf and derived-category devissages concern different objects. The existing closed smoothness/geometric-reducedness nodes are reused; no new attachment is claimed.

## WANTED

None. The required sources are present in `literature/stacks-project/`.

## What was wrong or changed

The statement is sound and is unchanged; its three statement dependencies are unchanged. The empty imported proof has been replaced by an explicit algebra proof of the route already named in its source. Tag 05I0 only compares the geometric and algebraic notions in one direction because the algebra version omits the dimension condition. I did not infer an equivalence or add that dimension condition: the argument verifies the eight conditions of 05HX directly, following the proof of 05HJ.

The inherited `blueprint.from.node` is null. `tools/blueprint_refs.py ancestor lem-sfb-complete-algebra-devissage-base-change` reports None, so I retained that inherited field and its detailed non-unspecified place/via chain. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/{_section.md,sk-thm-sf-ctf-stability.proof.md}` and the unit/chapter records. This is the algebra prerequisite already assigned to the compactification/direct-image chain, rather than a replacement of the unit route. Whole-blueprint search for devissage found constructible/derived-category devissages only; none is this item. No unit record is changed: this item is not the unit's key statement.

The item's inherited Mathlib searches were retained. New searches used the mandatory msearch command: Loogle and grep found no devissage notion; two semantic phrasings returned ordinary prime filtrations, generic module bases, smooth base change and adic completion, rather than a complete algebra devissage theorem. An auxiliary query about flat domains and extended primes found going-down and lying-over theorems, not the required assertion; that auxiliary argument is only a few lines from the existing exactness and smooth-fibre inputs. The log entries are copied accurately into `mathlib_searches`. No unavailable service is treated as a negative result.

## Not duplicates

No new nodes were created. Existing nodes for right exactness, smooth base change, smooth-flatness, geometric irreducibility, geometric reducedness and finite-presentation base change are cited directly. I also read the integral-pullback node; its locally Noetherian hypothesis prevents applying it to the arbitrary domain R'/p'. The proof instead tensors the injection into the fraction field with a flat algebra, for which the cited exactness node has no Noetherian hypothesis.

## Review by NZ

I read flat.tex Tag 05HJ (lemma-base-change-complete), its one-step input Tag 05H7 (lemma-base-change-one-step), the entire algebra definition Tag 05HX (definition-complete-devissage-algebra), and the affine comparison Tag 05I0 (remark-same-notion). I also read the actual statements of every node used in every proof step. There are no new-node sources to review.

Step 1 uses the existing devissage definition for its input data and finite modules, and the finite-generation and tensor definitions for its displayed generator calculation. It proves finite type and all three module-finiteness requirements directly on pure tensors. The finite-rank free-source identification is given on basis vectors with an inverse. I checked its source against Algebra Tag 05G5 (lemma-base-change-finiteness), parts (1) and (3), without turning those elementary calculations into nodes.

Step 2 uses the right-exact tensor node for surjectivity, not for left exactness. The finite-presentation base-change node explicitly applies to arbitrary base ring maps and supplies finite presentation. The balancing isomorphism needed to apply it over C rather than R is written with its inverse. I checked Algebra Tag 00DF (lemma-tensor-product-exact) and 05G5 part (4). The finite maps are already covered by step 1's generators; no finite-presentation assumption on those maps is inserted.

Step 3 uses the smooth-morphism definition's explicit affine equivalence to pass to smooth ring maps, the existing smooth-ring base-change node for arbitrary base change, and the geometric-irreducibility definition for every extension field of every new fibre. This is precisely the forward implication of More on Morphisms Tag 0555 (lemma-base-change-fibres-geometrically-irreducible) used in 05H7. It does not use a special closed point or assume R' is flat.

Step 4 uses right exactness to identify the quotient tensor, the smooth-flat ring-map node to make C flat over D, and the flat-tensor-exact node to preserve the injection of the domain D into its fraction field. The residue-field definition identifies that generic fibre; the closed smooth-geometrically-reduced node says the smooth fibre is reduced. The integral-scheme definition explicitly says nonempty reduced irreducible is equivalent to integral and that the affine ring is a domain. Thus C is a unital subring of a nonzero domain, proving the new extended ideal is prime. I read Varieties Tag 056T and the smooth-flat assertion (Morphisms Tag 01VF). All domains here are quotients by prime ideals, with no Noetherian assumption. This is a short composition of cited statements, not a new independent prime-extension theorem.

Step 5 uses the pointed hypothesis exactly where needed: R/p injects into R'/p'. Smooth base change and smooth-flatness make B_i/pB_i flat over R/p; the existing flat-exactness theorem gives the injective tensor map. Right exactness gives the quotient identification, as already written in step 4. Hence the inverse image of p'B_i' is pB_i, and the residue-field map is the displayed map on fractions with its denominators verified nonzero. This addresses the generic-point identification that would be missing if one only said that the fibre is integral.

Step 6 uses only the tensor definition and functoriality after the field map just proved. Both iterated-tensor identifications and their inverses are written down, and checking basis vectors identifies the new map with the old map tensored with the field extension. Tensoring its inverse proves invertibility; no unstated preservation-of-kernels theorem is used.

Step 7 uses the right-exactness node on the exact sequence ending in the cokernel and checks the resulting map is B_i'-linear. Tensoring the two given module isomorphisms and their inverses gives the compatible new module identifications. It proves the last cokernel vanishes, and requires only finite modules, not finitely presented modules. Step 8 checks the definition's conditions and separately handles the empty sequence, when N=0.

I tested n=0, n=1, zero ranks, identity base change, field extensions and the nonflat quotient R'=R/I with a prime p' above p (in particular R=k[t], R'=k). The argument only needs flatness of the smooth auxiliary algebras; no injection of an original alpha map is asserted or needed. None of the eight steps is over 2000 characters, and each auxiliary calculation is a few lines from the cited statements. Every quote in citations.json is copied verbatim from the statement actually used, including its hypotheses. No statement is disputed, no SGA source is used, and no Lean/compiler/build command was run.

## Unfinished work

None in the mathematical split. The required server dry run exited 0 and printed `OK (not pushed)` at f5c0d5f0a3c: preflight passed. The direct-delivery command is the final step.
