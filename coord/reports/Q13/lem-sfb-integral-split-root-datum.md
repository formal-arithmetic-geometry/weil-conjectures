## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-split-root-datum.json`: statement, split into nine proof steps using existing DAG statements; unchanged statement; no Mathlib match.
- `citations.json`: one verbatim statement excerpt for each step/node citation.
- `searches.jsonl`: actual searches made by the prescribed msearch command, retained with their results.

New nodes: 0. New Mathlib leaves: 0. Reusing the existing relative root construction and field structure theory avoids creating new versions of these lemmas. The sandbox also contains the reproducible writer `write_split.py`, which is not a delivery node.

## Attachments

None. Searched the project source `lean/WeilConjectures/` for the item id and blueprint tag, integral/split root-datum spellings, reductive groups and coroots. The only broad reductive hits concern Lie algebras, not the group schemes of this statement. There is no project declaration proving every clause of this item.

## Wanted literature

WANTED: Brian Conrad, *Reductive group schemes* (2014), local copy `literature/conrad-reductive-group-schemes.pdf`, Definition 5.1.1, Example 5.1.4, Proposition 5.1.6, Example 5.1.7 and Theorem 4.2.6, for lem-sfb-integral-split-root-datum. Read the Stanford-hosted PDF online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf. No repository or literature file was written. As required for a missing local source, `proof_origin.by` is `agent`; this is an assembly of the existing node interfaces following that source, with the converse lattice argument read in the local Milne text.

Read locally: Milne, *Algebraic Groups*, `literature/milne-algebraic-groups_iAG2017.pdf`, Proposition 21.48 (p.439), Propositions 23.5 and 23.29 (pp.485--486,493), Theorem 23.9 (p.487), Theorem 23.25 (pp.492--493), and Proposition 23.59 (p.502). In particular Proposition 23.29 writes the lattice sandwich used in steps 7--8; the proof here spells out the integral pairings instead of treating that sandwich as unexplained transport.

No Stacks tag states the integral reductive-group root datum theorem. The one generic smoothness consequence used in step 7 is carried by the existing `sbc-lem-smooth-geometrically-reduced`; its cited Stacks tag 056T is `varieties-lemma-smooth-geometrically-normal`, read in `literature/stacks-project/varieties.tex`, and proves in particular geometric reducedness for a smooth scheme over a field. No forbidden SGA source is used.

## What was wrong or missing

The imported statement is consistent with the source and was retained verbatim. Its proof was empty. The source's split definition assumes trivial root lines, whereas the item's input supplies only a split maximal torus. Over the integers this difference is resolved: tangent weights are finite projective, their ranks are constant on the connected spectrum, and a subgroup of a finite free abelian group is free. The existing arithmetic node is declared as an off-unit tool, not a change of the chapter or unit route.

The field lattice node `lem-sfb-simply-connected-character-lattice` gives the forward implication only. I did not use it for the converse. Steps 7--8 prove the converse with arbitrary central isogenies, finite possibly nonreduced kernels, coroot compatibility, and the existing isomorphism criterion. The integral root-datum isogeny node was deliberately excluded because its statement already depends on this item.

During the citation audit I corrected an initially too-short Borel existence argument: `lem-sfb-reductive-borel-pair-structure` gives some Borel pair, not explicitly a Borel containing the specified maximal torus. Steps 4, 6 and 7 now cite maximal-torus conjugacy and explicitly conjugate both the torus and Borel.

## Blueprint and duplicate search

Read the chapter record, the unit record `sk-thm-sf-ctf-stability`, and the newest blueprint's `_section.md`, six-functor stability proof, and direct-image proof (3). This is the inherited supporting algebraic-group branch of the alteration prerequisite, below the fixed unit route. The ancestor command returns null, consistent with the item's existing `blueprint.from.node`; the inherited detailed place and via chain are retained. The full imported-blueprint searches for `root datum`, `coroot`, `weight lattice`, and `simply connected` return no equivalent blueprint statement. The broad `root` search returns cohomological and polynomial roots rather than a reductive-group root datum.

Searched the whole DAG for root datum, coroots, weight lattice, root lattice and the structural source places, and opened the relevant nodes. Reused tangent-weight base change, torus-bundle weights, rank-one reflections, canonical root exponentials, opposite-root reflection maps, diagonalizable character duality, the field semisimplicity criterion, the forward simply-connected lattice statement, Borel/tori conjugacy, and central-isogeny compatibility. No new node or clause-restatement is needed.

## Mathlib searches

All new queries were run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py Q13 lem-sfb-integral-split-root-datum ...`. Both semantic phrasings were read. LeanFinder returns abstract `RootSystem.mk'`, crystallographic root pairings and G2 results. LeanSearch returns `RootDatum`, Lie algebra coroot facts and root-pairing categories. Loogle's joint RootDatum/AlgebraicGeometry query returns no hits. The AlgebraicGeometry grep returns no reductive/coroot/root-datum theorem. A second grep locates `RootPairing` and `RootDatum`; I read `Mathlib/LinearAlgebra/RootSystem/Defs.lean:82--119`. It defines the combinatorial object and does not construct one from a group scheme or prove either fibre criterion. No hit is a one-line specialization of the item. Existing search records were preserved; the actual new logged searches were appended.

## Not duplicates

No new nodes, so no new/existing pairs require distinction. In particular no second relative coroot, semisimple-roots-span or forward simply-connected-character-lattice node was created.

## Review by Q13

I read the worker contract, stage-1 rules, SETUP's three levels, GOAL, and delivery-errors B--E in full. The source check was against Conrad's actual connected-base and root-datum discussion and Milne's field lattice argument, not the imported dependency lists. No new statement was made, no statement correction or dispute was necessary, and no new unsplit node contains a hidden proof.

Step 1 uses the statement of relative diagonalizable character duality, which says that homomorphisms are locally uniquely lattice maps. Applying it to the free groups M and Z and using the generic point of Spec Z makes them constant, including cocharacters. The diagonalizable-group definition supplies the Hopf basis and functorial maps, so base change and the evaluation formula are written directly. I checked the base is nonzero and connected; disconnected rings are considered only after base change from the fixed integral maps.

Step 2 uses precisely the finite-projective, finite-support and arbitrary-base-change clauses of relative-tangent-weight-base-change. The torus-bundle statement supplies simultaneous local constancy of the ranks, and the geometric rank-one-reflections statement supplies dimension one for the nonzero weights. The subgroup-of-finite-free theorem proves freeness of the projective Z-summands. This does not assume the split group has already been constructed and does not assume a root line is globally trivial before proving it. It identifies support in each positive characteristic, not merely in the generic fibre.

Step 3 uses the existing canonical exponentials to meet the hypotheses of opposite-root-reflection-map: both opposite summands are now free rank one, G is smooth affine finite type over the nonzero Noetherian ring Z, its geometric fibres are reductive, and the specified torus is maximal in each fibre. That node states both existence of the coroot and its fibre and arbitrary-base-change interpretation. Relative character duality then makes it a single integer covector. Thus no full integral root datum has been assumed while constructing the coroots.

Step 4 uses the root-datum clause of reductive-borel-pair-structure on a geometric fibre, after choosing and conjugating a Borel pair by the exact maximal-torus-conjugacy statement. Rank-one-reflections supplies the finite Weyl group and compatible reflection/coroot actions. Since torus characters over a field retain the integer lattice, the equalities are equalities in M and its integer dual, not equalities of differentiated weights modulo the characteristic. The two relative comparison nodes then supply arbitrary ring base change. A free rank-one Z-module becomes A, so roots do not disappear for nonzero A. No reductivity-over-an-arbitrary-ring classification theorem is silently used.

Step 5 applies semisimple-roots-span to each algebraically closed fibre with its actual specified maximal torus. Its statement is the needed if-and-only-if, and the right side is independent of the fibre. This is the hypothesis that is explicitly imposed before P is used in steps 6--8.

Step 6 uses only the forward direction of simply-connected-character-lattice, after the Borel choice and conjugation. I checked that this source node requires both semisimplicity and simple connectedness, both available here. Its displayed full weight lattice is the same P as the item's, because steps 1--4 identify all the characters, coroots and pairings.

Step 7 first makes an arbitrary surjective central cover eligible for the faithfully flat compatibility statements. The homomorphism factorization node gives the closed image and faithful flatness onto it; smooth-geometrically-reduced gives that the target over the field is reduced. A closed image with full support has its defining ideal in the nilradical, so it is the whole reduced target. This short ideal argument is written out; it is not an assertion that a surjective morphism is always faithfully flat. The Borel-pair node says a semisimple group is reductive. The central-isogeny node now applies and gives the lifted specified torus and the coroot-pairing equality. The root-power-laws node gives injectivity, finite cokernel and exponent one for central kernel; it does not require the finite kernel to be smooth or to have order invertible in k.

Step 8 extends the pairing identity rationally along the injective finite-index lattice map, and for each character upstairs computes its preimage's integral pairing with every coroot. This proves it lies in P=M and therefore proves lattice surjectivity, with no new lattice lemma hidden in the word "transport". The isogeny-realization node explicitly states that EVERY such isogeny is an isomorphism when all exponents are one and the lattice map is an isomorphism; I use that criterion, not its existence assertion. This proves the defining condition of simple connectedness for every central cover, in every characteristic.

Step 9 checks the boundary cases rather than excluding them. I tested a positive-rank split torus (empty roots, span condition false), the rank-zero lattice (P=0 and all constructions empty), SL2 (M=Z, root 2 and coroot 1, hence P=Z), and PGL2 (M=Z, root 1 and coroot 2, hence P=(1/2)Z). The SL2-to-PGL2 kernel remains scheme-theoretic mu_2 in characteristic two, so it is crucial that the argument did not replace central kernel by a reduced finite subgroup. For the arbitrary base-change clause I also tested A=F_p[epsilon]/(epsilon^2) and products of nonzero rings: the root module is A and the cocharacters are the fixed integer ones. The zero ring is excluded exactly where the statement excludes it.

I opened every cited node's statement and selected its actual used sentence or formula in citations.json. Each excerpt is verified verbatim against the read node. The transitive statement/proof dependency search finds no path from the chosen supporting nodes back to this item. Every non-elementary fact in the proof is a cited existing statement; no step exceeds 2000 characters. The only off-unit citation is the generic finite-free arithmetic tool, declared in split_report.tool_uses. No chapter/unit statement or realization record is changed. This direct-delivery brief authorizes Q13's self-review; no second worker or subagent was started.

## Unfinished work

The stage-1 split is complete. The cited unsplit prerequisites remain the existing DAG's work, rather than duplicate new work. Required dry-run and delivery results are recorded by the delivery command.
