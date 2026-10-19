# Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-coef-fixed-object-simplicial-mapping-calculus.json` — statement node, split; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-fixed-object-simplicial-sm7-free-cell.json` — statement node, unsplit; no Mathlib match.
- `citations.json` — verbatim step citations.

Attachments: none. No declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` carries the blueprint tag or the target statement.

WANTED: archival copy of Dwyer–Kan, *Simplicial localizations of categories*, Section 7.1 and Proposition 7.2, printed pp.276–277, for the fixed-object simplicial model and mapping-calculus source.

The imported target is not present as Lean, and no source declaration gives it. The statement retains the empty-object and loop cases. The imported dependency `lem-coef-fixed-object-simplicial-free-calculus` gives the fixed-object model structure and free-cell presentation; `lem-coef-fixed-object-free-arrow-adjunction` gives the free-arrow/evaluation adjunction. I added one smaller node for the missing free-cell tensor pushout-product calculation instead of hiding that lemma inside the corner-map step. Mathlib searches (two phrasings each for LeanFinder, Loogle and grep) found only generic simplicial-set pushout-product or ordinary category declarations.

Nothing remains unfinished in the split. The proof is agent-written because the cited archival paper is not stored locally; its route is recorded in `proof_origin` and the WANTED line above.

## Review by NI

I read the complete imported item node, its blueprint ancestry (`prop-coef-integral-exceptional-adjoint`, proof paragraph 2), and the statements of every cited dependency. The fixed-object free-calculus statement supplies the model structure, local weak equivalences/fibrations and retracts of free extensions. The sorted-simplicial-algebra statement supplies the finite-product algebra model structure, generating boundary and horn cells, cocompleteness and the lifting characterizations. The free-arrow statement was checked for arbitrary `a,b`, including `a=b`, and for empty `O`; it says exactly the length-one-word Hom adjunction used in step 6. The Kan node was checked for the boundary/horn model structure and for trivial cofibrations as retracts of horn-cell composites; the simplicial-set anodyne pushout-product node supplies the horn pushout-product case. The SM7 generator-extension node states precisely the reduction from generating pushout products to the corner-map Kan fibration and its triviality.

Step 1 uses only the fixed-object model and sorted-algebra generating-cell statements, and I checked that the identification of the `(u,v)` sorts with mapping simplicial sets preserves the loop and empty-object cases. Step 2 explicitly defines `Fun(K,B(u,v))`, diagonal composition, and constant identities; the tensor is the coequalizer of the free-algebra construction, whose existence follows from the cited cocompleteness statement, with the universal property written in the step. Step 3 checks restriction along every simplex operator, diagonal composition, identity, and associativity, so the displayed mapping sets are an enriched simplicial mapping object. Step 4 cites the new free-cell statement verbatim and checks its hypotheses: `i` is a boundary or horn generator and `j` is a simplicial monomorphism; the Kan and anodyne citations cover the weak/trivial cases. Step 5 applies the cited SM7 extension with the exact generating sets and identifies its conclusion with the item’s corner map. Step 6 applies the free-arrow adjunction degreewise, uses the cartesian closed simplicial-set Hom identification, and checks that boundary/horn generators are preserved, giving the Quillen adjunction and naturality.

I tested the edge cases in the statements: `O=∅` makes all fixed-object Hom sets terminal and the generating families empty; `a=b` permits arbitrary loop words; `K=∅` gives the identity-only free category; `K=Δ⁰` gives one generating arrow; and all constructions are degreewise, so degenerate simplices are handled by restriction. `srvcheck.py` passed both `check_dag` and `review_split` before this report was written.
