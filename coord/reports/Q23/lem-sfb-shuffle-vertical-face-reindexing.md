## Worker report

The module `Sheaf.AlgebraicTopology.ShuffleVerticalFaceReindexing` defines the literal labeled vertical-face set and states `AlgebraicTopology.ShuffleVerticalFace.vertical_face_reindexing`. Its only postponed proof is that theorem (`sorry`); the face definition has real subtype data. No new independent notion or dependency repair is needed. The existing definition node `def-sfb-shuffle-word-combinatorics` is added to `stmt_deps` to record ownership of the reused definitions. The horizontal-face theorem is not a DAG dependency and is not used to construct anything.

Read the assigned node's complete statement and ten proof steps, the free-module dependency, the landed combinatorics node, and all six recorded combinatorics declarations in their source module. The source application was read in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). As the node explicitly records, this paragraph supplies the application only, not the combinatorial lemma; Weibel §8.5 is unavailable locally. No source-based statement correction is made. No repair note exists for this item. The requested CompactObject example file was read: its current contents are only `module` and a withdrawn-module comment; the landed horizontal-face module supplies the substantive current style example.

Clause correspondence (write B=b+1 for the positive vertical degree; thus the theorem covers every B>0 without subtraction casts):

- Arbitrary a,B≥0 and n=a+B: natural-number parameters `a b`; positive input `Word a (b+1)` and shorter output `Word a b`. The independent clause `IsEmpty (VerticalFace a 0)` handles B=0 for every a.
- Words with exactly a H and B V: imported `ShuffleHorizontalFace.Word a B` is the subtype of Boolean lists with length a+B and the two specified counts. H is false; V is true. No path ordering, nondegeneracy or distinctness restriction is imposed.
- A_k and B_k: imported `horizontalCount` and `verticalCount` count false and true in `w.val.take k`.
- Inversion number I: imported `inversions` counts precisely pairs r<s in range whose letters are V,H. Imported `sign` is the integer `(-1)^inversions`.
- Arbitrary sets X,Y and input sequences of lengths a+1,B+1: the final universal quantifiers use `X : Type u`, `Y : Type v`, `x : Fin (a+1) → X`, `y : Fin (b+1+1) → Y` with explicitly bound, independent universes. Imported `evaluate` is the full list of prefix-indexed pairs. No equality, inhabitation or distinctness assumptions are added.
- d_k on strings: `List.eraseIdx k`; d_j on the vertical input tuple: `Fin.removeNth (Φ p).1 y`. Its definition is precomposition with the order-preserving skip map `succAbove`, exactly deletion of entry j.
- Labeled vertical set: `VerticalFace a B` is a subtype of `Word a B × ℕ`, retains both word and mark, requires k≤a+B, and is the disjunction of k=0 and initial V, k=a+B and terminal V, or 0<k<a+B with both neighbors V. Option access is `some true`, excluding an absent letter.
- Bijection: `∃ Φ : VerticalFace a (b+1) ≃ Fin (b+2) × Word a b`. The equivalence supplies both inverse identities; Fin(b+2) is exactly the labels 0,…,B.
- Forward label and collapsed word: `(Φ p).1.val = verticalCount p.val.1 p.val.2` and `(Φ p).2.val = p.val.1.val.eraseIdx (min k (a+(b+1)-1))`. At k=0 this erases the initial V, at k=n it erases n−1, and at an interior k it erases the second V of the adjacent pair.
- Interior: the strict-mark implication states `1 ≤ j ∧ j < b+1`, `k = horizontalCount w k + j`, and `inversions w = inversions shorter + (a-horizontalCount w k)`. This is the node's i=A_k, k=i+j and I(w)=I(shorter)+a−i (the latter two forms agree since i≤a).
- Initial endpoint: `k=0 → j=0 ∧ inversions w = inversions shorter+a`.
- Terminal endpoint: `k=a+(b+1) → j=b+1 ∧ inversions w = inversions shorter`. The mark's equality is exactly k=a+B=n.
- Inverse at j=0: `(Φ.symm q).val.1.val = true :: q.2.val` and mark zero. Inverse at j=B: append `[true]` and mark a+B.
- Interior inverse: `∃ P Q : List Bool`, shorter word `P ++ true :: Q`, `P.count true + 1 = j`, reconstructed word `P ++ true :: true :: Q`, and mark `P.length+1`. The count condition selects the j-th V counted from one, not an arbitrary occurrence.
- Evaluated-string identity: `(evaluate w x y).eraseIdx k = evaluate shorter x (Fin.removeNth j y)` for every labeled input.
- Sign identity: `sign w * (-1 : ℤ)^k = (-1 : ℤ)^(a+j) * sign shorter`. The a contribution is retained, including at endpoints.
- Free-module interpretation: the same final clause equates `Finsupp.single` of the two strings, with coefficient `(1 : ℤ)`, in the free integral module on strings. Lists are the ambient set of strings; every occurring string has exactly the required length. Equal lists and their equal basis symbols are both stated.
- B=1, a=0 and B=0 are included, without extra hypotheses. No interior face is possible with one V; if a=0 all inversions are zero and k=j; with B=0 every marking test fails, including the empty word.

Dependencies and declarations:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`, read with its complete class signature and basis docstring. `Finsupp.single` is the canonical basis-symbol interpretation of the free ℤ-module on lists. The recorded Mathlib module is publicly imported.
- `def-sfb-shuffle-word-combinatorics`: `Sheaf.AlgebraicTopology.ShuffleHorizontalFaceReindexing`, declarations `AlgebraicTopology.ShuffleHorizontalFace.Word`, `horizontalCount`, `verticalCount`, `inversions`, `sign`, `evaluate`. Each was read in full, including the evaluation's bounded prefix indices and docstrings. The owning definition node was already landed; no definition is copied or re-recorded.
- The original sole proof dependency is the same free-module node, already publicly imported. No downstream lattice-path theorem is imported.

Edge checks: exhaustive finite enumeration for a,B=0,…,4 verified all 545 labeled vertical faces: forward image, injection and surjection onto all labels/shorter words, both inverse identities, interior/end inversion counts, signs and evaluated-string equalities for distinct-coordinate and fully repeated inputs. In particular a=B=0 gives no face, B=1 has only endpoint faces, a=0 gives the all-V word and k=j, and the length-one all-V input retains its two different endpoint labels although both shorten to the empty word. Empty underlying X or Y simply has no input tuple of positive length and is not excluded by an added hypothesis. Enumeration is a consistency check, not a Lean proof or an exhaustive mathematical verification.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder "Bijection of vertical deleted vertices of binary shuffle words with a vertical face index and a shorter shuffle, compatible with inversions and Koszul signs"`: 8 hits, including `SSet.prodStdSimplex.objEquiv_δ_apply`, simplex degeneracy normal forms and insertion. None states this labeled-word equivalence or its signs and endpoint formulas.
- `msearch.py ... loogle '"shuffle", "sign"'`: zero hits.
- `msearch.py ... grep 'shuffle|Shuffle' AlgebraicTopology`: zero Mathlib hits.
- `msearch.py ... leansearch "Bijection between labeled vertical deleted vertices of binary shuffle words and vertical face indices paired with shorter shuffles"`: 8 irrelevant hits including equivalence constructors, game relabeling and graph Hamiltonian walks; no match.
- Direct `rg` for shuffle/Shuffle/verticalFace/VerticalFace in `lean/WeilConjectures`, `lean/Sheaf` and `dag/nodes/sec-six-functors-basics` located the horizontal-face and mixed-corner modules and the existing combinatorics ownership node; no vertical-face statement exists. Direct search for the assigned id in `lean/WeilConjectures` returned no match. Search for `AlgebraicTopology.ShuffleVerticalFace` in `dag/lean_names_upstream.json` returned no match.

Server compilation with the prescribed `scompile.py` passed in both reported sandbox/library checks (1.1 seconds each), with no diagnostics. `set_option autoImplicit false` and `universe u v` enforce explicit bindings. `deliver2.py Q23 lem-sfb-shuffle-vertical-face-reindexing --no-push` returned `OK (dry run): commit 20366bc6adf passes the preflight and compiles; nothing pushed`. The final delivery command reruns the checks before pushing; its output is the authoritative delivery result.

## Second reading by Q23

This is the worker's final self-reading, not an independent-agent review: the dispatch brief forbids starting agents and assigns the independent review to the maintainer. I reopened the source node and delivered module and checked the correspondence above. The arithmetic parameterization uses shorter degree b rather than excluding any positive B; endpoints n and n−1 are distinguished in the collapsed-word formula; the interior inverse counts V letters in P before adding one; and the sign exponent is a+j. Reused definitions are credited through their already landed definition node instead of making the horizontal-face theorem a statement dependency. No mismatch was found requiring a statement correction. Definitions contain no sorry, and the only theorem proof is sorry. All a=0, B=0, B=1, repeated-input and empty-word cases remain covered. The maintainer's independent semantic review remains pending.
