## Worker report

Q160 split `lem-trf-free-normalized-homology-injectivity-transfer` in `dag/nodes/sec-trace-formula/lem-trf-free-normalized-homology-injectivity-transfer.json`. Its statement, source, statement dependencies, inherited searches, created record and blueprint ancestry are retained. The item now has four proof steps, their exact proof dependencies, proof provenance and split report. Also written: `citations.json` and this report. The search command wrote `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. Each step is a short calculation with the free-group generators, the face identities, or the quotient defining homology. Introducing a node for one of these calculations would violate the brief's elementary-node restriction.

Attachments: none. A search for the exact blueprint tag and for normalized injectivity/free simplicial homology in `lean/WeilConjectures/` found no project declaration stating this item. Generic finite-free derived-module results are different statements.

WANTED: none. The proof source is present: `literature/stacks-project/simplicial.tex`, Tag 08P2, label `lemma-homotopy-equivalence`, specifically the commutative evaluation square and the injectivity paragraph at lines 5935–5958. The tag-to-label mapping was checked in `literature/stacks-project/tags/tags`.

No statement dispute was found. Stacks uses the other face normalization, whereas the item explicitly uses the kernels of the higher faces and differential d_0. The proof is written directly with the item's convention, so no comparison isomorphism or sign convention is taken on trust. No hypothesis of set homotopy equivalence or surjectivity on homology is used: the source's final injectivity argument only needs the injectivity assumed here. The item already states exactly that weaker input to this subargument.

No work remains in this stage-1 split. There are no Lean edits or compiler invocations. The statement-only nodes of other groups were not changed.

## Searches and blueprint

I ran the prescribed leanfinder, loogle, grep and leansearch commands with the item's own id. I read the returned hit statements, then tried a second leanfinder formulation. Their exact query texts and actual results are appended to the item's `mathlib_searches`, preserving the searches inherited from its creation. `searches.jsonl` records all searches of this dispatch. No service failure was turned into a no-match verdict.

The closest hits are `AlgebraicTopology.NormalizedMooreComplex.map`, the monomorphism of the inclusion from the normalized Moore complex to the alternating-face complex, generic results making boundaries zero in homology, and monomorphisms on representation-group chains. These do not imply the present transfer in one line. I read `Mathlib/AlgebraicTopology/MooreComplex.lean:64–136` and `Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean:186–191` to check what the named maps and boundary statements actually provide. The proof does not invoke those categorical statements; it uses the explicit quotient in the item.

The blueprint searches `normalized homology`, `08P2` and `free abelian` found no blueprint statement matching this item. The free-abelian hits concern divisors, torsors, Kummer base change and hypercover resolutions. The ancestor command confirmed `lem-trf-local-term-locality`. I read that node's current statement and proof under `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`, as well as the chapter and unit records. The simplicial lemma is a tool in the inherited nearby-cycle branch, not a new local-term route. Its inherited precise `from.place` and `via` chain remain intact, and `same_as` remains empty.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to distinguish. The whole-DAG Tag 08P2 search located the parent simplicial-homotopy quasi-isomorphism, its free-homotopy input, the polynomial augmentation argument, the cotangent ancestor, and the sibling surjectivity transfer. The parent uses this item; the sibling asserts surjectivity rather than injectivity. Neither is cited to prove this item, avoiding a cycle or substitution of the opposite half of the argument.

## Review by Q160

I read Stacks Tag 08P2's proof rather than only its lemma statement. Its injection paragraph chooses a normalized cycle, lifts the cycle and its nullhomology witness by subtracting the zero generator, then uses injectivity upstairs and evaluation downstairs. Those are exactly steps 2–4 here. In particular, a cycle lift alone is insufficient for injectivity; the proof explicitly constructs the target boundary lift and its differential.

For step 1 I opened both cited definition nodes. `def-weil-pbc-simplicial-object` defines face maps and says a simplicial morphism is a natural transformation commuting with all operators. `def-weil-pbc-simplicial-set` defines the ordered simplex category and its face injections. Their verbatim statements are quoted in `citations.json`. Composing those injections gives the two displayed face identities. Evaluation commutes with each operator on a generator, hence on its finite integral linear combinations. This establishes preservation of normalization and differentials without citing a definition as if it asserted an unproved comparison theorem. The normalization complex identities are shown directly, including the bottom zero differential.

Step 2 uses the definitions written in the item's own statement and step 1, with no additional cited node. Every positive face of a normalized element vanishes, and the zeroth face of a positive-degree cycle vanishes. Thus the difference of the two basis generators has the required vanishing faces. For y I verified the full range 1 through n+1 and used d_0 y = f_n(x), so the constructed element really is the desired boundary witness. The assertion f_n(0)=0 uses the given additivity, not an assumption about arbitrary simplicial-set maps.

Step 3 unpacks the quotient kernel/im definition twice: first to choose y from the vanishing image of the class of x, and then to choose u after the lifted class vanishes by the assumed injectivity. It does not assume evaluation is injective, does not assume a splitting, and does not use an exact-sequence or homotopy theorem. All the needed cycles and boundaries have been produced in earlier steps.

Step 4 checks every higher face and d_0 of evaluation of u by writing the actual finite sum. Therefore evaluation of u is normalized and has boundary x. The last inference of injectivity subtracts two classes in an abelian group; no non-elementary lemma is hidden under the word transfer. All four steps are below 1000 characters; none hides a long unnamed comparison.

I checked n=0 separately: normalization there is the full degree-zero group, the outgoing differential is zero, and the only faces used to detect a boundary are those from degree one. For zero simplices the lifted differences are literally zero even though the generator [0] is not itself zero in a free abelian group. For constant simplicial groups positive normalized degrees vanish, and in degree zero the formulas reduce to a kernel element being zero. The zero source, zero target, zero map and identity map cause no additional hypothesis or exception. The pointwise calculations do not assume the map z ↦ [z]−[0] is additive; it generally is not.

I checked delivery-errors B–E against the files and source. There is no new statement-only node to carry a hidden proof, duplicate, missing hypothesis or unchecked Mathlib match; no clause was relabelled as a new lemma. Every non-definitional operation in this proof is written out as a short elementary calculation. The item statement and source intent agree, citations quote what their steps use, and no SGA source, derived comparison or off-unit theorem has been introduced. Nothing required correction in the statement; the repair was to replace its empty proof with the actual generator and quotient argument.
