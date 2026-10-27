# Q108: lem-sfb-rational-highest-weight-modules

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-highest-weight-modules.json`: item, statement; split into eight proof steps, unchanged statement and statement dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-semisimple-root-decomposition.json`: new statement, unsplit; no exact Mathlib match for the full root-decomposition/simple-generation package under the maximal-abelian hypothesis.
- `dag/nodes/sec-six-functors-basics/lem-sfb-verma-monomial-weight-basis.json`: new statement, unsplit; no Mathlib Verma/PBW module construction found.
- `dag/nodes/sec-six-functors-basics/lem-sfb-integrable-upper-bounded-weight-finiteness.json`: new statement, unsplit; Mathlib finite-weight results assume an already Noetherian ambient module.
- `citations.json`: one verbatim statement quotation for each citation in each item proof step.

Three new nodes; zero Mathlib leaves. All three new nodes carry statements only, empty proof/proof_deps, and null proof_origin. Their lower-level proofs remain later stage-1 work. The sandbox also retains the genuine search log `searches.jsonl` and the item-specific writing helper `write_split.py`.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item id, highest-weight/fundamental-weight terminology, Verma modules, root-system and integrability terminology found no declaration stating the item, or the new prerequisites. Triangular-field-model and l-adic weight results are unrelated.

## Wanted sources

WANTED: J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapters V-VII, root-space/simple-root-generation theory, ordinary PBW and the highest-weight quotient construction, for lem-sfb-rational-highest-weight-modules and its three new prerequisite nodes. In particular the argument needs its split rational-field version; a theorem over C alone is not being treated as descent to Q.

Milne, *Algebraic Groups* (2017), is available and was read at printed pp.503-511. Page 503 explicitly assumes the background theory of semisimple Lie algebras and describes the split root decomposition; p.508 uses the integral-weight gradation of rational representations; p.511 uses fundamental weights in Corollary 23.73. These passages motivate the input but do not contain its Verma-module proof. The item's proof is therefore marked `proof_origin.by = agent`, rather than falsely attributed to a full proof in Milne. No literature was downloaded and no SGA route was used.

## Problems in the supplied material

The item was an unsplit, statement-only prerequisite with prior Mathlib searches. Those searches and the original source, creation record and blueprint lineage were retained; searches run by Q108 were appended, not invented in their place. There was no sandbox split to resume. The statement is correct as written; no STATEMENT-DISPUTED correction was needed.

The upstream reference to Lemma 22.24 does not itself construct fundamental highest weights. This split supplies the missing rational construction using an explicit quotient of U(g), rather than invoking an unspecified complex representation or a group highest-weight theorem which would depend on the group-realization result above this item.

`tools/blueprint_refs.py ancestor lem-sfb-rational-highest-weight-modules` reports `None`: the existing created.item chain has no recognized imported ancestor. I retained the existing null ancestor, fully specified place and via chain, and prefixed this item for new-node via lists. The place identifies the inherited direct-image-finiteness / alterations / projective stable-moduli / Chevalley representation branch. I read the current `literature/blueprint/latest/` (main-20261024), including the six-functor stability unit and direct-images proof, rather than relying on the older unit source path. I did not edit the unit or chapter.

## Not duplicates

lem-sfb-split-semisimple-root-decomposition vs lem-sfb-chevalley-root-normalization: the existing node assumes the reduced root system, its root-space decomposition and a simple base, and produces a fully normalized Chevalley basis with integer structure constants. The new node establishes the root pairing from the maximal-abelian diagonalizing hypothesis and the generation of n+ and n- by simple root spaces; it does not normalize all structure constants.

lem-sfb-split-semisimple-root-decomposition vs lem-sfb-serre-rational-presentation: the existing node constructs one Lie algebra from a root system by generators and relations. The new node concerns an arbitrary given split semisimple Lie algebra and its given h, and does not assume or assert an identification with that presentation.

lem-sfb-split-semisimple-root-decomposition vs lem-sfb-root-base-rational-integral-spans: the existing abstract root-pairing lemma assumes the root-pairing axioms and proves the integral and rational simple-base spans. Step 1 reuses it; the new node supplies those axioms from the Lie algebra and also the simple root generators.

lem-sfb-split-semisimple-root-decomposition vs lem-sfb-semisimple-roots-span: the existing node concerns algebraic groups over algebraically closed fields and their character/cocharacter lattices, not arbitrary rational Lie algebras and root spaces.

lem-sfb-verma-monomial-weight-basis vs lem-sfb-kostant-integral-pbw: the existing node gives a Z-basis of a particular integral subring of U(g) after assuming a Chevalley basis. The new node gives a Q-basis of U/I_eta for every rational eta and its ordinary weight spaces. It neither assumes nor proves integral straightening for the Kostant form. In particular, the integral PBW node does not state the Verma quotient or its nonzero highest line, so citing it alone in the item would fail C4.

lem-sfb-verma-monomial-weight-basis vs lem-sfb-rational-highest-weight-modules: the Verma quotient exists for every rational eta, including nonintegral and nondominant eta, and is normally infinite-dimensional and nonsimple. The item constructs, rather than delegates, the quotient by the singular simple-root powers.

lem-sfb-integrable-upper-bounded-weight-finiteness vs lem-sfb-rational-highest-weight-modules: the new lemma is a conditional criterion on an already given, possibly noncyclic weight module with support in a finite union of upper cones. It constructs no module, no highest vector and no simple quotient. Steps 3-5 of the item prove its nontrivial integrability hypotheses for the explicitly constructed quotient; step 7 proves simplicity by a separate elementary quotient argument.

The DAG was searched as a whole by keywords and then by parsed titles/statements to exclude irrelevant search-history matches. I opened the statements of all the existing nodes compared above. Whole-blueprint searches included highest weight, Verma, root system, integrable, semisimple, Poincare and weight; none states these three prerequisites. No relevant Stacks tag occurs: these are Lie-theoretic inputs, not scheme-theoretic Stacks statements.

## What remains

Nothing required for this one-level split is omitted. The three new nodes are intentionally unsplit. Obtaining Serre and subsequently splitting these prerequisites remains future work, not a claim that the whole transitive DAG is finished. No Lean source was written and no compiler, Lake or build command was run.

## Review by Q108

I checked the statement against the actual use in Milne's rational Chevalley representation argument. The important hypothesis is that h acts diagonally over Q itself. I kept that hypothesis, and introduced no algebraic closure, faithful-representation condition, simply connected group, or regularity condition on lambda. The zero algebra has the stated one-dimensional trivial representation. For sl2, the singular vector is f^(n+1)v for n=lambda(h)>=0, and the quotient has weights n,n-2,...,-n; n=0 gives the trivial module. For products of simple algebras, the construction uses all simple roots, so it does not silently impose simplicity of g.

For step 1 I opened the full statements of lem-sfb-split-semisimple-root-decomposition and lem-sfb-root-base-rational-integral-spans. The first really supplies both spanning families, the crystallographic integer pairing, and compatible root/coroot reflections. Thus the latter lemma's perfect pairing, finiteness, reducedness, spanning and sign-coherent base hypotheses all hold. Its conclusions are exactly the simple-coroot rational basis and integral spanning used to show P is the dual integer lattice. The coordinate calculation, not a new node restating the first clause, produces the fundamental weights.

For step 2 the new root-decomposition statement supplies normalized rational rank-one triples and simple root generation. The Verma node explicitly states the left-ideal model, its nonzero highest vector, its ordinary eigenspaces, the highest line and finite weight-space dimensions. I checked that the argument takes these exact conclusions, not generalized eigenspaces of an existing finite-dimensional representation. For the new root node I read Milne p.503 and pp.508-509 plus Mathlib RootSystem.lean:387-450 and Basis/Basic.lean:15-74; the latter explicitly leaves general basis existence as TODO. This is why partial Mathlib root-system support is recorded as a candidate, not a false leaf.

Step 3 is a written commutator calculation. The sole citation is the root-decomposition node, whose statement includes [e_i,f_i]=h_i, [h_i,f_i]=-2f_i, cross-commutation for different simple roots, and generation of n+. The factor m(n_i-m+1) was checked at m=1 and m=n_i+1, with the latter zero; n_i+1 is strictly positive even on a dominant wall. All positive root spaces annihilate w_i because their Lie algebra is generated by the e_j. I did not leave a singular-vector theorem as an uncited assertion.

For step 4 I checked the Verma statement again with eta=nu_i, which need not be dominant or integral: its hypothesis allows every rational functional. The explicit map from that left-ideal quotient is well-defined because its generators kill w_i. Its image, not an assumed injective map or an assumed irreducible module, supplies the weight bound on Uw_i. The simple-root independence prevents lambda from occurring in any of those images, so their sum misses the highest line. The image is graded, making N graded and giving the ordinary quotient weight decomposition. This proves nonzero Q and finite weight-space dimensions before any global finiteness is used.

For step 5 the cited root statement says ad(x) is nilpotent on g. I wrote the derivation expansion on words to extend this to local nilpotence on U, then the binomial commutator identity to extend annihilation of the cyclic generator to every u times that generator. This corrects the tempting circular argument that root vectors are nilpotent simply because Q is finite-dimensional: Q is not known finite-dimensional until step 6. The proof of step 5 is one explicit propagation calculation, 980 characters, not a hidden separate existence or comparison lemma.

For step 6 I checked every hypothesis of lem-sfb-integrable-upper-bounded-weight-finiteness against steps 2, 4 and 5: rational Lie algebra and rational triples, ordinary weight direct sum, finite-dimensional individual spaces, a finite upper-bound set {lambda}, and local nilpotence of both e_i and f_i. None of these hypotheses is the conclusion finite-dimensionality. In the source search for this new node I read Mathlib Weights/Basic.lean:686-700: its finite-weight theorem assumes IsNoetherian on the whole module, so it cannot discharge this criterion. The intended lower-level argument is rational rank-one strings/Weyl invariance plus finiteness of the lattice points in the intersection of the finitely many reflected upper cones. Finite weight multiplicities then give finite dimension; the criterion also allows zero modules, empty bounds and rank zero. It is recorded as an agent formulation with its missing full background reference stated openly.

Steps 7 and 8 use only elementary linear algebra on the now finite-dimensional rational representation. A proper submodule of largest dimension exists among the finite set of possible dimensions; no complete reducibility theorem is used. I verified that killing the generator would kill all of Q, so its image in the simple quotient is nonzero. For ordinary weights in this last quotient I wrote out rational separating operators and Lagrange projectors preserving the submodule. Thus no diagonalizability over an algebraic closure, descent or unstated semisimplicity theorem is being smuggled into the last step. Integral weights follow from the already proved lattice calculation, while Omega is defined by nonzero spaces so its nonvanishing clause is automatic.

For the new Verma node I read the available Milne passages and Mathlib's enveloping-algebra construction and PBW discussion; neither was misrepresented as a full proof of the new statement. As small-case tests, sl2 with arbitrary nonintegral eta still has its infinite monomial basis, the highest line remains one-dimensional, and each weight space is one-dimensional; a rank-zero algebra gives only the empty monomial. The finite-dimensionality node does not assert that this arbitrary Verma module is finite, because its simple lowering operator is not locally nilpotent. This separates the three genuine prerequisites from clauses of the item itself.

I checked delivery-errors B-E with the node statements open: objects and notions are introduced, TeX has a single escape level, sources distinguish available text from WANTED background, no fabricated search is present, no new node carries a proof or repeats an existing theorem, and all step citations are quoted verbatim in citations.json. The new dependencies point downward; none invokes the item or its algebraic-group ancestors. All proof steps are below 2000 characters. The only reused nondefinition node is the root-base lemma in the same unit, so no off-unit tool permission is needed. I retained the original statement and all inherited metadata.
