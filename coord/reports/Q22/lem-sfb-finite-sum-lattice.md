## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-sum-lattice.json`: statement split into five proof steps, with unchanged statement and statement dependencies; no exact Mathlib match for the whole item.
- `citations.json`: six verbatim dependency quotes, one for each step/dependency pair.
- `searches.jsonl`: the five actual Q22 searches, preserved as emitted by msearch.py. The item's inherited Q46 search records are retained as well.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are reused for finite freeness, basis cardinality and linear homeomorphisms.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, finite sums of lattices, lattice sums, `IsLattice`, `finiteSumLattice`, `stratifiedLattice`, and the relevant integral-basis construction names. The search found only unrelated coherent ideal-sum constructions and the algebraic use of `Module.basisOfFiniteTypeTorsionFree'` in `Algebra/Module/AdicTowerLattice.lean:81`. None states every clause of this item, so none is claimed as an attachment. No compiler or Lake tool was run.

## WANTED

None for this split. The existing coefficient-field structure nodes retain responsibility for their own sources; this delivery does not claim to prove them.

## Corrections and source audit

The imported statement is true as written. Its blueprint ancestor is `sk-lem-stratified-lattice`, specifically the final trace paragraph of the current 2026-10-15 unit. I read the chapter and unit records, the ancestor split, and `sk-lem-stratified-lattice-trace.proof.md`, especially the sentence about the finite sum being finitely generated, torsion-free, free, and spanning. I also read Stacks Tag 0AUW, label `more-algebra-lemma-dedekind-torsion-free-flat`, in `literature/stacks-project/more-algebra.tex:4954` and its proof. Part (3) gives finite freeness over a PID, not the topology claim. The proof is therefore marked agent-written: it follows the blueprint's algebraic argument, and explicitly supplies the denominator, rank and topology details instead of attributing them to 0AUW.

The item previously had no proof. I have not changed its statement, source, creation record, statement dependencies or blueprint ancestry. The added proof dependencies replace no unit-level route: they establish precisely the algebraic and topological lattice fact needed in the trace paragraph. The local-field DVR theorem is declared as a generic off-unit tool in `split_report.tool_uses`; the other outside-unit dependencies are existing Mathlib leaves. No SGA source is used.

The whole-DAG searches for 0AUW and the relevant concepts, plus `blueprint_refs.py search 'lattice'`, `search 'finite sum'`, and `search 'torsion-free'`, located the existing freeness and coefficient-ring nodes. In particular, the item does not need a new statement of the DVR finite-free theorem. The dimension node's statement explicitly includes equality of the cardinalities of finite bases, with `Module.finrank_eq_card_basis` in its verified Mathlib match; that is the precise clause used, not an unstated consequence of a definition.

Mathlib's `Submodule.IsLattice.sup` (`Algebra/Module/Lattice.lean:107-109`) only treats a binary algebraic sum. `Module.Basis.extendOfIsLattice` (same file, lines 145-158) starts with an already-known lattice and basis. These are relevant ingredients but do not each give the whole finite-family, rank and subspace-topology assertion by a one-line specialization. The recorded two semantic phrasings, Loogle, grep and LeanSearch results were read. ZLattice and number-field mixed-embedding results use different lattice/topology hypotheses. I also read the matched existing freeness construction in `LinearAlgebra/FreeModule/PID.lean:375-390`, basis-cardinality theorem in `LinearAlgebra/Dimension/StrongRankCondition.lean:451-453`, and the linear-homeomorphism construction in `Topology/Algebra/Module/FiniteDimension.lean:367-372`.

## Not duplicates

No new nodes. All the structural facts are citations of existing nodes.

## Review by Q22

For Step 1 I opened `lem-weil-l-adic-extension-integers-dvr` and read its statement: clause (1) supplies that E is the fraction field of A and clause (2) supplies the DVR property. These hypotheses match the finite coefficient extension fixed in the item. The remaining work is written in the step itself: the finite union of the given finite bases generates the sum; multiplication by a nonzero scalar is injective inside E^r; and one member of the nonempty family already spans E^r over E. Thus neither finite generation nor full span is being silently taken from a definition node.

For Step 2 I opened `lem-sc-dvr-fg-torsionfree-free`, whose full statement concerns a finitely generated torsion-free module over a DVR and concludes finite freeness. Step 1 supplies exactly its two module hypotheses and its ring hypothesis. I take only the existence of a finite A-basis from this citation, not the asserted rank or topology. This is the reusable form of Stacks 0AUW(3), so no duplicate freeness lemma was created.

For Step 3 I checked the fraction-field clause again and wrote out the finite denominator product: every coefficient c_i is a_i/s_i, s is nonzero, and every s*c_i is in A. A-independence therefore proves E-independence. The finite basis spans because it generates Lambda and Lambda already E-spans E^r. I opened `def-weil-vector-space-dimension`; its statement literally says that any two bases have the same number of elements, and its existing Mathlib record names the basis-cardinality theorem. This gives n=r by comparison with the standard basis. The citation quote copies that actual clause. No existence of an E-basis or dimension formula is inferred just from the name of a definition.

For Step 4 I opened `def-weil-l-adic-coefficient-extension` and `lem-weil-pbc-finite-dimensional-linear-homeomorphism`. The former states completeness and the extension of the l-adic absolute value; the latter applies to every linear equivalence between Hausdorff topological vector spaces over a complete nontrivially normed field when the source is finite-dimensional. Here E is complete, the prime l has norm 1/l<1, and both spaces are E^r with their product topology and standard finite basis. Addition and scalar multiplication are continuous coordinatewise, so all hypotheses hold. The chosen lattice basis defines an ambient E-linear equivalence, exactly the object in the cited statement. I deliberately apply the theorem to E^r, not to the A-module Lambda as if it were an E-vector space.

For Step 5 the argument is elementary restriction of the two continuous inverse maps. I checked the topologies explicitly: finite products of subspaces A of E have exactly the induced topology from E^r, and N is given precisely its induced topology. B(A^r)=N follows from the chosen A-basis. This proves the assertion for every basis that is an A-basis and an E-basis, for the sum as well as for each summand. No compactness, quotient topology or mistaken discrete topology is used.

I checked small and limiting cases. If r=0, all modules and coefficient powers are singletons and the empty basis works. If J is a singleton, the argument recovers that lattice and its topology for every eligible basis. In rank one, the sum of pi^a_j A is pi^(min a_j) A, and multiplication by its generator restricts the ambient field homeomorphism as asserted. An empty family would fail to span for r>0, explaining the nonempty hypothesis; an infinite family such as pi^(-n) A can have non-finitely-generated sum E, explaining finiteness. No equality of the input lattices and no common input basis was assumed.

Against delivery-errors B--E: there are no new nodes to carry hidden proofs, missing definitions or duplicate tags. Every non-elementary invoked result is among the step's explicit existing citations, and I opened each statement before writing its verbatim quote. The only elementary step spells out its topological argument. The freeness clause is proved using a smaller existing generic theorem, rather than moved to a new node repeating the item. No induction, undocumented transport, extra hypothesis, or cyclic dependence on the lattice-sheaf construction is used. All five steps are under 2000 characters. The item remains on the trace paragraph's route.

## Unfinished work

None for the one-level stage-1 split. No new unsplit dependency was needed. The required server dry run and delivery results are recorded below after they run.

## Validation

The first dry run rejected the Step 2 quotation as shorter than 40 characters. I replaced it with the entire existing DVR freeness statement, including all hypotheses; the mathematical proof was unchanged.
