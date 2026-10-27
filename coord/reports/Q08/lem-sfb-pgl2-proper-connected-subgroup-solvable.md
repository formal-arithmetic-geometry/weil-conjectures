# Stage-1 delivery: lem-sfb-pgl2-proper-connected-subgroup-solvable

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-pgl2-proper-connected-subgroup-solvable.json`: item, split, with its statement and statement dependencies preserved verbatim.
- `dag/nodes/sec-six-functors-basics/lem-sfb-connected-group-dimension-two-solvable.json`: one new statement-only prerequisite, unsplit; no Mathlib match. It states Milne Corollary 17.27 for every smooth connected affine group of dimension at most two, in every characteristic.
- `citations.json`: one complete verbatim statement quotation for every citation of every item step.
- `searches.jsonl`: the five searches actually run with msearch.py. `milne.txt` is the local PDF text extraction; helper script `write_split.py` records preparation only and is not a delivered node.

There are one new node and zero new Mathlib leaves.

## Attachments

None. Searching the live project source under `lean/WeilConjectures/` for the item id, PGL/ProjectiveGeneralLinear, solvable/solvability, and the small-dimension group statement found Lie-algebra and abstract-group facts, not the requested group-scheme theorem. In particular those are not attachments for this item. The existing smooth-geometrically-reduced node is reused in step 2.

## WANTED

None. The needed Milne iAG2017 PDF and Stacks sources are locally available.

## What changed and what was wrong

The item had no proof. Its statement is correct with its reducedness, connectedness, algebraic closure and proper-inclusion hypotheses, and none was changed. Milne's phrase “every proper subgroup” in Theorem 20.16(c) implies (d) is read with its connected group-variety image hypothesis; it does not claim the result for arbitrary disconnected finite subgroups. The split retains those hypotheses explicitly.

The argument now proves smoothness from the existing reduced identity-component result, obtains the affine integral ambient group of dimension three from existing results, proves that a proper closed subgroup has genuinely proper support, and proves the dimension drop by extending chains of irreducible closed subsets. Only the general small-dimension solvability theorem is new. It is a genuine input, not a renamed PGL2 theorem: it concerns every smooth connected affine algebraic group, contains no PGL2, embedding, proper-subgroup or reducedness-to-smoothness assertion, and is applied only after the item's geometric reduction has been proved. The source's Borel/nilpotence proof of this general theorem is left for that new node's own split, as the one-level rule requires.

The ancestry command returned `blueprint.from.node = None`; the item has the existing long ancestry through `lem-sfb-rank-one-adjoint-projective-linear` to the alteration prerequisite. The new node preserves that ancestry, prepending the item, and makes its Corollary 17.27 role explicit. The current blueprint was read under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, including `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. This remains a low-level algebraic-group tool on the existing route, with no change to a unit or chapter. No unit realization file is due: this item is not a unit key node.

## Searches and reuse

Read the existing item's four recorded searches and their actual result summaries before retaining them. For the new node, ran and read LeanFinder on smooth connected affine groups of dimension at most two, LeanSearch on connected linear algebraic groups of dimension less than three, Loogle on `"IsSolvable"`, a whole-Mathlib grep for solvability alongside finrank/dimension/Krull, and an AlgebraicGeometry grep for `solvab|Borel`. Both semantic phrasings return abstract group solvability, not this geometric theorem; Loogle returns Lie-algebra solvability; the dimension grep returns Cartan-criterion comments; the AlgebraicGeometry grep has zero hits. All services answered, and each recorded query and result digest is copied from searches.jsonl. The relevant abstract/linear algebra hits cannot specialize in one line to Krull dimension or algebraic-group-scheme solvability.

Searched the whole DAG by statements and titles, the source place 17.27, and the concepts solvable, small dimension and group smoothness; ran blueprint_refs searches for `solvable`, `reduced smooth`, `dimension two`, `small dimension`, `dimension at most`, and `17.27`. No existing blueprint node states the new theorem. `lem-sfb-geometrically-reduced-group-smooth`, `lem-sfb-locally-algebraic-group-identity-component`, `lem-ag-equal-dimension-subgroup`, `lem-wf-affine-dimension-drop`, the central-maximal-torus nilpotence theorem and the existing solvable/unipotent structure nodes were opened before choosing the split. In particular the Q_lbar-only equal-dimension theorem does not apply in arbitrary characteristic; the new node is not an elementary dimension calculation.

## Not duplicates

lem-sfb-connected-group-dimension-two-solvable vs lem-sfb-pgl2-proper-connected-subgroup-solvable: the former is the independent general small-dimension theorem; the item additionally establishes smoothness from reducedness and a dimension bound from a proper embedding into PGL2. Neither geometric reduction has been moved into the new node.

lem-sfb-connected-group-dimension-two-solvable vs lem-sfb-central-maximal-torus-nilpotent: the latter requires a central maximal torus and concludes nilpotence; the new node has a dimension bound and includes nonnilpotent solvable groups such as the upper triangular subgroup of PGL2.

lem-sfb-connected-group-dimension-two-solvable vs lem-sfb-smooth-unipotent-solvable: the latter assumes unipotence; the new node allows tori and the nonunipotent two-dimensional affine group.

## Review by Q08

I read Milne, Algebraic Groups, iAG2017, Proposition 1.26 on printed p.13, the Section 17b standing hypotheses on p.353, Corollary 17.27 and its proof on p.360, and Theorem 20.16(c) implies (d) on p.413. Corollary 17.27 assumes a connected group variety over an algebraically closed field, and the book's algebraic groups are affine; Proposition 1.26 identifies group varieties with smooth algebraic groups. Those are exactly the new node's hypotheses, without a characteristic-zero assumption. I also read Proposition 6.30 on p.132 and the preceding derived-series paragraph, which expressly give the scheme-theoretic derived-series formulation of solvability. Thus the new node has the same notion of solvability as the item, not merely a claim about rational points. Its proof and proof-dependency lists are empty, and its statement includes no proof sketch.

For step 1 I opened `lem-sfb-locally-algebraic-group-identity-component` and `def-weil-pbc-scheme-reduction`. The former actually says that the reduced identity component is smooth and integral over an algebraically closed field, with the same underlying topological space. It is stronger than a statement about identity-component existence alone. Connectedness makes the supplied open component all of I, and reducedness makes its nilradical zero, so the reduction definition identifies that component with I as a scheme. This proves the smoothness conclusion with exactly the hypotheses available. The Stacks source was checked at Tag 0B7R, `proposition-connected-component`, and at the reduction/smoothness tags 047R, 047P, 047N listed by the existing node; Milne Proposition 1.26 is the direct reduced-group smoothness source.

For step 2 I opened `lem-sfb-projective-matrix-central-cover`: its statement explicitly gives affineness, smoothness, geometric connectedness and dimension r^2-1, so r=2 gives exactly three. I opened the identity-component statement again: its geometrical irreducibility clause gives irreducibility of connected P. I opened `sbc-lem-smooth-geometrically-reduced`, whose statement really gives geometrically reduced fibres, and read the corresponding project Lean declaration at Geometrically/Reduced.lean:66–74; applying it to P over the field gives reducedness. The definition `def-pc-integral-scheme` includes the equivalence with nonempty, reduced and irreducible; nonemptiness here is furnished by the identity. I read the affine-quotient-ring clause of `def-weil-closed-immersion`, which does identify I with Spec(A/J) for affine P=Spec A. I corrected my first draft of this support argument: instead of implicitly invoking the theorem that the nilradical is the intersection of all primes, the final proof uses that A is a domain, so the prime (0) belongs to Spec A and V(J)=Spec A would force J=0. This is the elementary argument showing that the proper scheme inclusion has proper support; properness here never means a proper morphism. Finally `def-kun-topological-krull-dimension` defines dimension by lengths of chains. Every such chain in the closed subspace |I| is closed in |P|, and adjoining |P| increases the length strictly. The three-dimensional ambient bound therefore gives dimension at most two with no unstated catenarity, equidimensionality or tangent-space result. I verified the precise source labels for Stacks 056T (`lemma-smooth-geometrically-normal`) and 01QO (`lemma-closed-immersion`).

For step 3 I read the new node's complete statement after writing it. Affineness, finite type and connectedness of I are hypotheses of the unchanged item; smoothness is step 1 and the dimension bound is step 2. The field is algebraically closed. Thus every hypothesis of the new theorem is checked before its use. The conclusion is exactly termination of the scheme-theoretic commutator series. Every cited node has a verbatim quotation in citations.json; no step uses another node's proof instead of its statement.

I checked delivery-errors B–E against the finished files: no new definition, no hollow data, no proof in the statement-only leaf, no invented search, no missing external lemma disguised as an elementary claim, and no theorem about Lie algebras standing in for one about groups. The elementary support and dimension-chain arguments remain explicit parts of the item; they have not become unnecessary nodes. All three steps are shorter than 2000 characters. The only cross-unit statement tool, smoothness implying geometrically reduced fibres, is declared in split_report.tool_uses; it is a general geometric property, not a replacement for the unit route. No SGA source is used.

Small-case tests: the trivial subgroup is nonempty, smooth and solvable, with dimension zero; G_a, G_m and a two-dimensional split torus meet the new theorem; the two-dimensional upper triangular subgroup of PGL2 is solvable but need not be nilpotent, which is why the new statement claims solvability only. In characteristic two the ambient PGL2 and a reduced connected subgroup still satisfy the argument: no invertibility of 2 or Lie-algebra classification enters. PGL2 itself has dimension three and is excluded by proper inclusion. Disconnected finite nonsolvable groups, and nonreduced infinitesimal examples such as alpha_p, are excluded by the hypotheses that the argument actually uses. I found no statement dispute.

## Unfinished work

Only the new general Corollary 17.27 prerequisite remains unsplit, as required for a one-level delivery. The item has a complete assembly proof. Dry-run and push results will be recorded after execution.
