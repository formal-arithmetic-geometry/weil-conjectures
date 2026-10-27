# Q63: lem-sfb-character-picard-isogeny-sequence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-character-picard-isogeny-sequence.json: item, split into five proof steps; original statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-borel-characteristic-picard-sequence.json: statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-isogeny-borel-comparison.json: statement-only lemma, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every proof-step citation.
- searches.jsonl and search-results.json: command-produced query log and full results; queries.json/run_searches.py retain the search questions and execution; milne.txt is the local text extraction used to read the source.

## Attachments

None. Searches of lean/WeilConjectures for the item tag, Picard/character combinations, Borel, Rosenlicht, and isogeny found no exact declaration of the item or either new input. The existing Picard descent node is reused without editing it.

## WANTED

None. Milne, Algebraic Groups (2017), is available locally as literature/milne-algebraic-groups_iAG2017.pdf. No SGA source is used.

## Corrections and scope

The item was statement-only. Its statement agrees with Milne Proposition 18.18, sequence (129), printed p.391, specialized to finite multiplicative kernel over an algebraically closed field; there is no statement dispute. I supplied its proof following Milne's diagram. The Borel characteristic exact sequence (Theorem 18.15) and the Borel/flag comparison under the isogeny are supporting facts, rather than copies of any clause of (129): they involve the auxiliary Borel subgroups and flag quotients, and the item's steps perform the diagram chase. The new nodes are deliberately not split themselves.

I retained the existing blueprint ancestry, including its null ancestor and long via chain. tools/blueprint_refs.py ancestor confirms null. The current latest blueprint's constructible-direct-image proof provides the alteration context; this item is a subsequently introduced Milne prerequisite, not a claim that the blueprint itself contains Proposition 18.18. Neither the chapter nor the unit route or bindings is changed.

## Not duplicates

lem-sfb-borel-characteristic-picard-sequence vs lem-sfb-homogeneous-line-bundle-sections: the existing node assumes reductivity and identifies sections with regular semi-invariant functions; it states no characteristic exact sequence and no surjectivity onto Pic(G). The new theorem applies also to nonreductive connected smooth affine groups.

lem-sfb-borel-characteristic-picard-sequence vs lem-sfb-reductive-borel-pair-structure: the existing node is the reductive Borel/root-datum structure theorem and does not state the characteristic/Picard exact sequence. It also cannot supply Borel existence for the present nonreductive groups.

lem-sfb-multiplicative-isogeny-borel-comparison vs lem-sfb-multiplicative-isogeny-composition: composition concerns composite kernels and their centrality, not inverse-image Borel subgroups, identical flag quotients, or restriction-surjectivity for Borel characters.

lem-sfb-multiplicative-isogeny-borel-comparison vs lem-sfb-reductive-borel-pair-structure: the existing node treats one reductive group and does not compare Borels, quotients, or character groups across an isogeny; the new input allows nonreductive groups.

DAG statement/title searches for Borel, characteristic map, isogeny, Rosenlicht, central extensions, and Milne 18.15/18.18 found no existing statement of either new input. Whole-blueprint searches using blueprint_refs.py for Borel, characteristic map, homogeneous line, isogeny, characters and Picard likewise found no equivalent statement. Abelian-variety isogeny nodes concern proper commutative groups, not these affine groups. No Stacks tag is assigned to the new Milne-source nodes, so no same-tag pairs arise.

## Review by Q63

I read Milne printed pp.389-391, including 18.11, 18.14, Theorem 18.15 and Proposition 18.18, and section 18.f on pp.395-396 (Theorem 18.32 and the proof of 18.15). For the first new node the latter explicitly gives the Borel-character form of the characteristic sequence, without requiring reductivity; on p.390 Milne explains why the split condition holds over an algebraically closed field. For the second new node I read the proof and displayed diagram of 18.18: the preimage Borel, identical flag variety and short exact character row are exactly its inputs. I have kept these genuinely non-elementary assertions as a statement-only prerequisite instead of hiding their proof in the item. In particular I did not substitute the existing reductive-only Borel node, and did not assume that a finite diagonalizable kernel is smooth or reduced.

In step 1 I opened both new statements and checked that the first supplies Borel existence and both exact characteristic rows, including the injectivity and surjectivity later used, while the second supplies B1, the flag isomorphism and the entire short exact Borel-character sequence. The hypotheses match: F is algebraically closed, both Gi are smooth connected affine of finite type, f is faithfully flat, and its scheme-theoretic kernel is finite diagonalizable. In step 2 the same statements define the characteristic maps and the actual contracted-bundle relation; precomposition and the explicit substitution beta(f(b)) verify commutativity. The lift formula is independent of the lift because p0 c0 = 0, so it defines a homomorphism on the given character group rather than a newly assumed boundary map.

Step 3 uses the same bundle definitions and the existing sk-thm-picard-descent statement. I read that whole statement: D1 is an effective equivalence of module descent categories which preserves and reflects finite local freeness, so it supplies both existence and uniqueness of the descended line. The explicit frame equation [gn,1]=[g,lambda(n)] determines the sign convention, and (g,h) maps to (g,g^-1 h) on the full fibre product. Faithful flatness is a hypothesis; quasi-compactness follows from affineness and finite type. Thus the descent cover is fpqc, even in inseparable characteristic, and the computation takes place on all F-algebras. This generic descent theorem is recorded in split_report.tool_uses; it supports the Borel proof and replaces no unit-route step. I did not use the sketch proof of that node as an additional lemma.

Steps 4 and 5 use only the two explicitly stated exact rows and the short exact Borel-character row. I checked each invocation: j0,j1 and u are injective; ker(c_i)=im(j_i); ker(p_i)=im(c_i); both p_i are surjective; ker(r)=im(u). In step 4 these give injectivity of v and the image of v as the restriction kernel. In step 5 they give the restriction image as ker(delta), ker(w) as im(delta), and surjectivity of w. Every lift and subtraction is written down. These are elementary abelian-group calculations; there is no unquoted snake-lemma black box. All five steps are below 2000 characters (574, 536, 888, 336, 689 at writing).

For B1 and the two new statements I tested the identity isogeny (r has zero target and both Pic maps agree), tori with power maps (the Borel is the torus, Q is a point and Pic is zero), the trivial group, and a nonreductive group such as G_a (again Q is a point and both character/Pic terms vanish). I also tested SL_p -> PGL_p in characteristic p: the kernel mu_p is not reduced, but X*(mu_p)=Z/p and the Borel-character row is a finite-index lattice inclusion, so the rightmost Borel character map must indeed be surjective scheme-theoretically. The descent frame argument does not replace mu_p by its F-points. In rank one, SL_2 -> PGL_2 gives the familiar inclusion 2Z -> Z of Borel characters and the Picard cokernel Z/2, checking the direction of the flag comparison and the boundary construction.

I checked delivery-errors B-E: new statements introduce every object and define Borel, solvability, characters, Picard classes, torsors and diagonalizability inline or through their definition dependencies; each is statement-only with honest command-logged searches and full source locations. Search hits were read: the closest Mathlib results Submodule.mulExact_unitsToPic_mapAlgebra (Mathlib/RingTheory/PicardGroup.lean:859) and mulExact_unitsMap_spanSingleton_unitsToPic (:763) concern invertible submodules of a ring algebra, not characters of group schemes or Borel quotients; they do not specialize in one line. I also read their definitions and statements in the source. The Loogle searches ran and returned zero hits; the semantic searches ran twice per node with different formulations. Each step citation has a verbatim quotation in citations.json. No new node repeats the item's terms with a renamed conclusion, no proof relies on a node's proof instead of its statement, and no source, hypothesis or coefficient category was silently changed.

## Unfinished work

The two new statement-only nodes remain for subsequent stage-1 workers, as required by a one-level split. Nothing remains unfinished in the item's natural-language proof. No Lean file was written, no compiler/build/Lake command was run, and all writes were confined to this sandbox.
