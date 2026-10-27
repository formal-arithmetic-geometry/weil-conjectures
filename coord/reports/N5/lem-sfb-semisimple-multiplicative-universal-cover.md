# Stage-1 delivery: lem-sfb-semisimple-multiplicative-universal-cover

## Files written

The item is split with six proof steps. Its statement is unchanged. All node files are under `dag/nodes/sec-six-functors-basics/`.

- lem-sfb-picard-trivial-multiplicative-cover: statement, unsplit; no Mathlib match.
- lem-sfb-character-picard-isogeny-sequence: statement, unsplit; no Mathlib match.
- lem-sfb-connected-group-characters-torsion-free: statement, unsplit; no Mathlib match.
- lem-sfb-semisimple-characters-trivial: statement, unsplit; no Mathlib match.
- lem-sfb-semisimple-isogeny-invariance: statement, unsplit; no Mathlib match.
- lem-sfb-semisimple-central-isogeny-multiplicative: statement, unsplit; no Mathlib match.

`citations.json` records a verbatim statement for every citation in every proof step. The search output files preserve actual answers and `searches.jsonl` preserves the launcher's records. Six new nodes, zero new Mathlib leaves. The existing group-like-element classification and fpqc descent nodes are Mathlib leaves.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the item id and by semisimple, isogeny, simply connected, multiplicative type, and Picard/character combinations. The geometric-constituent and monodromy declarations concern semisimple representations and characteristic-zero matrix groups; abelian-variety isogenies do not prove this affine algebraic-group result. Searched `lean/Sheaf/` for the possible supporting declarations too; no exact attachment.

## Literature wanted

None. Read the local Milne *Algebraic Groups* PDF, printed pp.387--393, 400--401, 440; the diagonalizable group calculations on pp.231--234, the rigidity argument on pp.243--245, and the homomorphism discussion on pp.110--111 and pp.74--75. Read Stacks `descent.tex`, Tag 02L4, label `lemma-descending-property-isomorphism`, lines 5915ff. No SGA route is used.

## Corrections and source verification

The item itself is mathematically correct, including the trivial group and positive characteristic. Its imported statement and source are retained. The imported proof was empty. The split spells out the character argument of Milne Theorem 18.25 rather than renaming the universal-cover existence assertion as a child.

Milne Lemma 19.14 on printed p.400 says exactly that semisimplicity of the target implies semisimplicity of its smooth connected finite covering group. I checked the rendered PDF page as well as the extracted text: pdftotext misplaces the prime in the displayed arrow, so the rendered page is decisive. There is no source error or statement dispute. The new node states only this direction, as needed. Its proof uses the image of a smooth connected solvable normal subgroup in the semisimple target, which is trivial; the subgroup is then finite and smooth connected, hence trivial over F.

No silent assumption of an etale kernel is made. A kernel such as mu_p in characteristic p is retained with its full coordinate algebra. The finite character group is computed from the basis of F[M], not from the possibly trivial set of F-points.

## Blueprint and route

Read the item's chapter record and unit record, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`. The item is a deep supporting algebraic-group prerequisite already introduced in the direct-image finiteness route through Haboush and stable-curve moduli. It is not the unit's key node. The inherited unit record has older chapter metadata; neither record is edited. The latest blueprint has no file for this created item or its proposed child statements.

Ran `tools/blueprint_refs.py ancestor` for the item: its output is `None`. Preserve the inherited null blueprint ancestor and its entire via chain; append the precise Milne proof place to each child's `from.place`. This reports the broken ancestral chain faithfully rather than inventing a blueprint identity. Whole-blueprint searches were run for universal covering, multiplicative isogeny, semisimple, Picard group, character group, simply connected, torsion-free characters, diagonalizable and central isogeny. All exact matches for the proposed group-scheme facts were absent; `same_as` is empty. Existing Picard nodes about curves or cohomological Picard groups do not supply the character--Picard theorem.

## Not duplicates

- lem-sfb-picard-trivial-multiplicative-cover vs lem-sfb-semisimple-multiplicative-universal-cover: the new statement constructs a cover killing Picard for every smooth connected affine group; it asserts neither semisimplicity nor simple connectedness. These require the item's character argument.
- lem-sfb-character-picard-isogeny-sequence vs lem-sc-pic-restriction-exact: the former is the character--Picard sequence of an arbitrary multiplicative isogeny of affine groups; the latter concerns restriction of line bundles on a curve.
- lem-sfb-connected-group-characters-torsion-free vs lem-sfb-split-torus-hom-matrices: the former allows every smooth connected affine group and concludes torsion-freeness; the latter classifies morphisms between products of G_m. An arbitrary source is not assumed a torus.
- lem-sfb-semisimple-characters-trivial vs lem-ag-closure-semisimple: the former concerns all semisimple affine groups in any characteristic and their one-dimensional characters; the latter concerns semisimplicity of a specified monodromy representation.
- lem-sfb-semisimple-isogeny-invariance vs lem-sfb-central-torus-semisimple-derived-product: the former concerns any finite covering of a semisimple target; the latter constructs the derived subgroup and product decomposition of a group with central torus and semisimple quotient.
- lem-sfb-semisimple-central-isogeny-multiplicative vs lem-sfb-reductive-centre-multiplicative-type: the former gives faithful flatness and diagonalizable finite kernel of a specified central isogeny of semisimple groups; the latter only asserts multiplicative type of a reductive centre, with a different presentation of the notion. The isogeny implication is Milne 19.15's supporting comparison; it is not the universal-cover existence assertion.

The six new nodes use Milne places, not Stacks tags shared with existing nodes. Existing general fpqc isomorphism descent, the group-like basis classification, and multiplicative-isogeny composition were reused instead of duplicated. Searches over the whole DAG for the Milne numbers and for the above notions preceded creation. The nodes `lem-sfb-finite-diagonalizable-character-duality` and `lem-sfb-zero-character-picard-simply-connected` were considered and searched but never created: their arguments belong inline in steps 2 and 4--5.

## Review by N5

I read the item against Milne 18.25 and 18.27 and checked both definitions of simple connectedness using 19.15. Each of the six children is statement-only and introduces its field, groups and additional objects. The smooth, connected, finite-type hypotheses are explicit. Characters and geometric Picard groups are defined inline; the curve-only Picard definition is not misused. The definitions of diagonalizability, faithful flatness and solvability are written where needed.

Step 1 uses the Picard-killing cover node for exactly P and pi with Pic(P)=0, and the isogeny-invariance node for exactly semisimplicity of this smooth connected P. I read Milne 18.22's construction and 19.14's proof, and verified the direction against the rendered PDF to avoid the misplaced prime in text extraction. The cover lemma applies over the algebraically closed field, which is the split situation in Milne's standing convention. No separate splitting assertion is used by the item's proof.

Step 2 uses the existing group-like-basis node, whose statement says precisely that Delta(a)=a tensor a and epsilon(a)=1 are equivalent to a=e^m. The cited affine-spectrum statement supplies the contravariant correspondence of morphisms, and the G_m statement gives its exact coalgebra formulas. Writing t's image gives the character identification directly; multiplication of basis elements gives its group law. This is an elementary calculation from those statements, not a new duality node. For N=D(0) it gives zero characters; for N=mu_p it gives Z/p, even though N(F) can be a singleton.

Step 3 uses the semisimple-characters node only for X*(H)=0, then the character--Picard node at X*(P) and the torsion-free node for P. I checked that the exact sequence is stated for multiplicative isogenies with smooth connected endpoints and finite possibly nonreduced kernel: these are precisely the hypotheses of pi. The finite torsion-free argument is written out. The Mathlib Picard-group search hits at `Submodule.mulExact_unitsToPic_mapAlgebra` (PicardGroup.lean:859) and `mulExact_unitsMap_spanSingleton_unitsToPic` (line 763) were read; they are ring exact sequences, not Milne's sequence with algebraic character groups, so do not furnish a leaf by one-line specialization.

Step 4 tests every surjective central finite cover q:Q->P allowed by the item's definition. Its semisimple-central comparison node gives exactly multiplicativity and faithful flatness; Milne 19.15 and 18.1 supply this fact. The exact-sequence and torsion-free statements apply to the smooth connected Q. The argument proves X*(K)=0 and then K=D(0) using the calculation of step 2. Neither simple connectedness nor a universal cover is assumed in a child. The centre and kernel are scheme-theoretic throughout.

Step 5 proves the kernel-pair isomorphism with explicit mutually inverse formulas, before using the existing fpqc-descent node. I opened its statement: it says an isomorphism after base change along a flat surjective quasi-compact morphism is already an isomorphism. Here h and phi are both q. q is faithfully flat by step 4 and is an affine morphism, hence quasi-compact. The base change is Q times_P Q -> Q, exactly the projection just checked. I also read Stacks 02L4 itself. The node is an existing Mathlib leaf and is additionally declared as a generic tool in split_report; it replaces no unit proof route.

Step 6 uses the existing multiplicative-isogeny-composition statement, which explicitly concludes centrality of the composite kernel. Apply it to pi and the identity of H; both endpoints are smooth connected and both maps satisfy its exact multiplicative-isogeny definition. This avoids an uncited rigidity theorem. With tilde H=P, all existential clauses follow. H=1 is valid, and no positive-dimensional or positive-rank hypothesis was introduced.

I checked B--E point by point: new nodes have no proofs or proof dependencies, statements are self-contained with single TeX escaping, every non-elementary step cites a statement saying exactly what is used, and citations.json copies those statements verbatim. No new node restates universal-cover existence or its simple-connectedness clause. The Picard cover is a genuinely different intermediate construction for all smooth connected affine groups. All Mathlib queries recorded in the new nodes actually ran through msearch.py; the second phrasings and the service responses were read. No matching project declaration exists. All six proof steps are shorter than 2000 characters. The only unresolved work is the future stage-1 splitting of the six statement-only children, as required for a one-level split.

## Unfinished work

No part of this item's one-level split is left unfinished. The six child lemmas are deliberately unsplit. Required dry-run and push results follow from the delivery tool.
