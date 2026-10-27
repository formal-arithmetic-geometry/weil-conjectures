## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-picard-pullback-kernel.json: existing statement, retained verbatim; five proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-character-pushout.json: new statement-only prerequisite; unsplit, no Mathlib match. Constructs the represented character pushout, its group law, associated line, and specified equivariant frame. It assumes no abelian quotient and asserts no algebraic triviality.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-gm-extension-picard-zero.json: new statement-only prerequisite; unsplit, no Mathlib match. Underlying-line consequence of the classification of commutative extensions of abelian varieties by the multiplicative group.
- citations.json: verbatim statements or the relevant sentence for every proof-step citation. searches.jsonl: actual msearch.py calls. This report and write_split.py are sandbox-only supporting files.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, semiabelian/semiAbelian, Rosenlicht, Picard pullback/kernel, character pushout, contracted products, and Picard extensions. There is no project declaration giving all clauses of the item without sorry. General Picard pullback/base-change declarations do not identify this kernel. No Lean was written and no compiler was run.

## WANTED

None needed to state or assemble this split. The local Milne volume supplies the classification statement; its proofs refer further to Serre 1959, VII section 3. The classification is intentionally a new unsplit node, rather than a claim that its proof has been completed here.

## What was wrong or changed

The imported item was an unsplit agent-extracted consequence of Milne 9.3, not the proposition's verbatim statement. It is mathematically sound. I kept its statement and all statement dependencies, source and blueprint metadata. I supplied the missing character computation and compatible line comparison; mere triviality after a covering is insufficient to descend a trivialization. The quotient convention and frame convention have now been fixed consistently, so no implicit dualization occurs.

The existing torus-torsor line-pullback lemma asserts surjectivity of Picard pullback only; it cannot identify the kernel. The existing character--Picard isogeny sequence assumes affine smooth connected groups and a finite diagonalizable kernel, so cannot be applied to this nonaffine abelian quotient and positive-dimensional torus kernel. The existing algebraically-trivial-line-multiplicativity lemma goes from algebraic triviality to a tensor identity, not from a group extension to algebraic triviality.

The chapter and unit records and current latest blueprint direct-images proof (3) were read. The inherited chain serves the stable-Picard auxiliary in that proof, and no unit route was replaced. blueprint_refs ancestor returns None for this auxiliary; its inherited from.node=null and full from.place/via are retained, with the item prepended to each child's via. Searches of all imported blueprint nodes for Picard kernel, Rosenlicht, Pic0, G_m, torus, pushout character and Picard extension gave no equivalent imported statement. The current latest blueprint was used, not an older snapshot.

## Not duplicates

lem-sfb-split-torus-character-pushout vs lem-sfb-smooth-affine-group-torsor-representability: both source references contain Tag 049C, but the existing statement represents a supplied locally trivial torsor under a smooth affine group. It does not form a character pushout, give the quotient group law or its exact extension, or identify the character-equivariant line frame. The new statement supplies those additional data for a commutative group extension.

lem-sfb-split-torus-character-pushout vs lem-sfb-split-torus-torsor-frame-geometry: the existing result decomposes a torus torsor into coordinate frames and constructs projective-bundle compactifications; it supplies no descended group law or character pushout extension.

lem-sfb-abelian-gm-extension-picard-zero vs lem-sfb-algebraically-trivial-line-multiplicativity: the existing result assumes fibrewise algebraic triviality and gives an uncoherenced tensor isomorphism in a relative setting. The new field statement starts with a specified commutative multiplicative extension and deduces algebraic triviality of its underlying line.

lem-sfb-abelian-gm-extension-picard-zero vs lem-sfb-abelian-polarization-calculus: the existing dual/Poincare and polarization calculus does not identify extension classes with points of the dual, or state algebraic triviality of the underlying torsor of a given extension.

lem-sfb-abelian-gm-extension-picard-zero vs lem-sfb-character-picard-isogeny-sequence: that existing exact sequence is for affine groups with a finite multiplicative-isogeny kernel. The new lemma concerns extensions of a proper abelian variety by the smooth positive-dimensional group G_m and has no such affineness or finite-kernel hypothesis.

## Mathlib searches

Both new nodes have two semantic phrasings, LeanSearch, LeanFinder, Loogle and source grep, run through the required msearch.py command and recorded in searches.jsonl. Every listed search is an actual logged query, with its returned names and a no-match explanation in the node. All these services answered successfully. The item's earlier searches are retained, and fresh item-specific LeanFinder and grep queries were appended.

I read Mathlib/RingTheory/PicardGroup.lean at relPic, line 618: this is the kernel of a map of Picard groups of rings, not a classification of algebraically trivial scheme lines. Ext search hits identify abstract Ext^0 with Hom and have no abelian-variety input. I read Scheme.GrpObjAsOverPullback in Mathlib/AlgebraicGeometry/Pullbacks.lean, line 831: it constructs the group structure on a base change, not on this quotient. GroupExtension section/splitting declarations in Mathlib/GroupTheory/GroupExtension/Defs.lean concern abstract groups and set-theoretic sections, without representability or line modules. Loogle's AddTorsor hits are affine spaces. No hit is an exact match or a one-line specialization.

## Review by Q57

I read the item's source, Milne, Abelian Varieties, I Propositions 9.2 and 9.3 on printed pages 41--42, together with the earlier definition of Pic^0 on pages 35--36 and the Poincare-family discussion on page 37. Proposition 9.3 is the extension classification, not the pullback-kernel assertion itself. Its Pic^0 classes occur in the dual abelian variety's normalized Poincare family (Remark 8.7(c)); this connected smooth parameter space also explains the algebraic-equivalence meaning needed here. Thus the second new node is the underlying-line consequence of that proposition. I have not silently transferred this classification to nonproper semiabelian varieties.

For the first new node I read Stacks groupoids.tex, remark-fun-with-torsors (Tag 049C), and descent.tex, proposition-fpqc-descent-quasi-coherent (Tag 023T). The new statement is explicitly an agent-extracted refinement: one takes the quotient by (g,z)t=(g i(t),chi(t)^(-1)z), with commutative multiplication inherited from the product. Fppf locally on the quotient base this is G_m, so it is an affine represented torsor; its associated rank-one module and frame arise by module descent. The character action makes this quotient multiplication well-defined. The statement includes this construction and sign, rather than using the tag as though it asserted the entire refinement verbatim. I also read Milne, Algebraic Groups, Proposition 12.48, identity (79), printed pages 246--247, for the normalized Rosenlicht formula used in the item's proof.

For step 1 I opened the statements of the torus-smoothness, affine-torsor representability, smooth-flat, fppf-site, fppf-to-fpqc, abelian-variety characterization and semiabelian-power-integrality nodes. They supply respectively smoothness of T; the represented smooth surjective affine covering and action isomorphism; flatness and local finite presentation; the covering criterion; conversion to fpqc; geometric integrality of A; and integrality of G for n=1. The torsor inverse is written on arbitrary test schemes using g^(-1)h, and comes from exactness of the sheaves rather than any unstated geometric quotient theorem. T is finitely presented from its displayed Laurent presentation. A is proper smooth connected by its definition and geometrically connected by the characterization; its commutativity follows fppf locally from that of G, so all hypotheses of the power-integrality statement hold.

For step 2 I opened the Rosenlicht node. It actually gives the normalized identity for prescribed rational basepoints, not merely a factorization up to an unknown scalar. G is integral by step 1; T has a Laurent coordinate domain inside a rational function field. Both schemes are nonempty separated and finite type and have identity points. The ratio of frames is a global regular unit, and u(g,1)=1 removes the G factor and scalar. The action cocycle proves chi is multiplicative as an identity of scheme morphisms. This avoids the false inference that a rational-point identity automatically covers nilpotent test schemes.

Step 3 uses exactly the first new statement: its E_chi, M_chi, and canonical frame are all in that statement. The quotient formula yields [g i(t),1]=[g,chi(t)], so its multiplier is the same chi as the original frame's, not its inverse. Step 4 uses the full-faithful equivalence in the opened fpqc-descent statement. I checked the isomorphism on the two lifts on G x_A G; both multipliers agree. Its inverse is compatible too, so descent produces an isomorphism, not just a morphism or a claim of local equality. Step 5 uses precisely the second new statement, which applies because E_chi is smooth separated commutative finite type and its exact extension and scalar-equivariant frame identification are supplied by step 3. Substitution of N isomorphic to M_chi preserves the equivalence relation on isomorphism classes.

I checked small cases: r=0 gives q an isomorphism and chi trivial; a split extension G=A x T has a section, so only the trivial line can be in the kernel; A=Spec F has trivial Picard group. For a nontrivial G_m extension the associated nontrivial Pic^0 line pulls back trivially, explaining why the conclusion must be algebraic triviality rather than triviality. The first new node includes chi=1, when its quotient is B x G_m, and r=0. The second includes the trivial abelian variety. No characteristic restriction, finite-kernel hypothesis or nonempty torus-rank assumption was introduced. There is no SGA citation. Neither new node is a clause of the item: the first is a construction for arbitrary commutative quotients with no algebraic-equivalence conclusion; the second is a general extension-classification consequence with no q^*N hypothesis. The item's argument between them is explicitly written.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the files: new nodes are statement-only and self-contained, every non-elementary step uses the actual statement it cites, no generic tool replaces the unit route, and all proof steps are below 2000 characters. The important corrections made during self-review were to fix the character quotient sign, to cite torus smoothness rather than treat it as a definition, and to record the full faithful-descent statement verbatim in citations.json instead of reconstructing a quotation.

## Unfinished work

No unresolved gap in the item's assembly. The two new prerequisites remain unsplit intentionally, as required by the one-level stage-1 brief. Their proofs are future DAG work, not Lean proofs claimed here.

## Validation

Server review_split passed during drafting. The required deliver.py --no-push invocation exited successfully: OK (not pushed), commit ccd4aa81432, preflight passed, and a durable dry-run receipt was saved. This includes the server DAG and split checks. All five steps are under 2000 characters (1120, 844, 435, 620, 449); citations.json has all 11 proof-step citations. The push invocation repeats delivery validation.
