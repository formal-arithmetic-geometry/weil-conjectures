# Stage-1 delivery: lem-sfb-relative-dynamic-attracting-subgroup

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-dynamic-attracting-subgroup.json: statement, split; retained its imported fields and searches, added four explicit steps and five searches run by Q36. The only statement edit specifies that the equivariant map is a group homomorphism.
- citations.json: one verbatim statement quotation for each cited node in each proof step.
- report.md: this report. No new nodes and no Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact item id and for attracting/dynamic terminology and group-scheme/unipotent concepts. There is no declaration proving this item; generic group-scheme and unipotent-matrix results do not suffice.

## Literature wanted

WANTED: Brian Conrad, Reductive group schemes, Theorem 4.1.7 and its proof, printed pp.112-114, and Proposition 4.1.10(2), printed p.115, for lem-sfb-relative-dynamic-attracting-subgroup; local file literature/conrad-reductive-group-schemes.pdf. Read the author's PDF online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf. No local copy was found and no literature file was written. The proof_origin is agent: this is an explicit elementary assembly using an existing DAG theorem, checked against Conrad, rather than a claimed local-document proof. The existing theorem carries the structural theorem's unresolved proof obligation.

## Statement dispute and correction

STATEMENT-DISPUTED: “f is equivariant” alone, read as an equivariant morphism of schemes, does not imply the asserted functoriality. Set A=Q and H=H'=G_a with trivial G_m-actions. The orbit is constant, hence U_a=U_a'={0}. The equivariant morphism f(x)=x+1 sends 0 to 1 and does not carry U_a' into U_a. The proof needs exactly f(1)=1; the intended setting is a map of group schemes, so I made “equivariant S-group homomorphism” explicit. This is faithful to the group-theoretic application in the parent root-exponential node. No target statement is edited. All other hypotheses and conclusions are retained, including arbitrary nonflat and successive base change, the disconnected case, and contraction inside U_a.

## Reuse and searches

Read the full statement of the existing lem-sfb-relative-dynamic-subgroups. It already states the more general relative theorem for P_a, U_a, Z_a, including the tangent formula, connected unipotent geometric fibres, coordinate ideals and arbitrary/successive base change. Its hypotheses are precisely the item's, with no connectedness requirement for U_a. It is in the same unit sk-thm-sf-ctf-stability. A traversal of statement and proof dependencies found no path from it back to the item (100 nodes inspected), so using it is acyclic. The existing field-only lem-sfb-gm-action-attracting-subgroup-big-cell cannot replace the relative theorem over arbitrary A; I did not cite it.

Searched all DAG statements/titles for attracting loci, dynamic subgroups, graded smooth algebras, faithful representations and contracting actions. Ran tools/blueprint_refs.py search for attracting, dynamic and graded algebra; none supplies a second blueprint statement of this relative assertion. The ancestor command reports blueprint.from.node=None, as already recorded in the item, so I preserved that inherited provenance and its exact place. Read the current latest blueprint unit and its direct-images proof (3), and the chapter record. This is a supporting algebraic-group prerequisite along that inherited alteration/root-group branch; no unit or chapter route is changed.

All five new Mathlib search queries in the item were actually run using msearch.py, with their results retained verbatim in searches.jsonl and copied into mathlib_searches. LeanFinder was tried with two different phrasings; its hits concern topological proper actions, Galois groups and modular forms. LeanSearch returns IsSmooth and smoothLocus, which have no group-action attracting construction. Loogle returned no GroupScheme/smooth match, and grep found no attractor/attracting/unipotent/cocharacter declaration under AlgebraicGeometry. These are not exact matches or one-line specializations. Historical searches from the live item are retained unchanged.

## Not duplicates

No new nodes were created. The stronger existing lem-sfb-relative-dynamic-subgroups is reused rather than duplicated. Step 2 is a specialization of that existing statement, not a new node restating a clause.

## Review by Q36

I read Conrad's definitions before 4.1.6, the whole statement and proof of 4.1.7 and the functoriality paragraph and 4.1.10(2) online. No forbidden SGA source is used: Conrad's discussion is the source, and the proof here invokes the existing relative DAG theorem rather than any SGA result. There are no new nodes needing independent source review.

Step 1 uses no node: two algebra maps into B[t] agreeing after the injection into B[t,t^-1] agree on every element. Laurent coefficients give this injection over nonreduced rings too, so separatedness or a density argument on ordinary points hides no hypothesis.

Step 2 uses the statement, not the proof, of lem-sfb-relative-dynamic-subgroups. I matched R=A, G=H and the action, checked its smooth/affine/finite-presentation hypotheses, and checked separately its representability sentence, its geometric unipotence and connectedness sentence, its dual-number tangent formula, and its arbitrary and successive base-change sentence. The conditional connectedness hypotheses for P_a and Z_a are not applied to U_a. The citation quotation is taken directly from that statement.

Step 3 uses the same node's explicit coordinate ideal, which its statement really provides. The ideal is homogeneous, negative degrees vanish and every degree-zero function becomes its identity value. Since an automorphism fixes the identity, the counit kills nonzero degrees, so it factors through D and splits A->D; thus D_0=A, not a possibly smaller quotient. Multiplying a homogeneous element of degree n>=0 by s^n respects products. At s=0 the resulting map is the counit, and at s=1 it is the identity. This writes the contraction into U_a itself as a scheme morphism and also proves stability, over every test algebra. These coefficient manipulations are elementary consequences of the cited coordinate formula, not a separate hidden geometric lemma.

Step 4 uses the same node only for the existing subgroup/tangent base-change identifications. The actual functoriality proof is written out: compose an extended orbit with f and use f(1)=1, the hypothesis missing from the imported wording. Composition and restriction to all B-algebras give a natural map between the represented subfunctors. Over an A'-algebra B the extended orbit is literally the same B-morphism before and after changing A to A'. Evaluating on dual numbers and kernels gives the compatibility of induced tangent maps; iterated changes use the same formulas. This needs no flatness, reductivity, geometric connectedness of H, or surjectivity of f. Yoneda here is simply the defining universal property of a represented functor; no stronger representability claim is being smuggled in.

I checked B--E of delivery-errors: no new unsplit node contains a proof; every object is introduced and the existing definition dependencies are retained; no spurious Stacks tag is assigned to a relative algebraic-group theorem; no unlogged search is recorded; every non-elementary step cites the existing theorem; each cited statement was opened, and citations.json quotations are literal substrings. No source-proof internals are used. All four steps are under 800 characters, so there is no long step hiding a lemma. No new node restates a clause or duplicates a Mathlib result.

Small-case checks: the trivial action gives U={1} and no positive tangent weights; G_a with weight +n (n>0, even divisible by the residue characteristic) gives U=G_a with contraction s^n; weight 0 or negative gives U={0}; a finite etale disconnected group with trivial action still gives the identity subgroup. The empty base A=0 is harmless, and all coefficient arguments work over dual-number rings and nonflat quotient changes. The translation counterexample above is why the functoriality wording was corrected.

## Unfinished work

None in this one-level split. The cited existing general relative dynamic-subgroups theorem remains its own stage-1 item; it was not falsely marked finished. Required server validation and delivery are performed with deliver.py and their results are reported by the final delivery command.
