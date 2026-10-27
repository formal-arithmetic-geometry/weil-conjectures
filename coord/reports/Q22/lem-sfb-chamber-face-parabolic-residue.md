# Stage-1 delivery: lem-sfb-chamber-face-parabolic-residue

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-chamber-face-parabolic-residue.json: statement item split in four steps; no Mathlib match.
- citations.json: verbatim statement quotations for every proof-step citation.
- searches.jsonl: actual msearch.py queries and results for the item; the original node's earlier searches were retained.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, chamber, parabolic, root-system and expected face-residue names returned no declaration. No upstream sorry declaration was used as a finished proof.

## WANTED

None needed for this split. The source PDF is available locally. Milne does not assert this exact face lemma; the original source already labels it an agent supporting argument, and proof_origin.by remains agent.

## Corrections and completion

The statement is unchanged and is true, including its empty cases. The unsplit item had no argument. The proof now derives the vanishing-root clause directly from the one-sign basis coordinates, and uses a finite-orbit maximum for the chamber clause. No parabolic-stabilizer theorem is assumed, and no clause is moved to a renamed node. The existing rational root-subsystem orbit node is deliberately not used: its objects are rational vector spaces, whereas the present hypotheses are real and already suffice for the direct argument.

The inherited blueprint.from.node is null. Running tools/blueprint_refs.py ancestor on the item confirms None; the inherited place and via are retained. The whole-blueprint searches for chamber and reflection, and the text search in literature/blueprint/latest/blueprint, found no equivalent node. The existing chapter/unit records were read: this is the inherited lower-level supporting root-geometry obligation, not the unit's key node, so no unit fields were changed.

Nothing remains unfinished in the one-level split. The chamber theorem it cites is already an existing split node, not claimed to be a Lean-finished result.

## Review by Q22

I read Milne, Algebraic Groups, Appendix C in the local PDF, printed pp.608--612 (PDF pages 620--624): C.8 gives the orthogonal-reflection formula; the paragraph before C.9 defines bases and chambers; C.9 and C.10 give the chamber/base correspondence and simple transitivity; C.15 explains faithfulness of the action on the spanning finite root set and hence finiteness; C.19--C.22 relate this to the invariant-real-form formulation. I also opened the complete statement and proof of lem-sfb-root-chamber-simple-transitivity and the statement of def-weil-vector-space-dimension. There are no new-node sources to check. No Stacks tag states this root-arrangement result and no SGA route is used.

Step 1 cites only def-weil-vector-space-dimension for the equality of dimension and basis cardinality. Its statement explicitly defines dimension that way. All coefficients outside J have one sign, and all corresponding q-pairings are strictly positive, so the sum is zero precisely when all those coefficients vanish. This proves both inclusions of the zero-root equality without appealing to an uncited subsystem theorem. Since J consists of roots vanishing at q, the equality of spans and dimension follow. The one-sign hypothesis is essential and is present.

Step 2 is the explicit reflection calculation: the involution is orthogonal, acts by a permutation of R, and a linear map fixing the spanning set R is the identity. Thus W_R embeds into the finite permutation group of R, W_J is finite, and its generators fix q by the actual face hypothesis. Each v in W_J therefore preserves the norm-distance to q. The same formula proves preservation of regular points. This is elementary finite linear algebra, not a citation to a definition as a substitute for a theorem.

Step 3 cites lem-sfb-root-chamber-simple-transitivity for precisely its stated conclusion that the given simple-root cone is a nonempty chamber and the reflection group acts on chambers. Its real-vector-space, positive-definite, reduced, crystallographic, spanning and same-sign-base hypotheses match each hypothesis of this item. I did not take anything from its internal proof. For h in C the points q+t h have all simple pairings positive for every t>0; their limit is q. Applying a homeomorphism fixing q proves the closure condition for every vC. This supplies the easy inclusion explicitly.

Step 4 cites that same node only for its chamber action. It does not assume the theorem about a point stabilizer or any unproved parabolic presentation. The finite family of strict inequalities outside J remains positive in some ball centered at q, and q in the closure of B ensures that B meets the ball. Maximize (v y,h) over the finite W_J orbit. A negative simple pairing in J would increase the functional under its generator; equality to zero is excluded because y, hence v y, is regular. The generators are orthogonal and fix q, so maximization cannot leave the chosen ball. Consequently all remaining pairings are positive too. Two components meeting at v y are equal, giving B=v^{-1}C. This is one routine finite maximization argument (1178 characters), with no hidden sublemma or comparison. Every step is below 2000 characters.

I tested the boundary cases explicitly. If J is empty, W_J is trivial and q is interior to C; the chosen ball lies in C, so the only incident chamber is C and no root vanishes. If J=D, spanning gives q=0, every chamber is incident and the maximum argument reduces to the usual full reflection-orbit argument. In rank one R={a,-a}, q with positive pairing has just the positive ray incident; q=0 has the two rays incident, interchanged by s_a. In rank zero, R=D=J is empty and E={0}; the unique chamber is {0}, its closure contains q=0, and dimension is zero. For reducible systems the proof uses only spanning and positivity, with no irreducibility assumption. The assertion would fail without the strict inequalities outside J, but these are exactly the supplied hypotheses, so no statement dispute is needed.

I checked delivery-errors B--E point by point: no new unsplit statements or duplicate nodes, no unintroduced root-theoretic notion (the item defines all of them inline), single-escaped TeX after JSON decoding, exact sources, actual logged searches, no proof-only citation or extra hypothesis, no circular dependency, no relabelled clause, and explicit topology and reflection calculations in the two inclusions. The dimension node is a Mathlib leaf; the chamber node belongs to this same unit and has no dependency on the present item. citations.json quotes the actual statement text for each citation.

The Mathlib searches used leanfinder with both the chamber-orbit and point-stabilizer formulations, leansearch with the closure-of-chamber formulation, Loogle with CoxeterSystem, Subgroup, and grep in both LinearAlgebra/RootSystem and GroupTheory/Coxeter. Both source greps found no chamber/parabolic/stabilizer result. I read CoxeterSystem.subgroup_closure_range_simple in Mathlib/GroupTheory/Coxeter/Basic.lean:241, RootPairing.Base.induction_reflect in Mathlib/LinearAlgebra/RootSystem/Base.lean:665, and RootPairing.weylGroup_apply_root in Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean:197. These assert generation, reflection induction and preservation of roots; none identifies the chamber orbit at a face. All service requests succeeded. The original item's earlier search records were preserved, and the new queries have their exact msearch log records attached.
