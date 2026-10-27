1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-invariant-power-exact-sequences.json: item, statement unchanged, four-step split, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-kernel-invariants-quotient-action.json: one new statement-only lemma, unsplit, no Mathlib match.
- citations.json: verbatim statement excerpts for every cited node in every proof step. searches.jsonl and the two search-results JSON files retain the actual search calls and output. run_searches.py and write_split.py are sandbox-only preparation scripts.

2. Attachments

None. Searched lean/WeilConjectures for the item id, invariant-power names, invariant exact sequences, normal-kernel and quotient-action language. No declaration supplies the whole item. The existing symmetric-algebra grading is already attached to its own node and is reused, not delivered.

3. WANTED: literature/alper-adequate-moduli-spaces.pdf, Lemma 9.2.5(2),(5), printed pp.522-523, and Proposition 9.5.1, printed p.525, for the item and lem-sfb-normal-kernel-invariants-quotient-action. Local file absent. Read the journal PDF at https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf in the browser; did not download it or write literature/.

4. Errors or omissions corrected

The item was unsplit, not an earlier failed delivery. No statement dispute: its arbitrary-module criterion is exactly Lemma 9.2.5(5), whose equivalence does not require a Noetherian base or a resolution property. Finite free modules occur only in later, stronger-hypothesis versions of that lemma. The source proves the quotient/extension result using classifying stacks; the delivery gives a direct rational-module proof, marked proof_origin.by = agent, and isolates the quotient descent input rather than pretending ordinary-group invariant lemmas provide rational group-scheme descent. The single new node contains neither a power-lifting property nor any part of the item's conclusion.

Read the recorded chapter and unit and the latest blueprint unit and direct-image proof. The DAG unit record is older than the latest blueprint text; the item is a deep supporting prerequisite of its inherited direct-image alteration chain, not the unit's key node. blueprint_refs.py ancestor reports None. Retained its inherited null ancestor and via list and added the item to the new node's via list. No unit or chapter change. Whole-blueprint searches for invariants, coaction, normal subgroup, quotient representation, symmetric power and geometrically reductive found no equivalent blueprint statement.

5. Unfinished work

The new quotient-action lemma is deliberately statement-only for a later stage-1 item. Its proof would form the kernel equalizer, use flatness of coordinate algebras to commute that equalizer with flat base change, restrict the H-action by normality, and descend the resulting action through the faithfully flat torsor H to Q. Equality of inflated coaction maps is reflected by faithfully flat tensoring. This is a genuine descent theorem, not a few-line manipulation of the item's hypotheses. No Lean was written or compiled.

## Not duplicates

lem-sfb-normal-kernel-invariants-quotient-action vs lem-sfb-rational-fixed-space-base-change: the existing node assumes a field and finite-dimensional rational representations, and gives H-stability and base change of fixed vectors; the new node works over any ring with arbitrary modules and supplies descent to a specified fppf quotient Q, plus inflation detection. It is not a specialization of the existing statement.

lem-sfb-normal-kernel-invariants-quotient-action vs lem-sfb-flat-coalgebra-subcomodule-core: the existing node constructs the largest subcomodule inside a submodule for a flat coalgebra, without a quotient group or descent; it neither states normal-kernel invariants are stable nor gives their quotient coaction.

lem-sfb-normal-kernel-invariants-quotient-action vs lem-sfb-affine-torsor-algebra-invariants: the existing node treats algebras already pulled back along a torsor and identifies sections with invariant rings; the new node treats arbitrary representation modules and constructs a quotient representation. It does not assume the module already descends.

lem-sfb-normal-kernel-invariants-quotient-action vs lem-sfb-quotient-stack-invariant-base-change: that statement identifies a 2-cartesian stack square, with no assertion on rational modules or invariant submodules.

lem-sfb-normal-kernel-invariants-quotient-action vs lem-sfb-normal-inflation-resolution-naturality: that statement concerns condensed modules for profinite groups with open normal kernels, not rational comodules for affine group schemes.

lem-sfb-normal-kernel-invariants-quotient-action vs lem-sfb-normal-quotient-tower-resolution-coherence: that statement concerns derived condensed invariants and open kernels in profinite quotient towers; it cannot supply an algebraic rational Q-coaction.

lem-sfb-normal-kernel-invariants-quotient-action vs lem-sfb-normal-tensor-invariant-powers: that statement is about powers of field-tensor invariants for an automorphism group, with neither group schemes nor modules descending along an fppf quotient.

lem-sfb-normal-kernel-invariants-quotient-action vs lem-sfb-coideal-coinvariant-projection: that statement assumes a field and a split coideal inclusion and constructs a projection for relative Hopf modules; it does not give arbitrary-ring normal-kernel quotient descent.

## Review by Q41

I read Alper's Lemma 9.2.5 and Proposition 9.5.1 in the journal PDF. The former explicitly quantifies over all module surjections to the trivial base ring; neither Noetherianity nor local freeness belongs to that clause. The latter treats flat finitely presented separated group algebraic spaces and gives both implications claimed here. Affine group schemes satisfy its separatedness requirement. Its proof's fully faithful quotient pullback and normal-kernel direct image motivate the new statement; I read that proof and kept the substantive arbitrary-module descent as a new lemma, rather than citing the proposition itself for a clause of the item. The source statement's classifying-stack apparatus is not imported into the item's statement or proof.

For step 1 I opened the new quotient-action statement: it explicitly equates invariants before and after inflation, which is exactly what is needed to return an H-invariant lift to Q. I opened lem-weil-pbc-symmetric-algebra-universal-property: it explicitly gives the unique algebra extension and equality when generator maps agree. Applying it to the induced coactions verifies that taking symmetric powers commutes with inflation. Inflation changes no underlying module or surjectivity.

Step 2 is simply the assumed property P(A,K) applied to the restriction of the given map; the coaction restriction satisfies its identities by the group homomorphism identities. Its output q lies in precisely the kernel-invariant module used next. There is no assumption that H(A) surjects onto Q(A).

For step 3 the new lemma explicitly supplies a rational Q-action on V^K and restriction of equivariant maps. Apply it to V = Sym^n(M) and the map to the trivial A-module. The invariant submodule of a trivial module is all of A and its descended action is trivial by uniqueness. I checked surjectivity by the actual formula mu(aq) = a, not by exactness of the invariants functor. Applying P(A,Q) is legitimate even if this invariant submodule is not flat or finitely generated.

For step 4 I opened both existing symmetric-algebra node statements: the universal-property node gives F and its uniqueness, and the grading node explicitly gives spanning by products and Sym^n times Sym^m contained in Sym^(n+m). Thus degree m is sent to degree nm. Equivariance is equality of algebra maps checked on generators; the augmentation identity is checked on products x_1 ... x_m and extended linearly. This is an explicit elementary construction from those two cited statements and step 3's equivariant inclusion. No lemma about symmetrization by averaging, factorial division, or injectivity of symmetric powers is used. The new invariant-power element is theta(r), not an unsupported assertion that r itself embeds into Sym^(nm)M. All steps are under 1000 characters; none hides a lemma behind a step longer than 2000 characters.

I tested the new statement and the argument at A = 0, V = 0, K = 1, Q = 1, arbitrary nonflat modules with trivial action, and nonreduced kernels. For A = 0 the zero element maps to 1 = 0 and degree 1 suffices. For nonzero A the zero module cannot surject to A. K = 1 reduces to the original Q-representation; Q = 1 gives all H-invariants with trivial residual action. For the fppf quotient G_m to G_m by p-th powers in characteristic p, the kernel is mu_p; on weight modules the invariant weights are multiples of p and descend by dividing the weight by p. This illustrates why testing only geometric points of the kernel would be wrong and why no smoothness or reducedness may be inserted. The kernel is defined by the coaction equalizer, so the proof does not use that invalid pointwise test.

I checked B1-B10: the one new node is self-contained, introduces its rings/groups/modules/coactions, states all hypotheses, has no proof, and has actual logged searches. Inline coordinate-Hopf maps are defined by the group diagrams; the existing coordinate-Hopf definition is field-only and was not cited for a general base ring. TeX escapes are single after JSON decoding. No Stacks tag is claimed for Alper's theorem. C1-C8: every non-elementary imported fact is the new node's statement, all other constructions use the two opened symmetric-algebra nodes; proof_deps is the union of uses; verbatim excerpts are in citations.json; there is no upward dependency or route change. D1-D5: the new node has no power-lifting conclusion and cannot imply the item on its own; the item carries the two lifting applications and the multiplication. E1-E7: arbitrary modules, nonreduced kernels, positive degrees and the exact augmentation and coaction formulas were checked. The source proof was not silently copied as a citation-only proof. The split is signed as my own review, with maintainer independent review still to follow.

Validation: the first required dry run completed with OK (not pushed), commit 518c6a12d36. Recorded the additional targeted Loogle call already run and read, then reran preflight for the final file set. Every recorded search of the new node matches searches.jsonl.
