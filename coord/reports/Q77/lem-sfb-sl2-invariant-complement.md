## Worker report

Item: lem-sfb-sl2-invariant-complement. Group Q77. Stage 1 only, 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-sl2-invariant-complement.json: existing statement split into six steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-lie-hyperplane-criterion.json: one new statement-only lemma, unsplit, no Mathlib match. It is a conditional reduction for representations of an arbitrary perfect Lie algebra, with no assertion that the required simple-hyperplane splittings exist.
- citations.json: one verbatim statement quote for each step/node citation.
- searches.jsonl: actual msearch execution records; new-node records reproduce those tool/query texts and their returned summaries.

There are no new Mathlib leaves and no Lean files. Only the designated sandbox was written; no compiler, Lake, repository git command, or local preflight was run.

## Attachments

None. Searches in lean/WeilConjectures by the exact item id and by Casimir, Weyl reducibility, invariant complement, and sl2 found no declaration proving the item. The upstream Semisimple/Lemmas.lean file defines a semisimplicity predicate and derives consequences assuming it; it does not prove Weyl's theorem. The parent polynomial-model node uses this item and is not a possible dependency.

## WANTED

None. The source needed for the construction is present as literature/milne-algebraic-groups_iAG2017.pdf. No SGA source is used. There is no appropriate Stacks tag for this Lie-theoretic criterion; the actual book and numbered places are cited.

## Source and statement audit

Read Milne, Theorem 23.70(a), printed p.507 (PDF p.519), which invokes Weyl's theorem rather than proving it. Read the actual Casimir construction in section 22c, p.475, Lemma 22.40 and its two reductions, pp.476-477, and Proposition 22.41, p.477 (PDF pp.487-489). The construction is adapted to Lie modules over Q: no claim that the algebraic-group statements apply directly is made. In particular the book's scalar Schur-lemma step is replaced by injectivity on a simple rational module, proved from a nonzero trace. Thus no scalar extension, group integration, nilpotence, diagonalizability, or faithfulness of the given triple is assumed.

The original statement is correct and unchanged. Its existing source place only invokes a black box; the split now gives the rank-one Weyl argument. The proof is marked agent-written because the Lie-module adaptation and rational-field replacement are ours, although their route follows Milne pp.475-477. No unit or chapter route is changed.

The new node is explicitly an agent adaptation of Lemma 22.40, not a quotation of an identical Lie-module theorem. It introduces k, L, all representations and all invariant subspaces, and states both its universal antecedent and universal conclusion. The definition node def-wf-lie-algebra defines the bracket, perfectness, representations, invariance, and simplicity exactly as used. Finite dimensionality is supplied by def-weil-finite-dimensional-subspace. Direct sum is defined inline. It is valid over every field, including positive characteristic: this formal reduction only uses finite dimensions, the Hom action, and that a perfect Lie algebra acts trivially on a line. There is no appeal to Weyl's theorem in this dependency.

## Argument checked for the new dependency

This is justification in the report only; the new unsplit node itself has an empty proof and proof_deps.

First induct strongly on dim M to extend the simple-hyperplane antecedent to every invariant hyperplane W. If W=0 take M. If W is simple use the antecedent. Otherwise choose a nonzero proper invariant T in W of maximal dimension; then W/T is simple. The antecedent splits W/T in M/T. If Dbar is its complementary invariant line, its inverse image P in M satisfies P intersect W=T and dim P=dim T+1<dim M. Induction splits the hyperplane T in P as P=T direct-sum D. Then D intersect W=0 and dimensions give M=W direct-sum D. This works over any field; no eigenvector or irreducible classification is used.

For a general invariant subspace U of V, the cases U=0 and U=V are immediate. Otherwise give Hom_k(V,U) the Lie action (x.f)(v)=rho_U(x)f(v)-f(rho_V(x)v). Expanding two actions cancels the cross terms and gives [x,y].f=x.(y.f)-y.(x.f), so this is indeed a Lie representation. Let H1 consist of maps with f restricted to U=a id_U, and H0 of maps vanishing on U. Their stability follows by evaluating the displayed action on u in U: if f|U=a id, then (x.f)|U=0. Basis extension supplies a linear retraction V to U, so H1/H0 is a line. Apply the hyperplane result to get an invariant line D in H1 complementary to H0. Since L is perfect, the action of L on D is zero: all commutators act by commutators of scalars, hence by zero. A nonzero f in D is therefore equivariant; its restriction to U is a id_U with a nonzero, because D intersects H0 trivially. Then a^{-1}f is an invariant retraction and its kernel complements U. This verifies the new statement independently of the sl2 Casimir computation.

## Searches and blueprint provenance

Before creating the new node, searched the whole DAG for Casimir, Whitehead, sl2, highest-weight and semisimple Lie terminology; then for hyperplane, codimension-one and the source Lemma 22.40. Opened the existing group criterion, group Casimir-trace lemma, faithful semisimple trace-form lemma, Cartan trace criterion, module socle complement lemma, rational polynomial model, primitive-string lemma, and all cited definition/trace statements. The socle lemma assumes a sum of simple modules, which has not been established here. Group-level results require an action by a group scheme, absent from the item. The faithful Lie trace-form lemma is the exact general-field result needed and is reused.

Ran tools/blueprint_refs.py search on Casimir, invariant complement, complete reducibility, hyperplane, Lie algebra and perfect. The broad last two searches returned definition and unrelated perfect-complex statements; none states the new conditional Lie criterion. The two hyperplane matches concern geometric hyperplanes. Ancestor lookup returns None for this created-node chain. Retained the item's inherited null blueprint.from.node and entire via list, and set the new node's via to the item followed by that list; both same_as fields are empty, with exact role in the inherited proof location explained. Read the current latest chapter and sk-thm-sf-ctf-stability unit, including its direct-images proof (3); read the recorded DAG chapter/unit too. This is the existing Weyl prerequisite under the inherited alteration/moduli chain, not an alternative route to the unit.

For the item ran leanfinder, loogle, grep and leansearch, including a second wording of the operator problem. For the new criterion ran the same four kinds, with a second semantic wording about splitting extensions by irreducibles. Read all hits. Loogle's LieSubmodule.isCompl_toSubmodule only translates the complement predicate. The Fitting decomposition assumes a nilpotent acting Lie algebra and specifies its zero weight/Fitting summands, rather than a complement to every submodule. InvariantForm.orthogonal_isCompl applies to atomic adjoint ideals with an invariant nondegenerate form, not arbitrary modules or the universal hyperplane implication. Semisimple definitions and irreducibility constructors do not prove the implication either. Read the indicated source sections Submodule.lean:450-461, Weights/Basic.lean:580-610, Semisimple/Defs.lean:55-115 and InvariantForm.lean:130-155. No search was unavailable, and none is recorded as a match. Historical item searches were retained.

## Not duplicates

lem-sfb-perfect-lie-hyperplane-criterion vs lem-sfb-simple-hyperplane-splitting-criterion: the existing lemma is for rational representations of an affine finite-type algebraic group over an algebraically closed characteristic-zero field with no group-scheme characters; the new lemma concerns linear Lie representations over any field and uses perfectness. Neither an algebraic group action nor an equivalence with Lie representations is available; importing or constructing one would require the integration theorem whose proof uses this Weyl input.

lem-sfb-perfect-lie-hyperplane-criterion vs lem-sfb-sl2-invariant-complement: the new conditional criterion does not assert its antecedent for sl2 or for any other Lie algebra. The item's steps prove that antecedent using simplicity, faithful trace-form nondegeneracy, and an explicit Casimir retraction. It is a formal reduction, not a restatement of the desired unconditional theorem or one of its stability clauses.

lem-sfb-perfect-lie-hyperplane-criterion vs lem-sfb-module-socle-complements: the latter assumes that one module is the sum of its simple submodules and is a Mathlib lattice lemma. The new lemma starts with splittings only for simple codimension-one submodules across representations of a fixed perfect Lie algebra; it supplies the missing reduction by induction and Hom.

## Review by Q77

I reread the source pages and all six proof steps with their cited statements open. Step 1 uses def-wf-lie-algebra for the matrix commutator example, ideals, perfectness and derived series, and def-wf-semisimple-lie-algebra only for the definition by absence of solvable ideals. The three brackets are direct matrix multiplications. The displayed polynomials in ad h really project onto the eigenvalues 2,-2,0: on the basis e,f,h they have diagonal entries (1,0,0), (0,1,0), (0,0,1). An ideal is preserved by these polynomials, and bracketing any recovered basis vector gives all three. Perfectness excludes solvability of L. This is an explicit three-dimensional computation, not an uncited structure theorem.

Step 2 uses exactly the new criterion's implication. The three identities define a representation by bilinearity, with no requirement that the operators be independent; invariance is equivalent because the matrices e,f,h span L. The criterion's perfectness hypothesis was proved in step 1. Its antecedent ranges over all representations M, so steps 3-6 check it for an arbitrary M and simple invariant hyperplane W, not just the original V.

Step 3 cites lem-sfb-faithful-semisimple-trace-form. Its statement really supplies nondegeneracy for an injective representation over ANY characteristic-zero field, not just an algebraically closed field, and both required spaces are finite-dimensional. The action r on M may initially be zero; that branch is handled by basis extension. Otherwise ker r is a proper ideal, so the elementary simplicity calculation gives injectivity. Only in this latter branch is the trace-form theorem applied. The dual basis is formed by an invertible Gram matrix, so the Casimir is an actual rational operator.

Step 4 quotes lem-pc-finite-dimensional-trace-cyclic for trace cycling and def-weil-endomorphism-trace for the diagonal-sum trace. Their statements give exactly these operations. Expanding the brackets proves invariance of B, pairing with the basis proves the minus-transpose formula for the dual basis, and exchanging the two finite indices proves commutation of c. The trace is the sum of three dual-basis pairings, hence 3. There is no appeal to the group Casimir node, which would be inapplicable here. Cyclic trace is a generic tool from another unit, a Mathlib leaf, and is declared as such in split_report.tool_uses.

Step 5 proves that the quotient action is zero directly: scalar endomorphisms commute and L is perfect. Thus every r(x), and then c, sends M into W. A basis adapted to W gives diagonal blocks c|W and zero, so the already computed trace 3 is the trace on W. The invariant kernel of the nonzero endomorphism c|W cannot be W and must be zero by simplicity; finite-dimensional rank gives invertibility. The correction made during drafting was to avoid the source's algebraically closed scalar Schur argument, which does not justify a scalar over Q. No non-elementary fact is concealed here: the kernel argument and full-rank matrix inverse are written out.

Step 6 explicitly checks equivariance of a^{-1}, the retraction identity, existence of both components m=p(m)+(m-p(m)), and zero intersection. It invokes the new criterion again only after the universal antecedent has been proved. This gives the complement to the original U and therefore each of E-, F-, H-stability, rather than only a sum decomposition into unspecified modules.

I tested the item on V=0, U=0, U=V and zero action, which are all addressed explicitly. A nontrivial representation of the abstract L is necessarily faithful by the ideal calculation; a zero or nonfaithful original triple is therefore harmless. The standard two-dimensional representation has nondegenerate trace form and its usual Casimir has nonzero rational trace; adjoining a trivial line gives the hyperplane split covered here. I checked the new criterion when L=0 (all subspaces invariant and ordinary complements exist), M=0, a one-dimensional trivial M (the only hyperplane is W=0, handled outside the simple case), and a nonsimple W with a chosen maximal proper T (the inductive P has strictly smaller dimension). Its formal proof above works also in characteristics 2 and 3; the sl2-specific divisions and trace 3 occur only in the item's Q-proof.

Against B-E: the new node has only a statement, every object and notion is introduced or linked to its actual definition, TeX uses one layer of escapes, source places are precise, and Mathlib queries really ran. Existing source/keyword matches were opened and distinguished above. No new node asserts a clause of the item; its antecedent carries real content proved in the item's own steps. Every cited node has a verbatim quotation in citations.json, and no step uses the internal proof of another node. No parent depending on this item is cited; in particular the rational polynomial model and integration lemmas cannot create a cycle. All steps are under 2000 characters. The Casimir step is a single finite-matrix computation, while the substantial general induction/Hom reduction is exposed as the new lemma. I found no statement dispute and made no statement change.

## Unfinished work

Only the new statement-only criterion remains an unsplit DAG obligation, as required by a one-level split. No other missing argument is asserted as proved. Delivery validation and the push are performed with the authorized delivery tool.
