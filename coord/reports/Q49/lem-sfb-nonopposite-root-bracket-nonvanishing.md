# Q49 stage-1 report

Item: lem-sfb-nonopposite-root-bracket-nonvanishing. Date: 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nonopposite-root-bracket-nonvanishing.json — statement, now split; statement unchanged, five proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-sl2-primitive-lowering-string.json — statement, Mathlib leaf; three matching declarations in Mathlib/Algebra/Lie/Sl2.lean, read at lines 170, 186 and 203.
- citations.json — one entry for each step/node citation, checked verbatim against the cited statements.
- report.md — this report. searches.jsonl contains the actual searches made with the required command. prepare.py is sandbox-only preparation code, not a delivery node.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id, nonopposite, rootSpace, root-space and the relevant bracket/primitive-vector names found no project declaration stating the item. No Lean file was written or compiled.

## WANTED

WANTED: J.-P. Serre, Complex Semisimple Lie Algebras, Chapters V–VI, for lem-sfb-nonopposite-root-bracket-nonvanishing, as the human-written account of the characteristic-zero root-space theory assumed by Milne §23h. This is the inherited source request, not an additional black box used in the proof below. The complete agent argument uses the existing rank-one and weight-support nodes and the directly inspected Mathlib formulas.

## Findings and corrections

The item is mathematically correct as stated; no statement dispute or hypothesis change was needed. Its previous proof was empty. Milne §23h explicitly assumes the semisimple Lie-algebra prerequisites rather than proving this general-field assertion. Theorem 23.71 gives nonzero Chevalley constants over the complex field; using it for an arbitrary K-form would require a comparison not supplied by the item. I instead give the local highest-vector argument over K itself, retaining the intended rank-one route and marking proof_origin.by as agent. No existence of a Chevalley basis or scalar descent is asserted or used.

The live item has no lean_audit field and no corresponding project declaration. Its inherited blueprint.from.node is null because the created.item chain ends at the module name Sheaf.SixFunctors.CtfStabilityDirectImages rather than at an imported blueprint id. The required blueprint_refs.py ancestor command prints None. I retained that result and the exact inherited place/via chain, adding the same precise place and the item at the front of the new node's via chain. I read the current latest blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md: paragraph (3) is the inherited direct-image/alteration context. Neither the chapter nor the unit route is changed, and this is not the key node of a unit.

All four kinds of required Mathlib search were run and logged for the new leaf; the two distinct natural-language formulations returned the same primitive-vector API. The item was also searched by two formulations, Loogle and source grep. Its rootSpaceProduct hits construct bracket maps and prove their weight inclusion, not their nonvanishing. GeckConstruction.e_lie_v_ne and f_lie_v_ne, read in GeckConstruction/Basic.lean:351,365, are formulas for its particular constructed operators, not arbitrary Killing Lie algebras. Existing upstream search records are retained alongside the newly logged searches.

## Not duplicates

lem-sfb-sl2-primitive-lowering-string vs lem-sfb-sl2-rational-polynomial-model: the latter classifies finite-dimensional rational modules under global diagonalizability and nilpotency assumptions. The new leaf works over any characteristic-zero field and gives only the three exact formulas for an individual primitive vector; a finite-dimensional K-module need not be finite-dimensional over Q. That rational-field classification cannot be applied here.

lem-sfb-sl2-primitive-lowering-string vs lem-sfb-sl2-highest-orbit-polynomial: the latter concerns rational representations of the algebraic group SL2 over an algebraically closed field of arbitrary characteristic and gives polynomial orbit coefficients. The new leaf concerns only a Lie representation over an arbitrary characteristic-zero field and requires no group integration.

lem-sfb-sl2-primitive-lowering-string vs lem-sfb-sl2-divided-straightening: the latter is an associative-algebra identity in divided powers. It does not state naturality of primitive eigenvalues or nonzero lowering powers in a finite-dimensional module.

lem-sfb-sl2-primitive-lowering-string vs lem-sfb-killing-cartan-rank-one-spaces: the latter constructs the Lie-algebra triple and proves one-dimensional root spaces, but gives no primitive-vector representation formulas.

lem-sfb-sl2-primitive-lowering-string vs lem-sfb-nonopposite-root-bracket-nonvanishing: the leaf has no roots, Cartan subalgebra, Killing form or bracket-nonvanishing conclusion; the item's five steps perform the root-space argument using its much smaller general representation-theoretic formulas.

Whole-DAG searches for HasPrimitiveVectorWith and its matching declaration names found no existing owner. The cyclic Borel-eigenvector node was opened: it treats rational reductive-group modules in arbitrary characteristic, not primitive Lie vectors. Whole-blueprint searches for root space, nonopposite, sl2, primitive, highest weight and lowering found no statement of the new leaf or the item. No Stacks tag is attached to these Lie-theoretic statements, so no same-Stacks-tag duplicate pair arises.

## Review by Q49

I read Milne's Section 23h at printed pp.503–504 and the Chevalley-basis discussion and Theorem 23.71 at printed pp.508–509. They establish the intended context and explain why the general-field local argument should not silently start with a chosen complex Chevalley basis. For the only new node I read the actual installed Mathlib definitions IsSl2Triple (lines 42–46), HasPrimitiveVectorWith (lines 81–84) and all three proofs at Sl2.lean:170–215. The new statement has exactly the triple relations and primitive conditions those declarations take. The coefficient formula is for every natural j; the nonzero-power conclusion is restricted to i <= N. Finite-dimensional vector spaces over a field are Noetherian and torsion-free, so every additional Mathlib hypothesis is present. There is no required diagonalizability of the module action of h.

For step 1 I opened the entire statement of lem-sfb-killing-cartan-rank-one-spaces. It actually supplies one-dimensionality, ordinary eigenvector identities, alpha(c)=2 and the triple, not just a root-space definition. The item's stronger diagonalizability implies its triangularizability hypothesis; the nilpotent self-normalizing hypothesis is exactly its Cartan convention, and characteristic zero, finite dimension and Killing nondegeneracy agree. Ordinary root vectors are generalized ones by exponent 1; the cited converse identifies the spaces. Rescaling u and v by inverse nonzero scalars produces the prescribed arbitrary x, without changing c. Since alpha(c)=2 is nonzero, c is nonzero as the Mathlib triple requires.

For step 2 I opened lem-sfb-nilpotent-module-generalized-weight-decomposition and def-wf-lie-algebra. The former explicitly asserts finite support for functions H -> K, not only spanning; I use that clause. Its nilpotency and triangularizability hypotheses hold for the adjoint H-module L. The latter explicitly states Jacobi and that the adjoint action is a representation. The displayed Jacobi calculation proves both weight-shift inclusions directly. Each nonzero raising iterate lies in a generalized weight of distinct index gamma+j alpha, since alpha is nonzero and K has characteristic zero. Finite support then forces an iterate to be zero. This is a short consequence of those statements, rather than a new nilpotency or root-string lemma.

For step 3 the new primitive-vector leaf applies to the adjoint representation on the finite-dimensional space L, with h=c, e=x and the normalized f. The assumed vanishing bracket is exactly E y=0 and y has eigenvalue beta(c); the conclusion supplies the natural number m. For step 4 the chosen nonzero z exists by the item's L_(alpha+beta) hypothesis. Termination from step 2 gives a last nonzero E^r z even when r=0. Its weight is beta+(r+1)alpha, so evaluation at c is m+2r+2. The same leaf supplies a natural highest weight N; characteristic-zero injectivity identifies N=m+2r+2. Consequently r and r+1 are <= N. The formula at j=r gives the nonzero factor (r+1)(m+r+2), with both factors positive integers. I checked the off-by-one bounds and the raising coefficient explicitly.

For step 5 the lowering weight calculation puts F^(r+1)w in L_beta, whose one-dimensionality is exactly the statement cited again from the rank-one node. Since y is nonzero, the new vector is a scalar multiple of y. Linearity makes its E-image zero, contradicting the nonzero formula from step 4. No surjectivity of a bracket map, semisimplicity of the sl2 module, or independent-root assumption is smuggled into this step.

I tested the edge cases r=0 and m=0: N=m+2r+2 still gives r+1 <= N and the positive coefficient remains nonzero. Alpha=beta is not divided out or assumed impossible: the same proof would contradict the existence of L_(2alpha), consistent with reduced roots. Opposite roots and beta=0 are excluded by the item; dropping beta != 0 would lose the one-dimensionality used in the last step (e.g. a higher-rank Cartan has nonzero vectors in ker alpha), so that hypothesis is essential to this argument. Rank-zero and rank-one algebras have no admissible nonopposite root sum, hence the assertion is vacuous there. In sl3, x=E12 and y=E23 give the expected nonzero E13 bracket. All characteristic-zero uses were located explicitly; no positive-characteristic claim is made.

I checked delivery-errors B–E against both files: the leaf has only a statement, no proof; all notions are defined inline or by def-wf-lie-algebra; source and exact Mathlib lines were read; every search record is an actual msearch query; no elementary fact is promoted to a node. Every non-elementary step cites a statement that supplies its claimed input, and citations.json contains exact substrings. The proof_deps list is exactly the union of uses. The new leaf cannot cycle back to the item (its only statement dependency is the Lie-algebra definition), and the existing rank-one and weight nodes do not depend on the item. Every proof step is below 700 characters, so none triggers the 2000-character hidden-lemma audit. The item is an actual contradiction proof, not a restatement in a new node.

## Unfinished work

None in the requested one-level split. The two existing inputs retain their own current states; I have not split or edited another worker's node. The required dry run and direct delivery follow this report.

Dry-run correction: the citation checker required the Jacobi quotation to have at least 40 characters. I replaced the short isolated formula with the complete definition statement, including Jacobi and the adjoint representation; the mathematical argument is unchanged.

The first full server preflight passed at 08dd8539368. Before the final dry run I expanded the step-1 rank-one and step-3 primitive quotations to the complete cited statements so that the quotation itself also displays the triple construction and natural-eigenvalue clause, respectively.
