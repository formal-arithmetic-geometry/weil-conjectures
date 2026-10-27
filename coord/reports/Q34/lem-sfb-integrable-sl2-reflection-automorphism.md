## Worker report

Q34 split `lem-sfb-integrable-sl2-reflection-automorphism` by one level, preserving its statement and statement dependencies. There was no earlier item, split, report or citation file in this sandbox. The existing repository searches were read and retained; newly executed searches are recorded separately and verbatim in the node records and `searches.jsonl`.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integrable-sl2-reflection-automorphism.json`: item, now split into five steps; unchanged statement.
- `dag/nodes/sec-six-functors-basics/lem-sfb-locally-nilpotent-derivation-exponential.json`: one new statement-only, unsplit prerequisite; not a Mathlib leaf.
- `citations.json`: verbatim statement quotations for both citations in step 1. Steps 2–5 cite no external facts.
- `report.md`: this report.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, `IsSl2Triple`, locally nilpotent terminology and `LieDerivation.exp`. There was no project declaration stating the item or the new prerequisite. In particular, the upstream source does not supply an attachment for either node.

## WANTED

WANTED: Serre, *Complex Semisimple Lie Algebras*, Chapter VI appendix, the Serre-presentation reflection construction, for the item and its locally nilpotent exponential prerequisite. The source is already identified as wanted by the imported item's source record. I did not download or assert that I had read it. No Stacks tag is assigned to this Lie-theoretic lemma.

## Sources and route

I read Milne, `literature/milne-algebraic-groups_iAG2017.pdf`, printed pp.503–504 (PDF pages 515–516), Theorem 23.63 first proof, and printed p.508 (PDF page 520), which explicitly extends the result to arbitrary characteristic-zero fields. Milne refers the Serre-presentation proof to Serre VI rather than spelling out the local exponential argument. The item already identifies that expansion as agent-supplied; this delivery keeps that attribution and uses `proof_origin.by = agent`. The new prerequisite's source explicitly says it is an agent-supplied input, not a theorem stated in Milne. Its proof is not falsely attributed to the book.

I also read the chapter record, unit record and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit statement and direct-images proof. The inherited dependency chain serves direct-images proof (3), through the existing alteration, moduli, algebraic-group and rational Serre-presentation prerequisites. `blueprint_refs.py ancestor` reports a null blueprint ancestor here; I retained that and the inherited via chain and specified the exact added argument in `from.place`. No unit or chapter statement or route is altered.

## New nodes

`lem-sfb-locally-nilpotent-derivation-exponential` states that a rational linear Lie derivation D, with a power bound for each vector, has a well-defined pointwise finite exponential, preserving the bracket and with inverse Exp(-D). Its statement defines derivation, local nilpotence, powers, cutoff independence and the meaning of Lie automorphism inline. Its only statement dependency is the actual Lie-algebra definition. It has no proof steps, proof dependencies or proof sketch embedded in its statement.

This is a genuine reusable prerequisite, with no sl2 triple, Cartan subalgebra or weights. The item's remaining four steps prove its reflection and weight clauses themselves; they do not apply newly created versions of those clauses.

For the next worker, the elementary algebra behind this prerequisite can be organized as follows (this is a report of the intended argument, not a split of the new node). Increasing a cutoff adds zero terms; a common cutoff for x and y proves linearity. Induction on n using the derivation identity and Pascal's rule gives
D^n[x,y] = sum_(i+j=n) binomial(n,i)[D^i x,D^j y].
If D^p x=0 and D^q y=0 with p,q positive, every summand vanishes for n >= p+q-1. Divide the identity by n!, sum using this cutoff, and reindex the finite rectangle 0<=i<p, 0<=j<q to obtain Exp(D)[x,y]=[Exp(D)x,Exp(D)y]. For the inverse, on the finite D-stable span of x,Dx,...,D^(N-1)x the two exponential polynomials multiply to the identity: the coefficient of D^k for 0<k<N is sum_(i+j=k) (-1)^j/(i!j!)=(1-1)^k/k!=0, and the constant coefficient is 1. Terms of degree >=N kill x. This proves both inverse identities pointwise, without a uniform nilpotence bound on L. These binomial and inverse arguments are the nontrivial content retained for the new node's later split.

## Searches

Before creating the new node I searched the entire DAG by local-nilpotence, derivation and exponential concepts, and by the source's Theorem 23.63 / Serre VI references. I inspected the statements of the unipotent exponential, formal class-two exponential, Chevalley adjoint Weyl signs, rational opposition and root-normalization nodes. Whole-blueprint searches using `tools/blueprint_refs.py search` for `nilpotent`, `locally nilpotent`, `Lie derivation`, `derivation`, `exponential` and `reflection` found no duplicate. The latest blueprint Lie-algebra definition was also read.

All new Mathlib searches used the required msearch.py command. For the new node, LeanFinder's two different local-nilpotence phrasings, LeanSearch, Loogle `LieDerivation.exp`, and the Algebra/Lie grep all point to globally nilpotent exponentials. I read `Mathlib/Algebra/Lie/Derivation/Basic.lean:405–426` and `Mathlib/RingTheory/Nilpotent/Exp.lean` and checked the actual hypothesis `IsNilpotent D.toLinearMap`. It is not the hypothesis of the new node. The second phrasing additionally returned `LieDerivation.iterate_apply_lie`, a binomial ingredient, not the whole pointwise automorphism theorem. The new node is unsplit and records the global result as a candidate only.

For the item, I read its inherited LeanFinder/LeanSearch/Loogle/grep results and ran an additional integrable infinite-dimensional reflection query, Loogle `IsSl2Triple` and an Algebra/Lie grep. I read `Sl2.lean:41–46` (relations only) and `Weights/RootSystem.lean:364` and its finite-dimensional Killing-algebra context. Neither constructs the asserted locally finite exponential automorphism under the item's hypotheses. All services answered; no unavailable search was represented as absence. This delivery adds zero Mathlib leaves.

## Not duplicates

lem-sfb-locally-nilpotent-derivation-exponential vs lem-sfb-unipotent-exponential-construction: the latter constructs a scheme morphism into a finite-type unipotent matrix group; it does not exponentiate a locally nilpotent derivation of an arbitrary-dimensional abstract Lie algebra.

lem-sfb-locally-nilpotent-derivation-exponential vs lem-sfb-formal-class-two-exponential: the latter is a formal-series identity for a class-two tuple in an associative algebra; it gives neither a Lie-derivation exponential nor its pointwise local-nilpotence inverse.

lem-sfb-locally-nilpotent-derivation-exponential vs lem-sfb-chevalley-adjoint-weyl-signs: the latter is a root-vector sign theorem for finite-dimensional split semisimple algebras, and itself uses the item; citing it would also reverse the dependency.

lem-sfb-locally-nilpotent-derivation-exponential vs lem-sfb-serre-rational-presentation: the latter is a presentation and root-realization theorem, with a root datum and finite generators, not a general derivation theorem.

lem-sfb-locally-nilpotent-derivation-exponential vs lem-sfb-integrable-sl2-reflection-automorphism: the new node only supplies the general exponential tool; it contains none of the reflection formulas or weight-space conclusion. The item proves those by calculation.

## Review by Q34

I reviewed the actual node statements, the Milne pages and latest blueprint files named above, rather than treating the imported dependency list as an accepted proof. No statement dispute or statement change was needed.

Step 1 cites `def-wf-lie-algebra`, whose statement gives bilinearity, Jacobi, ad(x)y=[x,y] and the adjoint representation. Rewriting Jacobi is exactly the inner-derivation identity used here; no tangent-space or algebraic-group definition is substituted. The second cited node explicitly supplies linear Lie automorphisms and their negative-exponential inverses. I checked that E=ad(e) and G=-ad(f) are rational linear derivations and are locally nilpotent under exactly the item's assumptions. Negative powers introduce only the scalar (-1)^n. Composition and reversal of inverses require no extra theorem node. The general exponential assertion, the sole substantive non-elementary input, is cited rather than hidden in this step. The two quotations in citations.json are verbatim substrings of these statements.

Step 2 uses only the item's relations. I checked each sign: E(f)=h, E(h)=-2e, G(e)=h, G(h)=-2f, E(t)=-alpha(t)e and G(t)=-alpha(t)f. Thus the quadratic terms are -e in A(f) and -f in B(e), and higher terms vanish on these vectors. Both factors have h-2 times their respective root vector. The use of alpha(h)=2 is stated where it occurs. These are direct finite-sum evaluations, not an omitted representation-theoretic lemma.

Step 3 explicitly composes the expressions in the correct order A after B after A. I recomputed BA(t)=t-ae-ah, BA(e)=e+h-f and BA(f)=-e. Applying A gives t-ah, -f and -e. In particular no assumption that w is involutive on all of L is made; only its restriction to t is a reflection.

Step 4 proves s^2=id on t using alpha(h)=2. Since w|t=s, this also computes w^(-1)|t=s. Its displayed bracket equality applies bracket preservation to [s(t),x], so the reflected weight is beta-beta(h)alpha with the correct sign. It does not assume diagonalizability or a decomposition of L.

Step 5 proves surjectivity, which a mere weight inclusion would not supply: for gamma=beta-beta(h)alpha one has gamma(h)=-beta(h) and gamma(s(t))=beta(t). The bracket formula for w^(-1)y then puts the unique preimage in L_beta. The resulting isomorphism is of rational vector spaces; general weight spaces are not being asserted to be Lie subalgebras. Steps 2–5 are each under 500 characters, direct computations from definitions and previous steps, and contain no concealed comparison theorem.

For the new node I checked B1–B8: self-contained quantifiers, arbitrary dimension, a positive pointwise cutoff, explicit linear derivation identity, a genuine Lie-algebra definition dependency, single TeX escaping, source attribution and statement-only status. It is not incorrectly marked Mathlib despite the global-nilpotence candidate. The full-DAG and full-blueprint searches above rule out duplicate statements, and no newly created node repeats an item's clause.

Small cases checked: L=0 and D=0 give the identity exponential. An abelian Lie algebra Q[X] with D=d/dX is locally nilpotent but has no global nilpotence exponent; the new statement still makes sense, illustrating why Mathlib's hypothesis cannot be inferred. For the item, the standard rational sl2 matrices e=E12, f=E21, h=diag(1,-1) give conjugation by [[0,1],[-1,0]], with e sent to -f and f sent to -e. Elements t in ker(alpha) are fixed. Beta=0, beta(h)=0, and zero weight spaces cause no division or excluded case. The calculations use no finite-dimensionality, semisimplicity, nondegenerate Killing form, or nonzero weight-vector hypothesis.

I corrected no source statement and changed no inherited statement dependency. I extracted the substantive local-exponential argument instead of labelling it elementary, supplied the explicit inverse-weight argument rather than asserting transport, and retained the source's existing disclosure that the reflection expansion is agent-written. No SGA source, Lean edit, compiler, Lake command, repository write or git command was used.

## Unfinished work

The new prerequisite is intentionally statement-only and unsplit for a subsequent stage-1 item. No part of the assigned item's assembly proof is left unfinished. Required dry run and delivery follow this report.
