# Stage-1 delivery: lem-per-bennett-normal-flat-local-criterion

Group Q22, 2026-10-24. Direct worker delivery, independently reviewed by the maintainer after push. No Lean was written and no compiler, Lake, or build tool was run. All writes are in this item's sandbox; repository and launcher files were only read.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-bennett-normal-flat-local-criterion.json: item, statement unchanged, split into eleven complete proof steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-split-nilpotent-filtration-graded-piece.json: one new statement-only lemma; unsplit, no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- citations.json: twenty citation entries, one for each use in each item step, with the cited statement copied verbatim.
- report.md: this report. searches.jsonl contains the actual msearch results.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, Bennett, normal-flatness and Hilbert--Samuel words found no declaration stating this item. The nearby closed-immersion conormal base-change theorem is different. I also inspected lean/Sheaf/RingTheory/NormalFlatHilbertConvolution.lean: its theorem is sorry, proves only the forward convolution, and is not an attachment.

## Wanted sources

WANTED: Cossart--Jannsen--Saito, Canonical embedded and non-embedded resolution of singularities for excellent two-dimensional schemes, March 12 2009 preprint, section 2, Definition 2.1 and Theorem 2.3, printed pp.28--29, for lem-per-bennett-normal-flat-local-criterion. Read online at https://epub.uni-regensburg.de/13766/1/MP32.pdf; no archival copy is present in this machine's literature directory.

WANTED: Bruce Michael Bennett, On the characteristic functions of a local ring, Annals of Mathematics 91 (1970), 25--87, Theorem (3), for lem-per-bennett-normal-flat-local-criterion. CJS cites it for the numerical criterion, but this delivery does not substitute that citation for a proof.

## What was wrong or incomplete

The item had no proof. Its source.document names an absent BMT ancestor file, with its source.place honestly specifying the actual CJS statement; that historical source record is retained. I checked CJS online: section 2 assumes an excellent scheme, not a reduced scheme, and Theorem 2.3(1)--(2) gives the degree-wise numerical criterion along a regular centre. The length version is precisely its sum, not an eventual-polynomial statement. No statement dispute or correction was needed.

The DAG already has an accepted, fully expanded agent proof of the reduced version, lem-trf-bennett-normal-flat-numerical-criterion. I read its entire proof and review, and checked where reducedness enters: it does not. I retained its algebraic argument, adapted it to the present item, and isolated its finite nilpotent filtered-algebra calculation as a reusable statement. I did not cite the reduced-version statement to obtain a nonreduced conclusion, and I did not copy its reviewed status.

The current latest blueprint, its chapter and unit records, and the ancestor lem-per-artin-gabber-affine-curve proof were read. This numerical input belongs to the historical regular-resolution refinement already recorded in blueprint.from; the latest ancestor proof does not separately state Bennett's criterion. No chapter, unit, target, or blueprint file is changed.

## Not duplicates

lem-per-bennett-normal-flat-local-criterion vs lem-trf-bennett-normal-flat-numerical-criterion: the existing criterion assumes reduced R; the present item intentionally treats nilpotents and embedded components. Its proof can be adapted, but its statement cannot be applied to the present R.

lem-per-split-nilpotent-filtration-graded-piece vs lem-trf-bennett-normal-flat-numerical-criterion: the new lemma is a single finite quotient-module isomorphism over an arbitrary base ring and ideal, under freeness only below a fixed N. It contains no local regularity, prime localization, numerical equality criterion, or flatness equivalence. The criterion's proof contains this calculation, but its statement does not expose it.

lem-per-split-nilpotent-filtration-graded-piece vs lem-trf-injective-graded-filtration-splits: that statement splits filtrations with injective factors in an abelian category; our hypotheses concern free quotient modules, which need not be injective, and the conclusion identifies a piece for the sum of two ideals.

lem-per-split-nilpotent-filtration-graded-piece vs lem-trf-normal-flat-hilbert-convolution: the existing convolution assumes normal flatness in every degree and regularity of a local quotient. The new lemma permits a nonfree last piece over an arbitrary ring. That unrestricted last piece is essential to the converse induction, so normal-flat convolution cannot replace it.

Before creation I searched the whole DAG by Bennett, normal-flatness, Hilbert--Samuel, free lower filtration quotients, and nilpotent filtrations; searched all blueprint nodes using blueprint_refs.py search (normal flat, Bennett, Hilbert, nilpotent filtration, filtered algebra, filtration); obtained the ancestor with blueprint_refs.py ancestor; searched both library roots for the filtration notion. No node states the new quotient-module formula. The Mathlib hits concern filtrations/stability, Krull dimension, quotient transition maps and ordinary flatness. I read the signatures and the source of RingTheory/Filtration.lean and Ideal/Quotient/PowTransition.lean. Neither states the new formula, exactly or by one-line specialization. All newly recorded searches are actual msearch calls and their raw summary records are preserved; no unavailable service is represented as a negative result.

## New lemma: mathematical argument retained for its next worker

Let D,p,B,Q,N be as in the new node, and M=Q^N. For each j<N, lift a D-basis of Q^j/Q^(j+1) to Q^j and call its D-span E_j. Projection E_j to that quotient is bijective: its generators span the quotient, and any relation projects to a relation in a free basis, so every coefficient is zero. Subtracting a lifted expansion gives Q^j=E_j direct-sum Q^(j+1). Hence, successively for a=N,N-1,...,0,

Q^a = M direct-sum (direct-sum over a<=j<N of E_j), with E_j isomorphic to D^(r_j).

This is a compatible splitting of D-modules, with no claim about multiplication. Expand (Q+pB)^q as the sum of p^(q-a)Q^a for 0<=a<=min(q,N); all later Q powers vanish. Insert the same fixed direct decomposition of B into every summand. On E_j, the smallest p-exponent is max(q-j,0); on M it is max(q-N,0). Since ideal powers are nested, the sums on these coordinates equal the submodules with those smallest exponents. Thus b^q equals the direct sum of p^max(q-N,0)M and all p^max(q-j,0)E_j. At q=N and q=N+1, quotienting gives the displayed isomorphism, using the chosen bases of E_j. Every factor is killed by p, so it is an isomorphism of D/p-modules.

This calculation is independent of a coefficient section, reducedness, Noetherianity, localness, and any behaviour of the top piece M. Those restrictions are therefore deliberately absent from the new statement. The lemma is a nontrivial independent comparison for two ideal filtrations, not a clause of Bennett's criterion and not a two-line definition expansion.

## Review by Q22

I read coord/delivery-errors.md sections B--E in both copies, all eleven draft steps, the entire accepted reduced-version proof, the statement of every cited node, the cited Stacks source passages, and the online CJS numerical criterion. The proof is marked agent-written because the paper's proof is an external Bennett reference and the archived document is unavailable. The new lemma's source explicitly says agent-written and makes no invented Stacks-tag claim. Its complete argument is above; its node itself has only a statement and no proof or proof dependencies.

Step 1 uses exactly three statements: regular local rings are domains (lem-sc-regular-local-domain, Stacks 00NP, lemma-regular-domain), Noetherian submodules of finite modules are finite (00IK, lemma-Noetherian-basic), and exactness of localization (00CS, proposition-localization-exact). A is regular local, and each ideal power is a submodule of the finite R-module R, so all hypotheses hold. The quotient G_j is finite and killed by I; localizing sends its ideal-power presentation to the displayed graded piece over R_I. This needs no domain hypothesis on R: only A must be a domain. Its generic localization is K=Frac(A).

Step 2 applies the actual Nakayama generator statement to a finite A-module M, with A local, and the exact-localization statement to the kernel of A^mu -> M. Equal finite dimensions make the localized kernel zero. A kernel element lies in A^mu, and a nonzero denominator killing it makes every coordinate zero since A is a domain. This proves freeness even at rank zero; no unquoted freeness criterion is hidden.

Step 3 uses length-additive-short-exact (00IV, lemma-length-additive), whose statement gives length equality for each filtration factor. All factors here are finite-dimensional residue-field spaces, so a basis supplies a finite composition series. This gives h=Lambda g for all n. The two inverse finite-difference identities are written out as telescoping, so the numerical criterion is converted without losing the small n entries.

Step 4 cites the five completion statements for Noetherianity/completeness, the local maximal ideal and residue field, quotients modulo powers, regularity, and dimension. I read 05GH (lemma-completion-Noetherian), 05GI (lemma-radical-completion), 05GG (lemma-hathat-finitely-generated), and More on Algebra 07NY/07NV (lemma-completion-regular, lemma-completion-dimension). R and A are Noetherian local, their maximal ideals are finite, and their quotients by those ideals are fields. These are exactly the required hypotheses. Taking kernels of successive quotient maps gives g_C=g_R.

Step 5 uses the quotient-completion statement to give C/J=D and the image of completed ideal powers. Exact completion (00MA/00MB, lemma-completion-tensor and lemma-completion-flat) applies only to the finite modules I^(j+1), I^j, G_j. The finite-module tensor statement gives H_j=D tensor_A G_j, because I kills G_j and its two adic filtrations agree. The module-completion statement 05GG gives the residue reduction H_j/pH_j=G_j/aG_j. It does not assert freeness in the last degree.

Step 6 cites Cohen coefficient-ring existence (032A, theorem-cohen-structure-theorem), the existing regular-complete coordinate statement (0C0S, lemma-regular-complete-containing-coefficient-field), and the power-series adic-evaluation statement. C is nonzero complete equicharacteristic: its field F has the same characteristic as its residue field. Consequently p=0 in C even in positive residue characteristic, so the coefficient ring is a field. Its image is a coefficient field in D. D has dimension d and is regular, complete, Noetherian; hence a generating d-tuple gives the indicated power-series isomorphism. The chosen lifts lie in n, so evaluation applies to C. The explicit evaluation formula ensures that its composite with C->D is theta. This proves the section; no separability of k/F is used or claimed.

Step 7 cites the new lemma's actual module-isomorphism statement, not its proof. Under the induction hypothesis j<N, step 5 gives the required free D-modules. In B=C/J^(N+1), Q^(N+1)=0 and Q^N=H_N; nB=Q+pB by the section. Since J^(N+1) lies in n^(N+1), the quotient preserves precisely the degree-N maximal-ideal piece. Coefficient extraction in D=k[[T_1,...,T_d]] proves the monomial basis count directly. Thus the term mu_N remains unrestricted. I checked the application against every hypothesis of the new lemma and included its entire quoted formula in citations.json.

Step 8 is the elementary convolution identity: split a monomial by its last-variable exponent and interchange two finite sums. It starts with c_0 and includes d=0; c_d(0)=1 is the coefficient needed in the induction.

Step 9 obtains flatness of each G_j from its split inclusion/projection in the graded direct sum, using the tensor-injection definition directly. It then applies only the finite-flat-local-free node (00NZ, lemma-finite-flat-local); G_j is finite by step 1 and A is local. The resulting ranks and step 7's formula give the numerical equality, including degree zero. Step 10 proves the converse by induction starting from G_0=A, cancels the common lower-degree convolution sum, and uses the already proved kernel argument of step 2. Step 11 constructs a basis of the direct sum from the degree-labelled bases and proves tensor-injectivity coordinatewise with finite support. These steps use no unquoted tensor-exactness assertion.

All cited statements were opened rather than inferred from titles; quotations are verbatim full statements, so they include every hypothesis used. Off-unit algebraic statements are declared as generic tool uses in split_report.tool_uses, never as top-level accepted tool_uses. None replaces a step of the Fourier/perverse unit's route. Every proof step is under 2000 characters. The new lemma is statement-only, self-contained and uses the existing free-module definition; no notion is defined by an external tag.

Small-case tests: for I=m, d=0 and both numerical sequences are identical while the graded ring is a vector space. For I=0, R=A is a regular local domain, R_I is its fraction field and h_R(n)=binomial(n+d,d)=Lambda^d(1)(n). For R=k[t,x]_(t,x)/(x^2), I=(x), the flat nonreduced example has h_R(n)=2n+1 and h_(R_I)=(1,2,2,...), whose partial sums agree. For R=k[t,x]_(t,x)/(x^2,tx), I=(x), G_1=k is torsion over k[t]_(t); h_R(n)=n+2 for n>=1, whereas Lambda h_(R_I)(n)=n+1, so both sides of the criterion fail. This tests that nilpotent torsion is retained rather than discarded. For the new lemma at N=1, a square-zero algebra B=D direct-sum M gives b/b^2=(p/p^2) direct-sum (M/pM), including nonfree M. Taking p=0 leaves exactly Q^N. Taking Q=0 leaves only the j=0 summand. Higher truncated polynomial examples B=D[x]/(x^(N+1)) give the expected shifted p-adic pieces. Zero-rank lower pieces are harmless.

## Unfinished work

No part of the assigned stage-1 split is intentionally left unfinished. The single new lemma remains unsplit as the brief requires; its argument is preserved above for the next worker. Required server dry run and push results are reported after the tools finish.
