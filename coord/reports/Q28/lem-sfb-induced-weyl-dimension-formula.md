# Stage-1 delivery: lem-sfb-induced-weyl-dimension-formula

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-induced-weyl-dimension-formula.json`: item, statement unchanged, four proof steps, status split; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-dominant-flag-line-kempf-vanishing.json`: statement-only Kempf vanishing, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-flag-line-euler-alternant.json`: statement-only integral equivariant Euler identity for arbitrary weights, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-weyl-alternant-augmentation.json`: statement-only abstract root-datum augmentation lemma for arbitrary numerator and regular denominator, no Mathlib match.
- `citations.json`: eight verbatim statement extracts covering every citation in every item step.

Search commands were all run through the prescribed msearch.py and are recorded in searches.jsonl. I read their returned types. Each new node has LeanFinder (two phrasings), Loogle and grep; LeanSearch was also tried. The Euler-character LeanSearch timed out and is recorded as unavailable. The successful services returned Lie-module weight-space traces, ordinary-group characters and root bilinear forms. Character.lean defines a field-valued trace character: its char_one is insufficient for an ordinary integer dimension in characteristic p, and it supplies neither the integral character formula nor Kempf vanishing. I read that definition and char_one in Mathlib/RepresentationTheory/Character.lean:56--67, and the root-form product results around CanonicalBilinear.lean:309--344. These are not matches. No Mathlib leaves were created.

## Attachments

None. Searches by the exact item id/docstring tag and by Weyl dimension, Weyl character, Kempf and induced-module terminology in lean/WeilConjectures found no declaration stating the item. The ordinary and discrete group induction declarations do not concern regular functions on an algebraic group scheme. No Lean was written and no compiler was run.

## Wanted literature

WANTED: Jantzen, Representations of Algebraic Groups, second edition (2003), Part II 4.5, for lem-sfb-dominant-flag-line-kempf-vanishing.

WANTED: Jantzen, Representations of Algebraic Groups, second edition (2003), Part II 5.10--5.12, for lem-sfb-flag-line-euler-alternant, lem-sfb-weyl-alternant-augmentation and the item's textbook proof.

These references are not local and were not downloaded. The item's source already records the missing book. I read the local Milne iAG2017 PDF, Section 18c and 22d, especially the proof of 22.48 and Theorems 22.50--22.52 on printed pp.479--480. The replacement sign conventions and the assembly/augmentation argument are marked agent-origin, rather than claiming to have read Jantzen. I also checked the already-cited online primary reference, Williamson, Algebraic representations and constructible sheaves, https://arxiv.org/pdf/1610.06261, sections 1.1--1.3: its Borel contains the negative roots, so its inducing-character convention must be translated before using it here.

## Source error

The item is true as stated; there is no STATEMENT-DISPUTED and no correction of its statement. The local auxiliary reference has errors relevant to using it as a proof:

1. Milne 18c and the proof of 22.48 identify L(chi)-sections with f(gb)=chi(b)^(-1)f(g). With positive roots in Lie(B), the line needed here is therefore L(-lambda), not L(lambda). For SL2 with upper triangular B and fundamental weight omega, L(n omega)=O(-n). Thus 22.51 as printed with dominant chi is false: chi=2 omega gives H^1(P^1,O(-2)) of dimension one. Our vanishing node instead says H^i(L(-lambda))=0 for dominant lambda.
2. The printed Euler alternant in 22.50 has the corresponding sign problem. Taking its chi=2 omega predicts augmentation 3, whereas the Euler characteristic of O(-2) is -1. The correct identity in our convention is q_lambda A(-rho)=A(-lambda-rho) for L(-lambda). At lambda=-2 omega it gives -1 as required. The item never substitutes a Borel-opposite formula without checking this sign.
3. 22.52 as printed claims a Weyl character for every simple representation, then refers to a general case beyond characteristic zero. This is false in positive characteristic: for SL2 in characteristic p, the Frobenius twist of the standard module is simple of highest weight p omega and has dimension 2; the Weyl product is p+1. Our Euler identity concerns line-bundle cohomology and requires no simplicity. No node for the false printed simple-module assertion was created.

The current blueprint's latest sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md were read. The item remains a supporting representation-theoretic input in the inherited alteration/moduli/Haboush branch under direct-images proof (3). I did not change a unit or chapter. The inherited ancestor is null, and tools/blueprint_refs.py ancestor confirms None; the inherited detailed place and via chain were retained, with the item prepended for its children.

## Not duplicates

lem-sfb-dominant-flag-line-kempf-vanishing vs lem-sfb-homogeneous-line-bundle-sections: the existing node identifies global sections and constructs the bundle; it makes no higher-cohomology vanishing assertion.

lem-sfb-dominant-flag-line-kempf-vanishing vs lem-sfb-rho-section-modules: the existing node gives nonzero finite-dimensional H^0 only at multiples of rho, with no higher-cohomology assertion.

lem-sfb-flag-line-euler-alternant vs lem-sfb-induced-weyl-dimension-formula: the new node is an integral virtual-character identity in every degree for arbitrary, including non-dominant, weights; it asserts neither concentration in degree zero nor the dimension product. The item still needs vanishing and a separate root calculation.

lem-sfb-weyl-alternant-augmentation vs lem-sfb-induced-weyl-dimension-formula: the new node is a group-algebra identity for an abstract root datum, arbitrary regular denominator and arbitrary numerator. It contains no field, algebraic group, module or cohomology and does not assert the existence of a quotient polynomial.

lem-sfb-weyl-alternant-augmentation vs lem-sfb-restricted-rho-simple-dimension: the existing node is about a simple algebraic-group module at the single weight (p-1)rho; it supplies no abstract alternant calculation and would be the wrong object to use here.

Searches of the whole DAG and blueprint by Weyl, Kempf, alternant, alternating character, root system and flag variety found no other node stating these facts. The generic proper coherent cohomology node is reused, including its Stacks Tags 02O5 and 02O6, rather than duplicated. These representation-theoretic results have no Stacks tag in the local Stacks source; no tag was invented for them.

## Review by Q28

I checked B--E with the written files and the source open. All new nodes introduce their fields or lattices, groups, sign conventions and objects; they have statements only, empty proof lists and no proof sketch in the statement. The root lemma defines its rational group algebra, augmentation and root-datum assumptions inline, and cites the existing integer root-pairing conventions of lem-sfb-crystallographic-positive-base, whose full statement I read. The group nodes reuse the actual homogeneous bundle node and introduce Zariski cohomology as the right derived functors of sections. Every new notion needed in the assembly is either defined there or is the statement of an existing cited node. No new node is an elementary closure lemma or a relabelled clause of the item: the nontrivial ingredients are higher-cohomology vanishing, a virtual-character identity, and an abstract alternant calculation.

Step 1 uses exactly the statements I opened of lem-sfb-reductive-borel-pair-structure, lem-sfb-homogeneous-line-bundle-sections and lem-pc-coherent-hi. The first explicitly gives semisimple implies reductive and a proper finite-type flag quotient. The second explicitly gives coherence, the inverse-character transformation equation on every F-algebra, the linear identification and the correct left action. The third explicitly makes coherent H^0 over a proper scheme above Spec(A), A Noetherian, finite over A. Taking A=F satisfies this hypothesis. This is a generic tool of another unit, declared in split_report.tool_uses, not a replacement of a unit route. Finite-dimensionality does not come from a theorem about simple modules.

Step 2 uses exactly the new Kempf statement. I compared the fibre action in its definition with step 1: chi=-lambda makes chi(b)^(-1)=lambda(b). Its dominance is for our positive roots, not the opposite convention. Algebraic closure, semisimple simply connected group, split torus and all-characteristic scope are explicitly present. This new input is sourced to Milne's discussion with the printed sign corrected and the missing Jantzen reference acknowledged.

Step 3 uses exactly the new Euler statement. I checked that it allows arbitrary lambda, has the same line bundle and action as step 1, and writes an identity in Z[X] rather than a trace equality in F. It explicitly includes the finite direct sum into character spaces and finite cohomological support; hence after step 2, adding the integer multiplicities gives the ordinary dimension by finite direct-sum arithmetic. I have not imported an uncited torus weight-decomposition theorem into this step: that decomposition is part of the Euler input's statement. The use of an Euler polynomial does not assume its numerator/denominator can be evaluated separately at the identity.

Step 4 uses the statements of lem-sfb-simply-connected-character-lattice and lem-sfb-reductive-borel-pair-structure, both opened in full. The former gives rational bases of the root and dual root spaces and hence the spanning required in the abstract lemma; the latter supplies the perfect integer pairing, reduced crystallographic datum and its reflections. The actual integral rho is in the item's data. The new augmentation lemma explicitly gives both the evaluation product conditional on q A(sigma)=A(nu) and positivity of every rho denominator. Substitution sigma=-rho, nu=-lambda-rho is therefore legitimate; cancellation of the two minus signs in each fraction is elementary. No opposition automorphism, a dual-module identification, or simplicity theorem is hidden in that step.

For the future splitter, the abstract augmentation input has independent mathematical content. Its standard argument is to substitute e^x=exp(t<h,x>) in Q[[t]] for regular h. Put N=|Phi+|. The degree-j coefficient of the alternant, as a polynomial in nu and h, is alternating under each reflection in each variable. Therefore it is divisible by the product of the N distinct reflection hyperplane linear forms in each variable, vanishes for j<N, and at j=N is a constant times the two discriminants. The constant is nonzero: applying the discriminant differential operator in nu to the degree-N alternating sum gives |W| times the h-discriminant. The quotient identity then compares the degree-N coefficients for nu and sigma, giving the claimed ratio even when nu is singular. Positivity of rho on positive coroots follows from <rho,alpha_i^vee>=1 and the positive integral expansion of every positive coroot in the simple coroots. These substantive root-system facts were kept in the statement-only input, not called elementary in an assembly step. This argument is agent-written; a textbook proof is WANTED as above.

I tested small cases explicitly. For SL2, lambda=n omega, n>=0, the bundle is O(n), the section dimension is n+1 and the alternant is (e^((n+1)omega)-e^(-(n+1)omega))/(e^omega-e^(-omega)); n=p confirms the distinction from the two-dimensional simple Frobenius twist. For SL3 and lambda=omega_1, the three positive coroot factors are 2,1,3/2, giving 3; the left-translation section representation has the dual highest weight, which leaves this dimension unchanged. For lambda=0 the product is 1. The root lemma also works when nu is singular (the quotient is zero) and for a negative regular denominator. For the empty root datum, X=Y=0, W={1}, A(0)=1 and q=1; the argument gives dimension 1. Products of root systems factor the formulas, so no irreducibility assumption is used. Characteristic 2 changes none of the integral calculations.

I inspected every proof step for an omitted comparison or standard lemma. No step exceeds 2000 characters. The only elementary operations left inline are replacing chi by -lambda, adding dimensions in an already supplied finite direct sum, extending an integer identity to Q[X], and cancelling signs. citations.json quotes were copied from the actual statements, and a local substring check verified them; no project validation script was run on this machine. The required server dry run will provide the DAG, route and cycle checks.

## Unfinished work

No unfinished work in the one-level split. The three newly stated inputs remain unsplit as required; they are not claims of completed Lean proofs. The missing literature and source errors above are explicit limitations of the agent-origin assembly.

The first dry run returned two form diagnostics: the abstract root node needed an explicit existing-node citation even though its axioms were written inline, and step 4 used the phrase “the item's data”. I added the existing crystallographic root-pairing citation and made the hypothesis reference direct. No mathematical statement or proof route changed.
