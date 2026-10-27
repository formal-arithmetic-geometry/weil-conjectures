## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-graded-power-split-linear-factorization.json`: item, split into four steps; statement unchanged.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-graded-near-projective-hom-divisibility.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quotation for each of the item's two step/node citations.
- `searches.jsonl`: the actual search-command log, retained without editing.

Attachments: none. I searched the live `lean/WeilConjectures/` for the blueprint tag, gradedPower/graded_power/split_linear, near-projective/almost-projective/factor_hom and the uniform associated-graded notions. The determinant-split and categorical factorization hits concern different maps. No declaration states this item, so there is no ATTACH claim.

WANTED: none.

The item had an empty proof, not an incorrect statement. It now cites the intrinsic finite-sum Hom-divisibility theorem of Stacks 0GAC. Its proof chooses uniform constants and composes the Hom summands with the GIVEN scalar splittings of the GIVEN differential, then checks reduction on representatives. This is the argument that the original source place proposed but had not split. There is one new node and zero Mathlib leaves. No Lean, compiler, Lake, direct git, repository write, or launcher modification was used.

Nothing required for this one-level split remains unfinished. The new Hom-divisibility theorem remains an unsplit dependency, as required. It retains the exact finite-sum argument interface that its later worker must prove, rather than a sketch inside its statement.

## Sources and route

I read `literature/stacks-project/local-cohomology.tex`, Tag 0GA6 (`section-uniform`), including the definitions and graded-isomorphism invariance of d(S), q(S), the paragraph defining (A,n,c)-modules, Tag 0GAC (`lemma-factor-hom`) statement and proof, and Tag 0GAD (`lemma-bound-two-term-complex`) statement and proof. I also read `more-algebra.tex`, Tags 0G92 (`lemma-near-projective`), 0G93 (`definition-near-projective`), and the preceding finite-free factorization discussion. The finite-free condition is written out in the new statement; no undefined near-projective notion is required to interpret it.

For the new node take D=d(S), q=q(S) from 0GA6. Tag 0GAC has precisely t=n-(1+D)c, w=n-(2+D)c, the separate D=0 bound n>=q+2c, and maps to I^w/I^(n+w). Multiplication by a in I^c lands in I^t/I^(n+t), since w+c=t. These are maps between different quotient modules, not scalar multiplication inside the smaller-numerator quotient. Writing the multiplication map as mu_a avoids that ambiguity in the source's sum notation. The hypotheses n>=c and finiteness are explicit. The new node imposes no fixed differential and no completeness hypothesis. Its constants are chosen before c,n,M,u.

I read the chapter/unit records and SETUP's three levels, and the CURRENT latest blueprint files for `sec-deligne-laumon-a1`, `sk-p-dl-a1-perverse`, and `lem-per-artin-gabber-affine-curve.proof.md`. The ancestor's current Step 3 is Verdier exchange, not formal algebraization. The item's inherited `from.place` already says this. I preserved the inherited 0GAQ/rig-smooth branch, rather than claiming that the latest ancestor explicitly states an algebraization theorem or changing the chapter/unit route. The new node's via list prepends this item to its inherited list. No off-unit proof tool is introduced.

## Searches

Before creating the node I searched the whole DAG for 0GAC, 0GA6, 0G92, 0G93, lemma-factor-hom, near/almost-projective, and Hom/divisibility/factorization notions. The only substantive same-tag nodes are this item and its parent `lem-per-power-split-uniform-adic-map-lifting`. The other broad-regex hits are unrelated sheaf, character, or toric facts. `tools/blueprint_refs.py ancestor` gives `lem-per-artin-gabber-affine-curve`; full-blueprint searches for near-projective, factor-hom, power-split, Hom divisibility, and ideal power found no matching theorem. The ideal-power matches are a Rees algebra definition, derived inverse limits, and flat pullback of ideal powers. Direct text search in latest blueprint likewise found no Hom-divisibility theorem.

Every fresh Mathlib query was made with the required msearch.py command, including LeanSearch, Loogle, LeanFinder and grep for both the item and new node. The exact query texts and returned log records are in mathlib_searches, and the unchanged command log is searches.jsonl. Both mathematical questions were tried with a second phrasing. All services answered on this run. The new node's Loogle query returned zero results; semantic searches returned AdicCompletion.transitionMap, IsAdicComplete.StrictMono.extend/lift, compatible quotient reductions, homogeneous ideal identities, and elementary ideal quotient maps. The RingTheory grep's only hit was a Hahn embedding into a divisible hull, not near-projective Hom divisibility.

I opened Mathlib/RingTheory/AdicCompletion/Basic.lean at 765-841: StrictMono.extend composes already supplied compatible maps with quotient transitions; StrictMono.lift assumes an adically complete target and an entire compatible family. Neither creates an extension along our fixed d. I also read the relevant Functoriality.lean transition-map code and LocalProperties/Projective.lean at 1-100: split_surjective_of_localization_maximal concerns actual localized right splittings of a surjection with finitely presented target, not the asserted precision loss. No hit states 0GAC, and none specializes to it in one line.

## Not duplicates

lem-per-graded-near-projective-hom-divisibility vs lem-per-graded-power-split-linear-factorization: the new node is the 0GAC intrinsic divisibility statement for a module whose scalar maps each factor through some finite free module; it produces Hom summands in a quotient with denominator n+w and a finite sum in a DIFFERENT quotient. The item extends a map along one prescribed differential d and ends in denominator 2(n-e). Steps 2-4 supply that argument using the particular h_a; the new node asserts none of that conclusion.

lem-per-graded-near-projective-hom-divisibility vs lem-per-power-split-uniform-adic-map-lifting: the parent is the nonlinear complete-algebra lifting theorem from restricted.tex 0GAQ, for a completed polynomial presentation with conormal differential. The new node is a finite-module Hom-divisibility theorem over arbitrary Noetherian rings and requires no algebra presentation or completeness. Both use 0GA6/0GAC as source provenance, but their statements differ.

## Source error

The pre-existing source note reports the Ext subscript in 0GAD: its condition writes Ext over A/I^c for a complex given only over A/I^n, n>=c. This is not generally well typed. For example A=k[x], I=(x), n=2, c=1 and the complex A/(x^2) in degree zero has no compatible A/(x)-module structure, since x acts nontrivially. I have not used 0GAD as a theorem or carried its ill-typed condition into a new node. Only its elementary finite-sum composition motivates Step 3; the theorem cited there is 0GAC. The present item and its new dependency need no statement correction or new STATEMENT-DISPUTED flag.

## Review by Q94

I checked the item and the one new node with the source text open, using delivery-errors B-E as the content checklist. The new statement is self-contained: R_0,K_0, R,K, the graded isomorphism, all constants, the scalar factorizations and both quotient maps are introduced there. It has no proof sketch, proof steps or proof dependencies. Its three definition dependencies actually define Noetherian rings, associated graded rings and finite modules; I opened each statement. Source places use tags and labels, not unstable section numbers. The TeX is single-escaped after JSON decoding. The new node's source and the duplicate pairs above explain why this is neither an elementary bookkeeping fact nor a clause copied out of the item.

Step 1 uses the NEW NODE'S STATEMENT that D,q exist uniformly for the graded class. The citation quote is exactly that sentence. The arithmetic choice e=(D+2)c, N=max(q+e,2e+1) meets n>=c, both general bounds of 0GAC and its extra D=0 bound. No completion, restriction to proper ideals, fixed number of generators, or module-dependent bound is added. D,q are independent of c as the source requires; e,N may depend on c as the item permits.

Step 2 invokes no additional theorem: f_a=d and g_a=h_a give the stated finite-free factorization by the hypothesis h_a d=a id. This is direct substitution, including r=0. Lifting coefficients shows finite over R_n implies finite over R, so the source's wording of finiteness agrees. No identification of a merely projective module with a free module is being assumed.

Step 3 uses the NEW NODE'S STATEMENT for the finite set J, the a_j and psi_j, and its EXACT equality pu=sum mu_a psi. Its citation quotes that conclusion verbatim. I matched w=s and t=s+c. Defining V=sum psi_j h_a_j is an actual construction; evaluating Vd on m gives sum psi_j(a_j m)=sum a_j psi_j(m). This equality lives in K^s/K^(n+s), after applying lambda to the node's equality, not directly in K^t/K^(n+t). The statement never asks the new node for a common splitting d or an extension V, so there is no C4 use of its proof instead of its statement.

Step 4 is quotient arithmetic written out. Inclusion K^t subset K^s sends the relation ideal K^(n+t) into K^(n+s). Reduction from denominator n+s to 2s is defined because n>=s. On y, lambda mu_a is multiplication ay modulo K^(n+s); on x in K^n, beta lambda p is reduction modulo K^(2s). These formulas give vd=rho u. The R_n action is valid in all intermediate and final modules because K^n kills them: K^n K^s=K^(n+s) subset K^(2s). Thus there is no uncited comparison, change-of-rings theorem, or implicit transport. These elementary two-line quotient constructions were kept as a step, not new nodes. Every non-elementary input used in the assembly is the cited Hom-divisibility statement. The complete assembly is under 3000 characters; no individual step exceeds 2000.

I tested the boundary cases of BOTH statements. If c=0, the scalar 1 gives an actual splitting h_1 d=id, and v=u h_1 works with e=0; the intrinsic Hom-divisibility conclusion takes the single coefficient 1 and psi=u. If K=R (including the zero ring), all R/K^n modules for n>=1 and target quotients vanish. If K=0 and n>=1, the target quotients vanish too. At n=c=0 in the new node, R/K^0 is zero and all modules are zero; all exponent formulas remain nonnegative. Rank r=0 allows a nonzero M killed by K^c, rather than forcing M=0; the final composite still vanishes by the proved finite-sum calculation. As a concrete test take R=k[x], K=(x), n>=2c+1, M=(R/K^n)/(x^c), d=0: every value of u is divisible by x^(2n-c), and therefore reduces to zero at exponent 2n-4c when D=0,e=2c. The general new-node multiplication map is well-defined since c+(n+w)=n+t; its numerator inclusion is equality c+w=t. These checks also catch the incorrect temptation to compare psi_j and pu in a single quotient.

I corrected that potential quotient ambiguity explicitly by naming p, mu, lambda and beta and checking representatives; the item statement itself needed no change. There is no new source error beyond the inherited 0GAD typing issue noted above. All node citations have verbatim quotes in citations.json. The first server review_split check passed. The final required delivery dry run and push follow this report.
