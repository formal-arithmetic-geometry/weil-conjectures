# Q126 stage-1 report: lem-sfb-additive-subgroup-perfect-decomposition

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-additive-subgroup-perfect-decomposition.json: split, six proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-primitive-frobenius-module-duality.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-skew-polynomial-cyclic-decomposition.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-finite-commutative-reduced-splitting.json: statement-only, unsplit; no Mathlib match.
- citations.json: full verbatim statements for every node used by every proof step.
- report.md; searches.jsonl and search-results.json preserve the actual searches and returned hits. Sandbox-only Python helpers wrote these files; none modifies the repository or launcher.

## Attachments

None. I searched the live WeilConjectures source for the exact blueprint tag, additive subgroup, elementary unipotent, alpha_p/alphaP, primitive Hopf and skew-polynomial terminology. The semilinear Frobenius file explicitly avoids the skew-module structure theorem, and the group-scheme sources do not give the requested classification or any of the three new lemmas. No sorry-free exact project declaration was found. No Lean was written or compiled.

## Literature

Read Milne, Algebraic Groups (2017), printed pp.292–299, especially 14.40–14.46, 14.50–14.53 and Exercise 14-3 on p.301, and pp.209–211, especially Proposition 11.3 and its proof. For the existing generic citations, read the Stacks affine-product lemma (schemes.tex, lemma-fibre-product-affine-schemes, Tag 01I4; lemma-fibre-product-affines, Tag 01JQ), the etale composition/base-change lemmas (morphisms.tex, lemma-composition-etale, Tag 02GN, and lemma-base-change-etale, Tag 02GO), and the quoted monic power-basis node. The latter is a Mathlib leaf, AdjoinRoot.powerBasis', read through its recorded exact statement and match. No SGA source is used.

WANTED: Berrick and Keating (2000), Theorem 3.3.6, for future splitting of lem-sfb-perfect-skew-polynomial-cyclic-decomposition; Milne 14.51 refers to this book. The current item uses the new statement-only corrected cyclic-module assertion, not an unstated theorem from that unavailable book.

## Source error

STATEMENT-DISPUTED: the printed Proposition 14.51 says that the cyclic factors have annihilators zero or irreducible. This is false even for k=F_p, sigma=id, and M=k[F]/(F^2). Every nonzero element of this module is killed by a power of F. If it were a direct sum of quotients by irreducible polynomials, those polynomials would all have to be F, and F would act by zero; but F times the class of 1 is the nonzero class of F. There is no free summand because M is finite-dimensional over k. The correct assertion needed by Milne's very next proof is finite decomposition into A/Ag for arbitrary g, allowing zero; the new cyclic-module node states exactly that. The item itself is true and its statement is byte-identical to the live statement. This is not a weakening of a project target.

Milne 14.52 also abbreviates the case of a polynomial having both a positive F-adic order and a nontrivial remaining factor. Our steps do not pretend every g is either a pure power of F or has nonzero constant term. They explicitly compute the identity component for arbitrary g, then use perfect-field reduced splitting. A quotient A/Ag is a left module, not a commutative quotient algebra.

## Blueprint and searches

Read the chapter and unit JSON records, then the newest literature/blueprint/latest (main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), its sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images statement and proof. The inherited chain supports direct-image preservation in clause (3). The current item is a supporting structural lemma, not the unit's key node; no unit realized fields changed. blueprint_refs.py ancestor returns None for this imported ancestry; retained null and the full inherited place/via chain, and added the exact local step served by every new node.

Searched the whole DAG by primitive functions/elements, 14.46, 14.51, skew/Ore polynomials, additive subgroup, connected-etale splitting, 11.3 and all proposed ids; searched the whole blueprint with blueprint_refs.py for additive subgroup, primitive, primitive elements, skew polynomial, cyclic modules, elementary unipotent, connected-etale/connected etale, 14.46, 14.51 and 11.3. No existing node states the new assertions. The blueprint Lang–Steinberg proof contains a cyclic-block argument over an algebraically closed field, but its node states surjectivity of F-1, not a cyclic decomposition theorem. A proof is not its node's statement and cannot serve as that citation.

Every new node has leanfinder, loogle, grep and leansearch queries actually executed using msearch.py, plus a second semantic phrasing. I read all returned hits, retained their original query strings and outputs in the node records and search-results.json, and inspected the skew-polynomial Basic.lean source. In particular SkewPolynomial and its module instances are definitions, not the structure theorem. Module.torsion_by_prime_power_decomposition and the PID structure theorem require a commutative ring, so cannot specialize to k_sigma[F] when sigma is nontrivial. HopfAlgCat, group-like elements and monoid Hopf algebras do not reconstruct primitive-generated group schemes. Abstract GroupExtension splittings do not prove the reduced-scheme subgroup or connected-etale splitting. Algebra.Etale.iff_exists_algEquiv_prod classifies algebras, not the group-scheme product. Repeated item searches also found only these unrelated general notions.

## Not duplicates

lem-sfb-perfect-finite-commutative-reduced-splitting vs lem-sfb-finite-commutative-group-local-constant-product: the existing statement assumes an algebraically closed field and identifies a constant factor from G(K); the new node works over any perfect field, with the potentially nonconstant finite etale reduced subgroup. An algebraic closure argument does not by itself descend a group-scheme isomorphism to k.

lem-sfb-perfect-finite-commutative-reduced-splitting vs lem-sfb-finite-group-scheme-primary-order: the existing statement counts prime-to-characteristic torsion of geometric rational points over an algebraically closed field; it asserts no group-scheme splitting over a perfect field. Both cite Milne 11.3 but use different conclusions.

lem-sfb-primitive-frobenius-module-duality vs lem-sfb-additive-subgroup-perfect-decomposition: the new node reconstructs arbitrary elementary groups in any positive-characteristic field from their primitive-function modules. It neither classifies these modules over perfect fields nor asserts any additive/infinitesimal/etale factors.

lem-sfb-perfect-skew-polynomial-cyclic-decomposition vs lem-sc-lang-steinberg: Lang–Steinberg states surjectivity of F-1 over an algebraically closed field. The new node is the cyclic-module theorem for all finitely generated modules over a possibly noncommutative ring over an arbitrary perfect field, including infinite-dimensional free modules. No existing statement provides this theorem.

## Review by Q126

I reviewed the split against B–E of delivery-errors.md with the actual statements open. Each new node introduces its own field and objects, defines the skew ring or the reduced/identity-component objects explicitly, cites its definition nodes, has an empty proof/proof_deps, and carries the correct chapter/unit and blueprint provenance. No new node is a clause of the classification: primitive reconstruction is the group-to-module bridge, cyclic decomposition is a ring/module theorem, and finite reduced splitting concerns all finite commutative groups and does not classify connected factors as alpha groups. These are independent mathematical inputs, not names for the answer.

Step 1 uses exactly primitive reconstruction's finite-generation and evaluation-isomorphism clauses. The closed embedding and finite-type hypotheses are present on H, and commutativity follows from coordinatewise addition. The lemma does not require smoothness, connectedness, or perfection, so nothing has been silently added.

Step 2 uses the cyclic-module node with the actual perfect field. The direct-sum/product passage is written out by restriction and summation on Hom_A; representability comes from reconstruction's statement, not from its proof. The empty module/sum gives the trivial group.

Step 3 uses reconstruction only to name U and the affine-spectrum, algebra-quotient and additive-group definitions for its explicit description. An A-map from A/Ag is determined by the image of 1 and annihilates Ag precisely when g annihilates that image. This proves the displayed kernel identification on every test algebra, including nonreduced algebras; it never replaces a scheme by its k-points. This definitional step is marked elementary, and the argument is actually supplied. I verified the zero polynomial gives Ga and a nonzero degree-zero skew polynomial gives a linear polynomial cT, hence the trivial group.

Step 4 uses monic-quotient-free exactly for the basis and dimension, the affine definition of finite morphism for finiteness, and affine spectra/quotient definitions for the explicit Bezout decomposition. It normalizes coefficients together, keeping the smallest and largest nonzero indices r and m. I checked the CRT inverse in both residue rings: uv is 1 modulo T^(p^r) and zero modulo u, while T^(p^r)w_1 has the opposite values. Their intersection is their product since their sum is 1. The first factor has the sole prime (T) and contains the identity; the second has no identity because u(0) is nonzero. This proves it is precisely the open-and-closed identity component, with the inherited additive Hopf operations. No general CRT or component theorem is silently invoked as a black box.

Step 5 uses precisely the new perfect-field splitting statement, applied only after K_g has been proved finite and commutative. It does not apply the algebraically closed-field node to k. The affine-product node identifies the tensor coordinate algebra. Over O(E_g), the monic-quotient basis gives p^r copies of that algebra, so the dimensions force rank p^(m-r), not just some unspecified p-power. There is no claim that E_g is constant.

Step 6 uses the exact existing etale base-change statement for the projection and clause (2) of etale-composition-cancellation for its composite with the second structure map. Both are Mathlib leaves. The affine-product statement gives the tensor coordinate algebra; tensor products of finite bases span and are independent by the dual coordinate functionals, an elementary linear-algebra argument written in the step. Thus the affine definition of finite applies and the rank is the product of the previous ranks. The identity scheme handles the empty product. Every uses entry has a verbatim full-statement quote in citations.json; proof_deps is their exact union. No off-unit non-Mathlib statement is used, so no tool-use exception is requested.

Small cases checked: n=0 and H=1; H=Ga^n; the nonsmooth connected H=alpha_(p^2), whose module exposes the printed 14.51 error; a separable kernel of T^p-cT (c nonzero) with r=0; and the mixed kernel of T^(p^2)-T^p with m=2,r=1, giving alpha_p times an etale rank-p factor. For primitive reconstruction, M=0, A, A/AF and A/A(F-1) give respectively 1, Ga, alpha_p and the constant F_p group. For finite reduced splitting, G=alpha_p and finite etale G give respectively a trivial reduced factor and a trivial identity component; commutativity is essential and explicitly assumed. The perfection hypothesis is used for the cyclic theorem and the reduced splitting only. Each step is under 2000 characters; no long step hides a separate lemma. The only actual source correction is the documented irreducibility error; all missing generic citations found in drafting were repaired by existing exact Mathlib leaves rather than new nodes.

## Unfinished work

None for this one-level split. The three new nodes intentionally remain statement-only for later stage-1 items. No implementation, compilation or stage-2 work was authorized or done.
