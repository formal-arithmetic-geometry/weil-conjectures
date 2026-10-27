## Worker report

Files written, under dag/nodes/sec-six-functors-basics/:

- lem-sfb-restricted-pbw-basis.json: statement unchanged; seven-step split following Milne 10.40.
- lem-sfb-field-filtered-pbw.json: statement-only input, ordinary PBW over any field with the word-length filtration; Mathlib no match.
- Reused lem-sfb-associative-jacobson-identities from the current DAG (Q52); its file is not delivered or modified. The returned Q50 version is retained outside dag/ as returned-associative-jacobson-identities.json.txt for comparison.

Attachments: none. I searched lean/WeilConjectures for the item id, restricted enveloping, PBW, Poincare/Birkhoff and Jacobson formulas. No declaration states the item. The library's unrelated Jacobson-space and Jacobson-Noether declarations are not attachments. No Lean files were written or compiled.

WANTED: none. The needed source, Milne, Algebraic Groups (2017), is present in literature/milne-algebraic-groups_iAG2017.pdf.

The imported item had no proof. It already explicitly assumes all three restricted axioms and correctly includes all s_i for 1 <= i < p. No statement correction is needed. Its arbitrary-field and arbitrary-ordered-basis hypotheses are retained. In particular the p-map need not vanish, the field need not be perfect, and the Lie algebra need not be nilpotent.

The blueprint ancestor command reports None for this pre-existing deep created-node chain. I preserved its null ancestor and precise inherited place and prepended the item to the new nodes' via lists, rather than assigning an invented blueprint ancestor. The latest blueprint unit text and the chapter/unit records were read. This is the existing restricted-enveloping input below the direct-image/alteration/Kempf route, not a replacement of that route. No SGA reference occurs. No off-unit theorem is used: both inputs have the item's unit; field and Lie algebra notions are existing definitions.

Nothing remains mathematically unfinished in the item's split. The one new filtered-PBW statement deliberately remains unsplit; its later proof can follow Milne 10.36. The reused Jacobson statement is likewise unsplit in the live DAG; no claim is made that either input is already formalized.

## Searches and existing nodes

Before creating either node I searched the entire DAG for PBW, Poincare/Birkhoff, restricted enveloping, Jacobson formulas/identities, ordered-basis Lie-algebra assertions and Milne 10.36/10.38. I read the statements of rational-pbw, kostant-integral-pbw, enveloping-universal-property, verma-monomial-weight-basis, restricted-pbw-top-pairing and connected-finite-order. The blueprint search commands for PBW, Poincar, Birkhoff, Jacobson, p-Lie and enveloping found no matching blueprint statement. A direct search of literature/blueprint/latest found only the uses of restricted PBW in the connected-finite-order proof; its statement is about the order of a group scheme, not this input.

All Mathlib queries in the new nodes were executed using msearch.py, with their exact tool/query and output digest copied from searches.jsonl. Each input has LeanFinder searches with two phrasings, Loogle, LeanSearch and grep. The item has fresh searches in addition to its retained earlier records. Searches succeeded; none was silently recorded as unavailable or vice versa.

I read Mathlib/Algebra/Lie/UniversalEnveloping.lean:46--100, which constructs the ordinary quotient and its Lie map and lift; it contains no PBW basis theorem. I read Algebra/Lie/Free.lean:36--44, whose alternative construction expressly needs PBW; its free-Lie enveloping equivalence is not a basis theorem for arbitrary L. LinearAlgebra/SymmetricAlgebra/Basis.lean:74 gives the symmetric-algebra basis, without identifying that algebra with the associated graded of U(L). For the Jacobson input I read Algebra/Lie/OfAssociative.lean:304--324: ad_pow_lie is the iterated derivation rule for a bracket and does not state either requested Jacobson identity. Algebra/CharP/Lemmas.lean:111--145 requires Commute for the noncommutative-ring binomial theorem. It cannot be used on arbitrary a,b. The Geck/root-system and polynomial basis hits likewise do not supply either input.

## Not duplicates

lem-sfb-field-filtered-pbw vs lem-sfb-rational-pbw: the existing statement only concerns Lie algebras over Q. The new statement covers arbitrary fields, in particular the prime-characteristic field needed here; the existing result cannot specialize to characteristic p.

lem-sfb-field-filtered-pbw vs lem-sfb-kostant-integral-pbw: Kostant's statement is an integral divided-power form inside a split semisimple rational enveloping algebra; it does not cover an arbitrary Lie algebra over a positive-characteristic field or an arbitrary ordered vector-space basis.

lem-sfb-field-filtered-pbw vs lem-sfb-verma-monomial-weight-basis: the latter is a basis of a rational semisimple highest-weight module after a left-ideal quotient, not ordinary PBW for U(L) over any field.

lem-sfb-field-filtered-pbw vs lem-sfb-enveloping-universal-property: the latter is a rational universal property, with no assertion of linear independence or the degree filtration.

lem-sfb-field-filtered-pbw vs lem-sfb-restricted-pbw-basis: the new lemma concerns the ordinary quotient by bracket relations, has unbounded exponents, and assumes no restricted operation. The item proves the additional p-quotient and basis-generator presentation by its own semilinearity, centrality and triangular arguments.

lem-sfb-field-filtered-pbw vs lem-sfb-restricted-pbw-top-pairing: the existing node assumes an algebraic group and Borel radical, takes a restricted quotient, and asserts a top-coefficient pairing. It supplies no ordinary PBW statement in the generality required.

lem-sfb-associative-jacobson-identities vs lem-sfb-restricted-pbw-basis: the new lemma is a universal identity in any associative algebra, with no quotient, ordered basis or restricted operation. It supplies the non-elementary cancellation/adjoint formulas, while the item proves the ideal-generation and basis conclusions.

lem-sfb-associative-jacobson-identities vs lem-sc-connected-finite-order: the existing node's statement only gives the order of a finite connected group scheme. Its proof's reference to restricted PBW is not a reusable Jacobson identity in its statement.

## Source error

I visually checked the PDF's printed pp.204 and 206 as well as reading the text of pp.200--207. Milne's definition of s_r on p.204 has the minus sign -1/r in front of the iterated-adjoint sum ending in the second argument. The new node's positive 1/i coefficient convention ending in the first argument is equivalent: take the coefficient of t^i in ad(ta+b)^(p-1)(ta+b)=0. The two coefficient sums are negatives, exactly matching Milne's minus sign. I corrected an initially imprecise source-place explanation to make this sign explicit; the mathematical statement did not change.

Definition 10.39(c), printed p.206, has the typographical upper bound 0 < r < p-1, whereas Proposition 10.38(b) on p.205 has the correct 0 < r < p. The former would omit s_(p-1). For p=2, take a=E12 and b=E21 in M_2(F_2). Then a^2=b^2=0, but (a+b)^2=I and s_1(a,b)=[a,b]=I. Thus the shortened sum is false. The item's existing complete sum 1 <= i < p is correct, agrees with 10.38, and is retained. This is a source typo, not a dispute with the item.

## Review by Q50

I read Milne Theorem 10.40 on printed p.207 and Definition 10.39 on p.206 against every hypothesis and both conclusions of the item. Milne's theorem allows arbitrary ordered bases (indeed arbitrary dimension), so the finite-dimensional restriction is harmless and the statement's chosen finite basis has exactly the asserted range. The proof's central c_i generate the kernel and its mixed monomials have exponents less than p in the e_i and unrestricted in the c_i. I expanded those two compressed arguments instead of referring to them as standard. I also read Theorem 10.36 and its reduction proof on pp.200--204 for the new PBW node, and Proposition 10.38 with its definition of s_r and proof on pp.204--206 for the reused Jacobson node. These are the actual sources, not Stacks results; no Stacks tag is claimed for them.

For step 1, the quoted filtered-PBW statement gives exactly the basis and the basis in each word-length subspace. Its hypotheses are a field, a finite-dimensional Lie algebra and any ordered basis, all present here; no characteristic-zero condition occurs. The preceding equality r(x,y)=sum a_i b_j r(e_i,e_j) is merely bilinearity, written explicitly, and needs no separate node. Concatenation proves multiplicativity of the filtration directly.

For step 2, the quoted Jacobson node gives the full noncommuting sum identity with precisely the same coefficient-defined s_i as the item. Linearity and bracket preservation of j preserve these coefficients, so the two sums cancel term by term. The restricted scalar axiom gives the Frobenius semilinearity. The resulting c(sum a_i e_i)=sum a_i^p c_i proves generation of the p-ideal; it never takes p-th roots of a_i, so an imperfect base field is permitted. The mutual tensor-quotient maps are specified and their composites fix every tensor generator.

For step 3, the same quoted node explicitly gives [a^p,b]=ad(a)^p(b). Iterating bracket preservation of j and using the item's adjoint axiom gives the displayed zero commutator. The product commutator identity then extends it to every word. This supplies genuine centrality in all of U, not merely commutation with the chosen basis.

For step 4, the filtered-PBW quote provides the precise lower-degree expansion that the argument takes. The only other operations are expansion of products and the defining swap relation. Every replacement of E_i^p by j(e_i^[p]) lowers word length by p-1, which is positive even at p=2. Every swap introduces one bracket of degree one in place of two factors. Hence no omitted term can retain degree D. Division with remainder gives distinct leading monomials for distinct (a,b), independently of the ordering of the basis.

For step 5, the filtered-basis clause, not merely an ordinary basis declaration, is what ensures independence modulo U_(<=D-1). I checked the induction includes |m|=0 and has strictly smaller degree in its recursive terms. A putative dependence has finite support, hence a largest degree, so this argument does not require completeness or an infinite triangular-matrix theorem. This is the elementary change-of-basis argument spelled out for the specific family, not a hidden new input.

For step 6, the prior centrality and mixed basis are already established in this same proof. The formula B_(a,b)c_i=B_(a,b+delta_i) explicitly identifies I with a coordinate subspace; the complementary coordinate vectors then give both spanning and independence in the quotient. No external exactness or polynomial-freeness theorem is being assumed. For step 7, the quotient relation calculation of step 2 and bilinearity of step 1 show both inclusions of the defining ideals. This proves the presentation clause rather than moving it to a new node. The zero-dimensional calculation uses the scalar axiom to get 0^[p]=0 and leaves the nonzero field and its vector 1.

Small cases: the ordinary PBW node gives F for L=0 and F[X] for a one-dimensional abelian L, in every characteristic, including 2. For a one-dimensional restricted L with e^[p]=lambda e, the item gives F[X]/(X^p-lambda X) with basis 1,...,X^(p-1); lambda need not be zero. The Jacobson sum is the usual commutative p-power identity when a,b commute; at p=2 it becomes (a+b)^2=a^2+b^2+[a,b], verified by expansion, and p=3 retains both s_1 and s_2. Noncommuting matrix units detect the missing-term source typo above. These cases test zero dimension, arbitrary p-map, the smallest prime, and noncommutativity.

B1--B7: both input statements introduce every object, define their tensor quotient or coefficient polynomials inline, use TeX, cite actual document places, have empty proof/proof_deps, and use existing field/Lie definition nodes. No new node is an elementary few-line auxiliary, a clause of the restricted theorem, or a duplicate. C1/C4: every non-elementary fact taken externally is a statement of one of the two cited nodes; citations.json contains verbatim statement excerpts for every use. Internal references to earlier steps do not assert new external lemmas. D1--D5: the item carries the semilinearity, centrality, triangular, induction and ideal arguments; neither input restates its result. E1--E6: all field, prime-characteristic, dimension, filtration and bracket hypotheses were checked at their application, with the explicit cases above. Each step is below 800 characters, so none crosses the 2000-character review threshold. I corrected the source-sign explanation during self-review and retained the exact original item statement.


## Repair of returned delivery

The retained ready record identifies the returned delivery as a7d8d288ad4. I compared its three retained node files with the current read clone and the first required dry run rebased them onto server head 7d75581dd2837c4683a232ce0f2465294f562928. It reproduced the landing failure: the Jacobson file would modify an existing node. The item on the current DAG still has the same statement and statement dependencies and no proof. The filtered-PBW id is absent on the current DAG. The colliding Jacobson node is now owned by Q52, created for lem-sfb-restricted-rational-differentiation, with different provenance and wording.

I resolved the requested name collision by reusing that current node and withdrawing the duplicate Q50 file from the delivery. A mere rename would duplicate the existing statement, contrary to stage 1 section 2 (Duplicates). No mathematical distinction could honestly be entered under Not duplicates. The original returned file is archived in the sandbox outside dag/; no existing repository node is changed. This reduces the delivery from two new nodes to one. The item's statement, dependency ids and seven proof arguments are preserved; split_report now records the rebase and reuse, and citations.json quotes the current node verbatim.

I re-read the entire current Jacobson statement. It has precisely a field of prime characteristic, an arbitrary unital associative algebra, the central-indeterminate coefficient definition, both the p-power sum identity and the equality ad(a)^p=ad(a^p). Step 2 uses its sum identity in U and transports the same coefficient polynomials through j. Step 3 evaluates its endomorphism equality at j(y), giving [j(x)^p,j(y)]=ad(j(x))^p(j(y)); this is exactly the pointwise form previously quoted. No perfectness, finite dimension, or commutativity is added. Both uses remain valid without changing the arguments. Its empty proof dependencies cannot introduce a cycle through the item. Its field definition was also re-read, as was the Lie algebra definition used by the item and the new PBW input. The existing Jacobson node has the same unit as the item.

I retained and read the original Mathlib search log rather than repeating unchanged search questions. I checked the new PBW statement against Milne Theorem 10.36 and the item against Theorem 10.40, including n=0, p=2, the nonzero one-dimensional p-map, and the characteristic-free filtration argument. All five external proof citations now have exact statement substrings in citations.json. The seven steps are all shorter than 2000 characters. The historical sections above describe the original two-input search and review; only filtered-PBW remains a new node in this repaired delivery.
