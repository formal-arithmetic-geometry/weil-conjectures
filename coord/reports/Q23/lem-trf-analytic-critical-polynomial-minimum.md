## Worker report

Item: lem-trf-analytic-critical-polynomial-minimum. Group Q23, stage 1 only, 2026-10-24.

Files written: the item's JSON in dag/nodes/sec-trace-formula/, the three statement-only nodes listed below in that directory, and this report. citations.json contains a verbatim statement quotation for every step/node citation. Searches and their actual service outputs are retained in searches.jsonl and search-*.txt. No Lean was written or compiled; the read clone and launcher scripts were not changed.

## New nodes

- lem-trf-critical-coset-infimum-calculus: statement, unsplit, no Mathlib match. Temkin's critical-coset subgroup, equivalence with unrestricted infimum, coefficient bound and translated representatives.
- lem-trf-analytic-frobenius-schauder-basis: statement, unsplit, no Mathlib match. Temkin Proposition 6.2.5, including the power-orthogonality conclusion; this is a structural basis theorem, not an attainment assertion.
- lem-trf-critical-coset-coefficient-normalization: statement, unsplit, no Mathlib match. A supplement reducing an arbitrary linear coefficient to 0 or 1 in a finite tame radical extension, with descent of an attained critical-coset norm. It applies to arbitrary complete extensions of k, independently of type or rational generation.

Attachments: none. Searches for the item's blueprint tag and for critical cosets/polynomials, Schauder and normalized-trace notions in lean/WeilConjectures found no declaration stating this item or the new supporting assertions. The unrelated normalized cohomological traces were read as unrelated hits, not attachments.

WANTED: local copy literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, Lemma 6.1.2 and Propositions 6.2.4--6.2.5, for lem-trf-analytic-critical-polynomial-minimum and its three new nodes. The named PDF is absent from this read clone. I read the cited 60-page arXiv v3 directly at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (printed pp. 37--38, 42--44, 47), without downloading or writing literature files. In accordance with the missing-local-document rule, proof_origin.by is agent. The source distinctions and the supplementary argument are recorded explicitly.

The item statement was retained in full. No statement dispute or change of hypotheses was required. In particular arbitrary a in L, both type alternatives, and the finite tame extension remain. No stability theorem is cited: the parent analytic-type23-stability depends on this item and would create a cycle.

## Source error

The first paragraph of the printed proof of Proposition 6.2.4, p. 47, uses its k-Schauder basis to subtract a term of the form q-a q^(1/p), and later claims that a constant b_0 can be written d^p-a d with d in k because k is algebraically closed. These assertions need a in k; the critical-coset definition on p. 37 allows a in the whole analytic field. The issue is a missing reduction in that proof, not a counterexample to the proposition. For a concrete failed inference take an equal-characteristic-p Gauss field over algebraically closed k, a=T and b_0=1. No d in k satisfies d^p-Td=1: comparing the coefficient of T forces d=0, contradicting the constant coefficient. Likewise multiplication by T need not lower the Frobenius level of a basis term. This example diagnoses that local inference, without claiming the triple defines a critical coset.

The normalization supplement repairs exactly this issue. If a is nonzero, adjoin alpha with alpha^(p-1)=a, and divide values by alpha^p. All (p-1)-st roots of unity already lie in k. Thus E=F(alpha) is a splitting field of the separable polynomial X^(p-1)-a, and its Galois group embeds into the cyclic group of (p-1)-st roots of unity. Its degree n divides p-1. The finite-extension calculus then makes it tame: the defect, an inseparable residue degree and wild ramification indices have p-power factors, whereas n is prime to p. The new coefficient is 1 and the new threshold is t=s/|alpha|^p. The a=0 case uses E=F, alpha=1.

Here are the missing descent details for the new normalization node, for its future splitter. Put T_E/F(x)=Tr_E/F(x)/n. Uniqueness of the extended absolute value makes every conjugate isometric, hence |T_E/F(x)|<=|x|. The multinomial expansion of a sum of p-th powers, together with n^(p-1)=1 modulo p, gives

|T_E/F(x)^p-T_E/F(x^p)| <= |p| |x|^p.

In equal characteristic p this is an exact equality to zero. Therefore if |p x^p|<s and |e|<s, linearity gives

T_E/F(b+x^p-a x+e)=b+T_E/F(x)^p-a T_E/F(x)+e',

where |e'|<s and |p T_E/F(x)^p|<s. Consequently normalized trace maps the extended critical coset into the original one. The extended coset has no element of norm <s, since its trace would yield such an element in the original nonsplit coset. Its infimum is s because it contains the original coset. A member of norm s descends by trace to a member of norm at most s; nonsplitting forces equality. Scaling x=alpha y identifies this extended coset with alpha^p times the normalized one. This proves the supplement's criticality and attainment-descent clauses without asserting the existence of a minimum on any field. The argument belongs here in the report; the new node itself contains no proof.

## Searches and reuse

Before creating nodes I searched all dag/nodes by critical coset, critical polynomial, Schauder, normalized trace, 6.1.2 and 6.2.5, and ran tools/blueprint_refs.py search for critical, Schauder, normalized trace, coset and Kummer. The blueprint hits concern base-change injectivity, sheaf traces or Kummer sheaves, not valued critical cosets. No imported blueprint statement matched. The ancestor command identifies lem-trf-local-term-locality; every new node records this ancestor, the item prepended to its via list and the precise Temkin proof component within the semistable-alteration branch. I read the latest blueprint's lem-trf-local-term-locality.md, the chapter and sk-i-curve-zero unit records and SETUP's three-level route. This delivery supplies a component of the already recorded analytic-stability/semistable-modification route and changes neither chapter nor unit.

Each new node has its own statement-oriented LeanFinder and LeanSearch phrasing, a Loogle query and a logged Mathlib grep. I read all hits. Schauder searches return the general basis framework in Analysis/Normed/Module/Bases.lean, Hilbert bases and ordinary field bases; none constructs Frobenius chains or power-orthogonality for these fields. Critical-coset searches return p-adic Hensel, root bounds and proper-space polynomial minima; none asserts the nondiscrete complete-field calculus. Normalization searches return Algebra.normalizedTrace and trace identities. I opened FieldTheory/NormalizedTrace.lean (its construction of the linear map assumes CharZero, after line 69) and the basis source (opening through its structure): neither supplies the mixed/equal characteristic valued estimate or critical-coset descent. The malformed initial Loogle query Algebra.trace, pow reported unknown identifier pow; I replaced it by the successful Algebra.trace query. The record uses that successful query and does not call the malformed query evidence of absence.

## Not duplicates

lem-trf-critical-coset-infimum-calculus vs lem-trf-analytic-prime-coset-model: the latter constructs a special coset for an immediate degree-p extension; it does not give the equivalence, bound for arbitrary a, or subgroup/translation calculus used here.

lem-trf-critical-coset-infimum-calculus vs lem-trf-analytic-coset-generator-reduction: the latter gives a generator from a special coset in an immediate rational field, not the general critical-coset calculus.

lem-trf-analytic-frobenius-schauder-basis vs lem-trf-finite-ultrametric-almost-orthogonal-basis: the latter is a finite-dimensional r-orthogonal basis for r<1; it has neither an exact Schauder basis over k nor iterated Frobenius powers nor orthogonality to all p-th powers.

lem-trf-critical-coset-coefficient-normalization vs lem-trf-valued-finite-ramification-calculus: that existing node gives tame-extension invariant calculus, but no coefficient scaling, trace error estimate, criticality or minimum descent. It is reused separately for completeness and tame composition.

None of the new source records cites a Stacks tag, since these assertions are from Temkin and the stated agent supplement, rather than a Stacks theorem. No SGA source is used.

## Review by Q23

I read the online source's definitions immediately preceding Lemma 6.1.2 and both parts of that lemma, rather than treating the restricted c-infimum and the unrestricted polynomial infimum as interchangeable by definition. The calculus node states the equivalence, coefficient bound, subgroup and translation facts that Steps 1--6 actually need. Every representative of a critical coset is a base point for the same coset, so the translated versions are consequences of the exact source statements, not an additional attainment theorem.

For the basis node I read Proposition 6.2.5 on printed p. 43, its type-3 discussion and the type-2 residue-lifting continuation on pp. 43--44. I checked that the hypothesis is finite moderately ramified over the original completed rational type-2/3 field, not merely an arbitrary finite analytic extension. Its definition of orthogonal Schauder basis gives convergent finite approximations and exact maximal-term bounds. Its final inequality is for every p-th power in L; replacing it by linear independence or an r<1 bound would not justify Step 6. The statement includes that exact inequality.

For Step 1 I opened lem-trf-valued-finite-ramification-calculus and used its sentence on completeness of finite extensions. I checked nondiscreteness directly inside k by extracting all positive integral roots of a nonunit, so no spherical completeness, local compactness or discretely valued hypothesis was smuggled in. The critical-coset calculus then applies under exactly the positive infimum and |pb|<s hypotheses of the item.

For Step 2 I checked every clause of the new normalization statement: it supplies a complete finite tame extension, a coefficient A in the scalar field, a critical normalized coset and descent of a minimum. I checked tame composition against the existing ramification-calculus statement before applying the basis node to E/K. This retains the original rational base K and does not replace it by k(alpha), or invoke the stability theorem being proved above the item. The calculus supplies the bound on A and the |pv|<t invariant for all representatives.

Step 3 uses precisely convergence and exact norm bounds from the basis statement; changing B by an error smaller than t is in the coset by its displayed definition. Step 4 is a finite descending induction in the highest Frobenius level; at each iteration the subgroup/translation clause preserves criticality and the |pv| bound, while orthogonality bounds the term being removed. The scalar A now lies in k, which is essential to lowering the level. I wrote the induction and admissibility instead of merely saying improve the representative.

Step 5 needs algebraic closedness only for a polynomial with all coefficients in k, now guaranteed by normalization. I checked admissibility of the root explicitly: its p-th power is bounded by max(|b_0|,t), so |p d^p|<t. Step 6 uses the coefficient bound to show that any strict improvement of a representative of norm greater than t would already improve its norm by adding a p-th power. The exact power-orthogonality inequality rules that out. The last removal of e with |e|<s is elementary ultrametric arithmetic and gives an actual polynomial value, not merely a minimum of the enlarged coset. The citations file quotes each used node's statement verbatim, including the whole useful clauses of the new nodes.

I checked small cases a=0 (no radical extension), p=2 (the radical degree divides 1), L=K, both type alternatives, equal characteristic p (all p-error bounds are zero), and mixed characteristic (all p-error bounds remain strictly below the threshold). The impossible case b=0 has s=0 and so is excluded by the original hypothesis, not an added condition. An empty finite support is permitted; it would give the zero representative after constant removal, contradicting criticality, so the algorithm cannot finish at zero. No degree-p radical is adjoined. No new node restates the desired minimum theorem: the basis is structural, the calculus has no attainment conclusion, and normalization only transfers an already attained minimum between fields. All new nodes are unsplit with no proof or proof_deps. The routine finite reduction and the final two inequalities stay in the item's steps instead of becoming redundant nodes. Every step is shorter than 2000 characters.

Corrections made during this reading: I inserted coefficient normalization and trace descent to repair the source's arbitrary-coefficient gap; wrote out constant-root admissibility; retained the enlarged-coset-to-polynomial conversion at the end; and ruled out the tempting circular citation of analytic-type23-stability. Nothing remains unfinished in this one-level split. The three new statements are intentionally left for their own subsequent stage-1 splits.

Final form check: all new coset statements now explicitly quantify b in F, and the normalization statement explicitly extends the S-notation to valued extension fields. I also removed doubled TeX backslashes from the item proof texts. The server preflight passed before these final clarity/formatting fixes; the final dry run is repeated on the exact delivered files.
