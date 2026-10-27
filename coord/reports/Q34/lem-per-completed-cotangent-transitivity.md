# Q34: lem-per-completed-cotangent-transitivity

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-completed-cotangent-transitivity.json`: item, split into eight proof steps; not a Mathlib leaf.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-restricted-polynomial-first-order-calculus.json`: one new statement-only lemma, unsplit; no Mathlib match. It states continuous evaluation, substitution chain rule and Taylor modulo an ideal square, rather than presentation independence or the item's six-term conclusion.
- `citations.json`: one verbatim statement quotation per step/node citation.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id, completed cotangent/transitivity terms and restricted substitution/Taylor. No project declaration states the item or the new lemma. Ordinary polynomial Mathlib declarations are not project attachments.

## WANTED

None. All proof sources used are present in `literature/stacks-project/`.

## Corrections and scope

The mathematical statement is unchanged. The existing completed-conormal definition was added to statement dependencies because it supplies exactly the differential already spelled out in the statement. Existing metadata and the earlier searches were retained. The imported node had no proof; its source's “combining these presentations” and “reader verifies” diagram needed the completed quotient construction and explicit conormal ideal arithmetic.

The leftmost module is deliberately the kernel of the differential after termwise ordinary tensor, not the tensor of the original kernel. The conormal row need not be left injective. There is no flatness or etaleness hypothesis. No SGA source, Lean edit, compiler, Lake, repository write, or direct git command was used.

Read the chapter record and `sk-p-dl-a1-perverse` unit record. This is a supporting commutative-algebra input in the existing local-duality/Elkik branch of the affine-pushforward argument. It does not change the unit or chapter route. Read the current blueprint ancestor at `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.md`; the current snapshot is main-20261024. The inherited from/place/via records identify the finite-coefficient local-duality supporting branch. This is not the unit's key statement, so no unit realization fields were edited.

## Searches

Ran the required `batch2/msearch.py Q34 lem-per-completed-cotangent-transitivity` commands; the actual query/result records are preserved in `searches.jsonl` and copied into the relevant `mathlib_searches` arrays. For the item used LeanFinder for completed transitivity, Loogle `Algebra.H1Cotangent`, a completed/continuous cotangent grep, and LeanSearch for continuous Jacobi–Zariski. Its retained previous searches include the alternate continuous conormal/Jacobi–Zariski phrasing.

For the new lemma used two distinct LeanFinder phrasings (restricted substitution/Taylor and completed-polynomial evaluation), Loogle `MvPolynomial.pderiv`, two grep patterns, and LeanSearch for continuous evaluation and first-order Taylor. Read the results, including `AdicCompletion.evalₐ` (Algebra.lean:132, a quotient projection), `MvPolynomial.aeval_sumElim_pderiv_inl` (PDeriv.lean:155–165, an ordinary polynomial identity), and `MvPowerSeries.HasEval` (Evaluation.lean:67 onward, nilpotent/topological evaluation conditions). They do not give restricted substitution at arbitrary arguments or the completed Taylor claim. Read the JacobiZariski source: its generators are ordinary polynomial presentations, so it does not identify our completed complexes in one line. No service was unavailable in these searches.

Searched all DAG node statements and source places for 0ALM/0GAE/0AJR/0AJP/0AJQ, restricted polynomials, substitution, chain rule, Taylor, conormal exactness and completion tools. Used `tools/blueprint_refs.py ancestor` and whole-blueprint searches for cotangent, homotopy, Taylor, substitution, chain rule, restricted polynomial, first order Taylor and the source tags. No blueprint node states the new calculus lemma. Existing formal-transverse/Taylor nodes work over characteristic-zero fields with different formal topologies; the localized completed-polynomial lift lemma works over a field at a maximal ideal. Neither covers a general Noetherian base with arbitrary coefficient ideal and arbitrary evaluation arguments.

## Not duplicates

lem-per-restricted-polynomial-first-order-calculus vs lem-per-completed-cotangent-transitivity: the new statement is evaluation and differential/Taylor calculus for a single completed polynomial ring; it neither asserts presentation existence/independence nor any six-term sequence.

lem-per-restricted-polynomial-first-order-calculus vs lem-per-rig-etale-principal-tower-conormal-transfer: that node gives annihilation and reduction criteria for completed conormal homology, not substitution, chain rule or Taylor congruences.

lem-per-restricted-polynomial-first-order-calculus vs lem-per-completed-jacobian-homology-comparison: that node compares a finite-type polynomial presentation with its completion and its homology; it does not give completed substitution at arbitrary arguments or the Taylor identity.

lem-per-restricted-polynomial-first-order-calculus vs lem-sfb-completed-local-deformation-tangent: that is a deformation/lifting statement over a field for a completed local algebra; it does not state the general coefficient-ideal restricted-polynomial calculus here.

lem-per-restricted-polynomial-first-order-calculus vs def-per-completed-polynomial-conormal: that definition constructs continuous derivatives and the conormal differential; it does not assert substitution, the chain rule or the square-ideal Taylor congruence.

lem-per-restricted-polynomial-first-order-calculus vs lem-sfb-completed-polynomial-lift-calculus: the existing statement assumes a localized polynomial algebra over a field, its maximal-ideal completion and local maps; the new statement treats any Noetherian base, its coefficient ideal and arbitrary tuples in complete algebras.

lem-per-restricted-polynomial-first-order-calculus vs lem-trf-formal-transverse-shift-calculus: that statement concerns formal variable-adic power series over a characteristic-zero field and transverse shifts; the new statement permits arbitrary characteristic and an arbitrary coefficient-adic ideal.

## Review by Q34

I read restricted.tex Tags 0AJP (label lemma-topologically-finite-type), 0AJQ (lemma-topologically-finite-type-Noetherian), 0AJR (equation-NL), 0GAE (lemma-NL-up-to-homotopy), and 0ALM (lemma-exact-sequence-NL) with their proofs. Verified their tag/label pairs in `tags/tags`. For the new lemma I read 0GAE's substitution construction and final homotopy calculation, as well as algebra.tex lemma-NL-homotopy for the difference-of-lifts derivation. Its statement isolates the analytic-looking completed Taylor calculation without taking the item's presentation-independence clause as a black box. Its later proof can evaluate polynomial approximations modulo I^n, apply polynomial chain rule and first-order Taylor there, and pass to the limit. For the last congruence, D/H² is complete and separated by the existing finite-module completion theorem, so membership in H² is preserved in that limit. This proof guidance is kept here, not inserted into the unsplit statement.

For Step 1 I opened the cited completion-mod-ideal statement: it explicitly gives completeness of the completed ring for a finitely generated ideal. The Noetherian definition gives finite generation of I. The calculus node supplies extension of evaluation. The written successive-approximation construction proves surjectivity itself and checks compatibility of the polynomial classes; no uncited topological Nakayama theorem is being invoked.

For Step 2 I opened finite-type-algebra-noetherian and adic-completion-noetherian: they respectively cover the polynomial/quotient rings and their completion. B and C need no completeness of the original base A. I verified that finite type of C/IC over A/I gives finite type over B/IB using the same generators, so applying Step 1 over B is legitimate.

For Step 3 I checked both chain-map degrees against the calculus node's chain rule and Taylor formula. The target presentation ring is Noetherian by the same two permanence theorems, complete by completion-mod-ideal, and the ideal is its presentation kernel. For two lift choices the differences lie in that kernel. The signs give phi-phi'=h delta in degree -1 and delta h in degree 0. Composition and identities produce actual homotopy inverses. Tensoring these equations preserves them without asserting any kernel comparison. No separate node merely restates this clause of the item.

For Step 4 I opened all five cited statements. Finite-type permanence applies over the already Noetherian P to U=P[y]; the ideal JU is a finite U-module. Completion exactness explicitly applies to this short exact sequence of finite U-modules. The natural tensor-completion comparison explicitly identifies its completed image with JT. The I^n reduction comparison uses completion-mod-ideal for I^n and cofinality of powers; equality of the inverse-limit polynomial coordinates gives U-hat=T. This proves, rather than assumes, the combined presentation. Each claim here is the direct application or coordinate description of the cited statements, not an additional comparison lemma.

Step 5 is elementary ideal arithmetic: I checked the quotient J'=K/JT, its square, and both inclusions for the conormal row's image/kernel. No flatness is used and no left zero was added. Step 6 uses the exact existing derivative construction; reduction commutes with y differentiation because q fixes the y variables, while j has no y variables. Checking polynomial reductions proves the completed square commutes. The split finite-free row is written out, rather than delegated to a new node.

For Step 7 I read the module-category statement and the snake-lemma statement in full: the latter explicitly permits a merely right-exact upper row and requires a mono only in the lower row, precisely as here. Its final surjectivity add-on applies to the free projection. The explicit lift formula identifies the connecting map used. Step 8 proves the cokernel/tensor identification by inverse maps using the tensor definition node's universal relations; there is no unproved assertion about tensor preserving kernels. Transport to arbitrary presentations is by the explicit homotopies of Step 3. All cited statements were quoted verbatim in citations.json.

Small cases checked: I=0 gives ordinary polynomial presentations and the ordinary conormal snake sequence; I=A forces complete B and C to be zero; r=0 or s=0 gives zero free summands with the same row arguments. B=C and identity structure maps produce the expected zero relative complex up to the written homotopies. The calculus node allows non-nilpotent arguments (e.g. a variable evaluated at 1), which is essential for restricted rather than full formal power series, and uses no denominators, so characteristic p is allowed. Taylor at H=0 reduces to equality, at H=D the congruence is vacuous, and r=0 has empty sums. For the homotopy test f=x² the first-order error is (g-g')², correctly in the kernel square. No new node is elementary, a duplicate, or a restated clause. All proof steps are under 2000 characters.

Generic off-unit tools are declared in split_report.tool_uses: Noetherian completion/permanence, exact finite-module completion, tensor-completion comparison, modules abelian, and snake lemma. These are black-box algebra tools inside the already prescribed 0ALM route, not replacements for a unit step. The elementary diagram/conormal/cokernel arguments are retained in the item. No unfinished part remains in this one-level split; the new statement-only node is intentionally queued for its own later split.
