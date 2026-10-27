## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-torsion-separated-newton-correction.json`: the item, now split into four explicit elementary steps; statement and statement dependencies preserved.
- `citations.json`: one verbatim statement excerpt for each of the three step/dependency citation pairs.
- `searches.jsonl`: actual Q57 search-command records; the item also retains all inherited O3 search records.
- `report.md`: this report.

Attachments: none. A search of `lean/WeilConjectures/` for the exact blueprint tag and for Newton/torsion terminology found no declaration stating this item. The Newton identities for characteristic polynomials are unrelated. `Algebra.first_order_expansion` in `RingTheory/PopescuDesingularizationSubstitution.lean:30` is a private, proved first-order polynomial expansion, not a declaration of the entire item.

WANTED: Renée Elkik, *Solutions d'équations à coefficients dans un anneau hensélien*, I, Lemma 1, printed pp.555–558, especially equations (2)–(4) and the torsion intersection on pp.556–557; for lem-per-torsion-separated-newton-correction. Read online at https://www.numdam.org/item/10.24033/asens.1258.pdf on 2026-10-24; no archival copy found in the project's literature list.

WANTED: Ofer Gabber–Lorenzo Ramero, *Almost Ring Theory*, sixth release, (5.4.4), printed p.148 and Lemma 5.4.8, printed p.150; for lem-per-torsion-separated-newton-correction. Read online at https://pro.univ-lille.fr/fileadmin/user_upload/pages_pros/lorenzo_ramero/releaseLNM.pdf on 2026-10-24; no archival copy found in the project's literature list.

The item originally had no proof. Nothing was false or ill-typed in its statement. The point that needed explicit justification was cancellation: multiplication by t^h need not be injective on R. Step 3 instead constructs a specific difference inside t^(q-h)R, proves that t^h kills it, and uses exactly the stated separated-torsion assumption. No Noetherianity, completion, or finite generation of J was introduced. The proof is marked agent-written: the sources motivate it, but none is claimed to state this exact evaluated-scalar variant.

Unfinished work: none for this one-level split. There are no new statement nodes to put in the queue.

## New nodes

None; zero Mathlib leaves. The argument consists of ideal membership witnesses, ring identities, the supplied torsion hypothesis, and a finite distributive expansion. In particular neither the deep-torsion calculation nor the quadratic polynomial remainder is exported as an unnecessary auxiliary node.

## Searches and reuse

Read the item, its two definition dependencies, the chapter/unit records, the complete principal obstruction-lifting parent, and the nearby polynomial-calculus nodes. Whole-DAG searches for Taylor, first-order polynomial formulas, Newton correction, and separated torsion found `lem-per-completed-polynomial-taylor-evaluation`, `lem-per-restricted-polynomial-first-order-calculus`, and `lem-per-gabber-ramero-improve-precision`. The first two impose completion (and the second Noetherianity); the third assumes t is a non-zero-divisor and has a scalar splitting on the conormal module. None can be applied with the item's hypotheses. The finite polynomial expansion is written directly, as in Step 6 of the existing completed-polynomial proof, without citing that proof as though it were its statement.

Ran `tools/blueprint_refs.py search Taylor`, `search Newton`, `search 'torsion separated'`, and `ancestor lem-per-torsion-separated-newton-correction`. The Taylor hits concern power series or zeta functions, and the other two searches return zero blueprint nodes. The nearest imported ancestor remains `lem-per-artin-gabber-affine-curve`. Read its statement and proof in `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/`; its current Step 3 no longer contains the inherited formal-resolution branch. The existing provenance already records that fact. This split only supplies the finite correction needed by the recorded parent and makes no change to the unit, chapter or inherited creation chain.

The actual Mathlib queries are in `searches.jsonl` and verbatim in the appended item records: two differently phrased LeanFinder searches, LeanSearch, Loogle `MvPolynomial.pderiv, Ideal`, and two grep queries. Read all returned hits. Read `Mathlib/Dynamics/Newton.lean:48–105`, including `Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`: it needs a nilpotent error and a unit derivative for a single polynomial. The cotangent/Jacobian Loogle hits do not assert any correction existence. The PDeriv grep hits at lines 158 and 164 concern derivative/substitution compatibility. The Weierstrass hits concern one-variable power series and their completeness assumptions. None is an exact match or one-line specialization. One grep was directed at the single file `Dynamics/Newton.lean`; the search command consequently printed its line numbers in the file field. That raw result is retained exactly, and the actual file was read to assess it. No result was fabricated or silently normalized.

## Not duplicates

No new nodes, so there are no new/existing pairs sharing a Stacks tag. The existing completed-polynomial and non-zero-divisor Newton statements were read and were not copied into new nodes.

## Review by Q57

I read Elkik I, Lemma 1 on printed pp.555–558 online, in particular the one-step precision improvement before the limit argument, its Taylor formula on p.556, and the passage using the deep torsion intersection on p.557. Elkik assumes Noetherianity and completeness in that surrounding theorem; this item does not quote the whole theorem. Its finite construction only needs the explicitly given scalar identities and torsion bound. I also read Gabber–Ramero (5.4.4) and the surrounding scalar-factorization interpretation on p.148, and Lemma 5.4.8 on p.150, to check what the scalar identities encode. The proof neither asserts nor uses a derived obstruction-theory theorem. I read Stacks `restricted.tex`, Tag 0AK3, label `remark-linear-approximation`: it describes the quadratic error ideal and leaves the termwise expansion implicit. Our Step 4 gives that finite expansion explicitly for ordinary polynomials, so the completeness hypotheses of the Stacks remark are not used. There are no new nodes whose sources require separate checking.

Step 1 uses only the hypothesis g_i in J and the definition of membership in the principal ideal t^qR to select u_i. The same selected tuple defines a+ for all f; no f-dependent coordinate choice is hidden. The identities q=h+s and t^h t^s=t^q use h≤q, which follows from q>2h. All exponent differences are therefore nonnegative. This step requires no cited theorem.

Step 2 cites `def-weil-pbc-mv-polynomial-ring`. I opened its statement: its universal property explicitly identifies evaluation as an R-algebra homomorphism, so it supplies the multiplicativity/additivity used in the finite sum representing an element of J². The definition of J² is already given in the item's own statement. Each factor belongs to J, so its evaluated value really has a t^q witness. Substitution of G(a)=t^h and t^h v_i=g_i(a) then gives the displayed exact equality; it does not give an unjustified congruence after cancellation. The citation excerpt in `citations.json` is copied from the universal-property sentence of this dependency.

Step 3 cites no external lemma. For z_f=L_f-t^(2q-h)w_f, both summands belong to t^sR: q≥s, the v_i have that precision, and 2q-h≥s. Thus z_f belongs to t^cR because s≥c, and t^h z_f=0 by the exact equality of Step 2. This is precisely the hypothesis of the item with m=h. The conclusion L_f=t^(2q-h)w_f has at least the requested precision because 2q-h=2s+h. I checked that this is not cancellation in a quotient or cancellation of a possibly zero divisor.

Step 4 cites the same polynomial-ring definition for the finite monomial expansion and `def-weil-pbc-polynomial-partial-derivative` for its explicit monomial derivative. I opened both statements: the latter gives exactly the coefficient e_i and the convention that exponent-zero terms vanish. Expanding finitely many factors identifies the terms with zero, one, or at least two increments. Every term in the last class contains two elements of t^sR, hence lies in t^(2s)R; finite sums stay in that ideal. This is a few-line distributive calculation from the cited definitions, not an invocation of a Taylor theorem with unstated hypotheses. The second citation excerpt is the derivative definition's monomial formula. Combining with Step 3 proves every f-clause, and Step 1 already proves every coordinate clause.

I checked small cases d=0 (empty sums and zero remainder), J=0 (no error conditions), h=0 (t^h=1), t a unit (all parameter ideals are R), and t=0 (s,q>0, hence all evaluated errors and the increment are zero). A nonzero zero-divisor example is R=Z/8Z, t=2, c=3, h=1, q=4, J=(x), G=2 and g_1=2x; take a=0 and u_1=1, which is allowed since t^q=0. Then v_1=0, the correction stays zero, and the proof never cancels 2. Boundary s=c is allowed because the torsion hypothesis applies on t^cR itself. No positivity of h, domain property, characteristic restriction, or finite list of generators of J enters any step.

Against delivery-errors B–E: statements and notion dependencies are unchanged and self-contained; sources distinguish the exact agent adaptation from their more restrictive theorems; every citation has been read at statement level and quoted verbatim; no external non-elementary assertion is hidden behind a definition citation; no duplicate, clause-restatement node, cycle, or suppressed limit argument was introduced. All four steps are below 2000 characters. The corrected omission is the original absence of a proof, specifically the missing deep-difference argument that makes the torsion version valid. No statement correction was needed.
