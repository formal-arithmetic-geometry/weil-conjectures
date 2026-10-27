## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-finite-support-monoid-denominator.json — existing statement item, now split into four elementary steps; whole-item Mathlib verdict: no match.
- citations.json — the verbatim statement quotation for the single cited node in step 1.

## New nodes

None. There are 0 new nodes and 0 Mathlib leaves. Each calculation fits in a few lines; a new difference-presentation or finite-denominator node would restate a clause of this item rather than split its proof.

## Attachments

None. Searched lean/WeilConjectures for the literal blueprint id and for AddMonoidAlgebra, MonoidAlgebra, subgroup/submonoid generation, common monomial denominators and common translates. No project declaration states all clauses. The Laurent-polynomial and common-localization-denominator hits concern particular monoids or already-established localizations, not this statement.

## WANTED

None. The ILO source PDF is present and was read at printed pp.103–104 (PDF pages 109–110).

## Source and blueprint audit

The statement is unchanged, as are its statement dependency, source, chapter, unit and inherited ancestry. No statement dispute was found. ILO VIII 3.2.4 describes the common dense torus S[P^gp]; the last sentence of the proof of VIII Lemma 3.2.9 uses the isomorphism on dense opens S[F^gp]. Neither passage prints the finite-support denominator computation. Accordingly proof_origin.by is agent: the four steps supply that omitted elementary algebra, rather than claiming to quote a printed proof. No normality, finiteness, torsion-freeness or saturation hypothesis of the surrounding geometric results is imported into this elementary assertion.

Read dag/chapters/sec-trace-formula.json and dag/units/sk-i-curve-zero.json, and the newest literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md, its .proof.md and the unit _section.md. The current blueprint uses Varshavsky's contracting-correspondence argument; this node's recorded historical branch passes through monoid-algebra domain/fraction and toric comparison. I preserve that ancestry and realize its common torus calculation only, without claiming that monoid denominators prove the current contracting theorem. The blueprint.from.place was already specific; same_as remains [] after whole-blueprint searches. Commands blueprint_refs.py search 'common monomial' and search 'finite-support-monoid' both returned 0 matches; ancestor identifies lem-trf-local-term-locality.

## Search audit

The sandbox initially had no item, report or searches.jsonl, only dispatcher markers. Copied the live item, retained its seven inherited searches, and added six actual Q127 searches recorded in searches.jsonl. Both LeanFinder phrasings, LeanSearch, Loogle and both greps completed successfully. All returned types were read. LeanSearch's IsLocalization.commonDenomOfFinset and related declarations require a localization instance that the item does not assume; proving the needed instance would be additional mathematical work and would still not establish the prescribed exponent formula by one-line specialization. Read Mathlib/RingTheory/Localization/Integer.lean, lines 76–151. Loogle's AddSubgroup.closure_toAddSubmonoid is generated from the multiplicative statement at Algebra/Group/Subgroup/Pointwise.lean, lines 104–115: it concerns closure of Q union -Q, not the finite common denominator. The monomial multiplication hit at Algebra/MonoidAlgebra/Defs.lean, lines 548–551 is exactly a stipulated defining rule, not a whole-item leaf. The second semantic search returned finite-type, support-span and ideal-membership lemmas, whose types also do not state the item. No service was unavailable. No Mathlib searches were performed by direct grep outside the required search command; direct source reads only inspected returned candidates.

## Not duplicates

No new nodes, hence no new/existing pairs to distinguish. Whole-DAG searches for common monomial, common translate and group-difference found this item and related geometric chart nodes rather than an existing replacement; no new lemma was introduced.

## Review by Q127

I read ILO VIII 3.2.4 and the full statement and proof of 3.2.9 on printed pp.103–104. The source uses group completions for the torus, but the calculation in this item works for any generating submonoid of any abelian group and any commutative ring. I checked that the statement actually defines the finite-sum monoid algebra, its multiplication and the map iota inline. The only definition imported from def-trf-fine-fan-blowup is its opening sentence fixing additive notation with identity 0; I opened that node and quote exactly that sentence in citations.json. None of its fineness, fan, sheaf, blowup or resolution assertions is used.

Step 1 cites precisely that additive-notation sentence. The argument does not cite it for the difference theorem: it proves the theorem directly. D contains 0 and Q, is closed under addition by (a-b)+(c-d)=(a+c)-(b+d), and under negation by -(a-b)=b-a. These are calculations in an abelian group. Thus D is a subgroup containing Q, so the generated-subgroup hypothesis forces D=G. The monomial identity then follows from the multiplication expressly given in the item. No group-completion comparison theorem is hidden here.

Step 2 uses the representations already established in step 1, no additional cited statement. Finite choice supplies one pair for each element of T. Closure of Q under finite sums puts b in Q. Separating the g-summand gives b+g=a_g+sum over T minus {g} of b_t, displaying every cancellation. The argument holds for every specified family of representations. It does not assume that Q is sharp, saturated, finitely generated or torsion free.

Step 3 uses only step 2 and the inline definitions of R[Q], R[G] and iota, no cited theorem. Every proposed exponent is explicitly in Q. Linearity of the basis map and distribution of multiplication over a finite sum give exactly iota(f)=sum c_g e^(b+g)=e^b F. This is not an unsupported appeal to 'clear denominators': the numerator and every exponent are written. The coefficients need not be nonzero, and T need not be the exact support of F. As translation in G is injective there is no ambiguity about exponents; even without using that observation, equal monomials are simply added in the finite sum.

Step 4 uses the definitions and the empty-sum convention, no external fact. For the empty T, b=0 and f=F=0; for every b the two products e^b e^(-b) and e^(-b) e^b both equal e^0=1. This also proves the unit assertion in the zero ring. There is no appeal to a fraction field or domain property.

I tested the hypotheses on Q={0}, G={0}; Q=G in a nontrivial finite torsion group; Q=N inside Z with negative exponents; and the nonsaturated submonoid generated by 2 and 3 in Z, where 1=3-2 and -1=2-3. For T={1,-1}, these latter choices give b=5 and translated exponents 6 and 4, both in Q. Empty T and singleton T (empty complementary sum) satisfy every displayed formula. Zero coefficients and the zero ring preserve the expansion. A noncommutative ambient group would break the addition rearrangement, but the item assumes an abelian group. No hypothesis was added or dropped and no false edge case was found.

Against delivery-errors B–E: no new statement-only/definition nodes or leaf records are needed (B1–B3, B5–B8); decoded TeX has ordinary single commands (B4); blueprint ancestry and whole-blueprint search are recorded (B9); no exact project attachment was found (B10). The sole citation quotes its statement, not its proof (C3–C4); all other inputs are inline definitions and displayed elementary calculations (C1–C2). No new dependency edge outside the existing definition is added, hence no off-unit tool or cycle is introduced (C5–C8). The actual proof remains in the item rather than in restated child clauses (D1–D3), and it constructs D and b before using them (D4); the source's omitted denominator details are precisely the displayed argument (D5). Hypotheses, empty sums, signs and coefficient-ring cases were checked as described above (E1–E7). All four steps are below 510 characters, so none triggers the long-step concern. I corrected no mathematical statement; the missing argument and its honest agent provenance were the substantive additions.

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler, Lake or build command was run. The required server dry run and push follow this report.
