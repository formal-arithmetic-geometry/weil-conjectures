# Q71: lem-trf-separable-monic-approximation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-separable-monic-approximation.json`: item, statement preserved, five proof steps, status split. Mathlib searches give no match.
- `dag/nodes/sec-trace-formula/lem-trf-polynomial-constant-shifts-finite-exceptions.json`: one new statement-only algebraic lemma, status unsplit, no Mathlib match. No proof or proof dependencies are put in this new node.
- `citations.json`: verbatim statements for every use in every item step.
- `report.md`: this report. `searches.jsonl` contains the actual msearch results; `write_split.py` is sandbox-only preparation code.

One new node; zero Mathlib leaves.

## Attachments

None. Searched the complete read-only slopmaster2 WeilConjectures source for the blueprint id and separable/monic/approximation combinations. The only monic-separable hits were unrelated residue-field lifting and strictly-henselian retractions. More focused constant-shift/critical-value searches also found no algebraic shift theorem. The read-only upstream master was also searched for the item wording; it gives no attachment and is not treated as evidence of a finished proof.

## WANTED

WANTED: Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Theorem 3.5.5 Step 3, printed p. 22, for lem-trf-separable-monic-approximation. The imported source path `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf` does not exist in this mirror, and the literature listing has no local Temkin PDF. No download or literature modification was performed. The item already calls its assertion an agent-supplied auxiliary lemma rather than a quotation of Temkin; its supplied proof remains explicitly agent-written.

## What was wrong or incomplete

The item was an unsplit, statement-only auxiliary lemma. Its statement is correct as written; no STATEMENT-DISPUTED or statement change is needed. The main trap is that nonzero derivative does not imply separability for an arbitrary reducible polynomial: for example, in characteristic zero, T^2(T-1) has nonzero derivative and is not separable. The proof therefore makes a further constant perturbation after arranging a nonzero derivative. It does not apply the irreducible-polynomial theorem without irreducibility.

Mathlib's existing monic coefficient approximation does not impose separability. I read Dense.lean:22–30, which explicitly lists separable approximation as missing, and Approximation.lean:132–137, whose theorem has only monicity, equal degree and coefficient bounds. The semantic hits separable_def, separable_def', separable_iff_derivative_ne_zero, separable_X_add_C, and separable contraction results were read against their hypotheses. None states finite exceptional shifts. Two independent semantic phrasings, two Loogle patterns, and Mathlib source grep results are retained verbatim in the search metadata. A grep restricted to the nonexistent directory FieldTheory/Separable returned no hits; it was supplemented by a successful grep of FieldTheory, which finds Separable.lean and confirms the actual candidates.

## Intended argument for the new unsplit node

This is a genuine algebraic lemma independent of topology or approximation, not a clause of the item. For h' nonzero, there are finitely many monic irreducible divisors of h' in the Euclidean ring F[T]. If h+b is not coprime to h', a monic irreducible divisor q of their gcd divides h+b. A fixed q can divide h+b for at most one b: if it also divides h+c, it divides the constant b-c, so b=c because q is a nonunit and any nonzero field constant is a unit. Consequently the exceptional constants inject into a finite set (choose a divisor for each), and are finite. This intended proof is recorded here only; the new node carries just its complete statement and is left to a later worker to split, including the factorization facts it needs.

Its source is explicitly an agent-supplied consequence using the coprime-to-derivative convention of Stacks 09H1 (fields-definition-separable), not a claim that Stacks separately states the finite-exception theorem. I read fields.tex:1124–1218, including the polynomial-ideal argument in 09H0 and the 09H1 definition, and checked the labels against tags/tags. The statement makes no appeal to the irreducible hypothesis of 09H0.

## Not duplicates

lem-trf-polynomial-constant-shifts-finite-exceptions vs def-pc-separable-polynomial: the existing node defines separability and formal derivative; the new node asserts finiteness of inseparable constant shifts under h' nonzero.

lem-trf-polynomial-constant-shifts-finite-exceptions vs lem-trf-irreducible-separable-derivative: the existing node assumes irreducibility and tests a single polynomial; the new one allows arbitrary reducible h, and asserts a finite exceptional subset as the constant varies.

lem-trf-polynomial-constant-shifts-finite-exceptions vs def-weil-pbc-separable-algebraic-extension: the existing node defines algebraic separable extensions and minimal polynomials, and does not assert finiteness of polynomial constant shifts.

lem-trf-polynomial-constant-shifts-finite-exceptions vs def-pc-field-tower: the existing node defines extension degrees and types of field extensions; it makes no finiteness assertion about inseparable constant shifts.

lem-trf-polynomial-constant-shifts-finite-exceptions vs def-weil-pbc-separable-field-extension: the existing node defines separably generated/general separable field extensions, not constant shifts of arbitrary polynomials.

lem-trf-polynomial-constant-shifts-finite-exceptions vs lem-trf-separable-monic-approximation: the item concerns arbitrarily small perturbations of a monic polynomial over a nontrivially valued field; the new lemma has no absolute value or approximation, assumes a nonzero derivative, and merely bounds the bad constants for that one polynomial. The steps of the item construct the perturbations and verify every approximation and degree clause.

I searched all DAG statements for separable plus derivative/perturbation/discriminant terms, the Stacks tag 09H1, and the full blueprint via blueprint_refs.py searches for separable, derivative, constant shift, and approximation. Existing distinct-linear-factor, irreducible derivative, and valuation perturbation-factor-selection statements do not imply the new lemma: the latter requires a separably closed field and a valuation residue condition, and is not a theorem about arbitrary h with h' nonzero. The blueprint searches found no statement-equivalent node, so same_as is empty for the item and new node. The new node's from.node and via list follow the reported nearest ancestor lem-trf-local-term-locality exactly.

## Review by Q71

I checked delivery-errors B–E against the actual JSON and the sources, not just the dependency lists. The item remains the imported density assertion without changing hypotheses or conclusions. I read the trace-formula chapter and sk-i-curve-zero unit, whose present route is the contracting-correspondence theorem. This pre-existing queued auxiliary is explicitly historical in its ancestry: splitting its elementary algebraic assertion does not change or replace that route, and no unit record is edited.

For step 1 I opened def-weil-polynomial-ring and def-pc-separable-polynomial. The former specifies coefficients and leading coefficient, which yield f=T+f_0 in degree one; the latter gives precisely the Bezout criterion and derivative formula used to exhibit 0*f+1*f'=1. Thus degree one is treated without changing the leading term, before any linear perturbation is attempted.

Step 2 uses only the stated absolute-value axioms and elementary real arithmetic. Nontriviality means an element with absolute value neither zero nor one; taking its inverse if necessary gives a positive value r<1. The displayed induction (1+c)^n >= 1+nc proves the required smallness directly, and strictly decreasing absolute values prove distinctness. Every finite forbidden set excludes only finitely many powers. No completeness, nonarchimedean convergence theorem, characteristic-zero claim, or uncited topological density lemma is used. This two-line Bernoulli estimate is kept as an elementary step rather than an artificial new node.

For step 3 I reopened both cited definition statements: derivative coefficients give (f+aT)'=f'+a, and the finitely supported coefficient description gives unchanged leading coefficient when d>=2. Subtracting two putative bad a values proves there is at most one. Step 2 then provides an arbitrarily small permissible a even when the original derivative is zero, as happens for T^p in characteristic p. Nonzero derivative is used here only as the hypothesis of the next cited lemma, never as a separability conclusion.

For step 4 I read the full new lemma statement and verified that it supplies exactly the finite subset B_h of bad constants. Its sole substantive hypothesis, h' nonzero, was proved in step 3. No irreducibility, monicity, infinitude, or characteristic hypothesis is smuggled into this algebraic citation. The finite-set avoidance argument already proved in step 2 supplies b with the needed strict bound, and the lemma then asserts separability of h+b. citations.json quotes that actual statement verbatim.

For step 5 the cited polynomial-ring statement supplies coefficientwise addition and the meaning of degree. I checked separately the constant coefficient b, linear coefficient a, coefficients 2 through d-1 (an empty range when d=2), the unchanged coefficient 1 at degree d, and all higher zero coefficients. The strict inequalities follow from the choices of a,b and epsilon>0, without any simultaneous-perturbation estimate or missing ultrametric argument.

I tested the new finite-exception statement on linear polynomials (derivative a nonzero constant, no exceptional shifts), on h=T^2 in characteristic not two (only b=0 is bad), and on h=T^p+aT with a nonzero in characteristic p (constant nonzero derivative, no bad shifts). The h' nonzero hypothesis cannot be dropped: over an infinite algebraically closed field of characteristic p, every T^p+b is a p-th power and inseparable. The statement is also valid for finite F, where the exceptional subset is automatically finite. The zero polynomial and all constant polynomials are excluded by h' nonzero. For the item, a trivially valued field would give a counterexample with f=T^2 and epsilon<=1; the required nontriviality is present. In positive characteristic the small-power construction works in F itself, without adjoining p-th roots or assuming perfection.

Every new node is statement-only, self-contained and searched; all used notions either have cited definition nodes or are defined inline. Every item's non-elementary inference is exactly the citation of the finite-exception lemma. All five steps are below 2000 characters and hide no additional comparison argument. There is no reverse dependency on the item from the new node, and the new node depends only on three existing definitions. No project or launcher file was written and no Lean/compiler/Lake tool was run. No mathematical work remains for this one-level split beyond the explicitly unsplit algebraic child.

## Checks and delivery

The required server dry run and final push are run after this report is written; their tool output is the authority for the delivery result.
