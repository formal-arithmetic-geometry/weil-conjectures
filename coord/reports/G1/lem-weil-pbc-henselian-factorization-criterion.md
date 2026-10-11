## Worker report

The module states the Stacks Project Tag 09XI equivalence for a commutative ring `A` and ideal `I`, using Mathlib's `HenselianRing A I` as the dependency's henselian-pair notion. The first conjunct is (i) `I ≤ Ideal.jacobson ⊥`; the universal polynomial clause is (ii): `f` is monic, `g₀,h₀` are monic over `Polynomial (A ⧸ I)`, their product is the polynomial reduction `Polynomial.map (Ideal.Quotient.mk I) f`, and `Ideal.span {g₀,h₀} = ⊤` expresses generation of the unit ideal. The existential clause supplies monic `g,h : Polynomial A`, `f = g*h`, and both reduction equalities. The final implication is the node's “in particular” case, assuming the Jacobson-radical condition and equating henselianity with the factorization clause alone. The proof is `sorry` as required for stage 2.

Dependency used: `Sheaf.RingTheory.HenselianTerminology`, declaration `HenselianRing` (Mathlib declaration re-exported and recorded by `def-weil-pbc-henselian-terminology`). No other project declaration is needed.

Edge cases checked include arbitrary commutative (possibly zero) rings, arbitrary ideals including `⊥` and `⊤`, zero-degree monic polynomials, and the empty/degenerate quotient; no assumptions beyond the node's hypotheses were added.

Searches made: `msearch.py G1 lem-weil-pbc-henselian-factorization-criterion leanfinder "henselian pair iff every factorization of a monic polynomial modulo I lifts"` (no pair-level criterion); `msearch.py ... loogle "HenselianRing"` (only Mathlib's `HenselianRing` root-lifting class and local TFAE); `msearch.py ... grep "factorization.*henselian" Mathlib/RingTheory` (no matching criterion); `rg -n "Henselian|henselian" lean/Sheaf` (only the dependency module and unrelated applications). Thus no existing exact theorem was found.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, `A`, `I`, `f`, `g₀`, `h₀`, `g`, and `h` correspond exactly to the source objects. `Polynomial.map (Ideal.Quotient.mk I)` renders reduction modulo `I`; monicity, the product equation, and `Ideal.span {g₀,h₀} = ⊤` render every clause of the factorization hypothesis. The two reduction equalities and `f = g*h` render the conclusion. The final implication preserves the stated particular case. No mismatch was found.

## Second reading by G1

The node introduces a commutative ring `A`, an ideal `I`, and the henselian-pair
condition from `def-weil-pbc-henselian-terminology`; its conclusion has (i) the
Jacobson-radical inclusion, (ii) universal lifting of coprime monic factorizations
of reductions, and the stated particular-case implication. The theorem renders
these as `IsHenselianPair A I`, `I ≤ Ideal.jacobson ⊥`, the quantified monic
polynomials and `Ideal.span {g₀,h₀} = ⊤`, and monic lifts with both reduction
 equalities. Quantifiers and conjunctions match the node, including arbitrary
commutative rings, ideals, zero-degree polynomials, and degenerate quotients.

The first reading used Mathlib's `HenselianRing`, whose definition is simple-root
lifting and therefore does not render the dependency's idempotent-lifting notion.
I added the dependency module `Sheaf.RingTheory.HenselianPair`, defining
`IsHenselianPair` by unique lifting of every idempotent in `B/IB` for every finite
commutative `A`-algebra, and changed the theorem to use it. Searches with
LeanSearch, LeanFinder/Loogle, and grep of Mathlib, `WeilConjectures`, and
`lean/Sheaf` found no existing pair-level idempotent-lifting declaration or exact
factorization criterion. Both modules compile together; all proofs remain `sorry`.

## Dependency modules

`def-weil-pbc-henselian-terminology` had an unusable recorded declaration for
this use: Mathlib's `HenselianRing` is defined by simple-root lifting rather
than by the node's finite-algebra idempotent lifting. The delivered
`Sheaf.RingTheory.HenselianPair` states the node's pair notion exactly as
`IsHenselianPair`.

## Reviewer fix (R-hfc1101)

The dependency module `Sheaf.RingTheory.HenselianPair` (`IsHenselianPair`) is left out and
def-weil-pbc-henselian-terminology keeps its recorded notion, Mathlib's `HenselianRing A I`
(one definition per notion; landed citers J1/G1/E1 use it). The theorem is restated on
`HenselianRing A I`, with the landed sibling spellings `IsCoprime g₀ h₀` and
`f.map (Ideal.Quotient.mk I) = g₀ * h₀`. The delivered statement also parsed as
`P ↔ ((i ∧ ii) ∧ (i → (P ↔ ii)))` (`↔` binds looser than `∧`); the fix brackets
`(P ↔ (i ∧ ii)) ∧ (i → (P ↔ ii))`. The proof in words is added to the docstring.
