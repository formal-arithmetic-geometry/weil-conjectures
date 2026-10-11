## Worker report

The module `lean/Sheaf/RingTheory/GRingMaximalIdealCriterion.lean` states
`isGRing_iff_maximalIdeal`. It imports `Sheaf.RingTheory.GRing`, using the dependency
`def-weil-pbc-g-ring` declaration `IsGRing`, and Mathlib's `IsNoetherianRing`,
`Ideal.IsMaximal`, `Localization.AtPrime`, `AdicCompletion`, and
`IsLocalRing.maximalIdeal` for the other dependency notions.

The theorem has the node's Noetherian hypothesis as the explicit typeclass
`[IsNoetherianRing R]`, together with `[CommRing R]`. Its left clause is exactly
`IsGRing R`. Its right clause quantifies every maximal ideal `m : Ideal R` via
`[m.IsMaximal]`, localizes at `m` using `Localization.AtPrime m`, and states that
the canonical map into the adic completion at the localization's maximal ideal is
`RingHom.IsRegular`:
`algebraMap (Localization.AtPrime m)
(AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
(Localization.AtPrime m))`.
The biconditional renders the “if and only if” in the node statement.

Dependencies used:

* `def-weil-pbc-noetherian-ring`: Mathlib `IsNoetherianRing`.
* `def-weil-pbc-g-ring`: `Sheaf.RingTheory.GRing.IsGRing`.
* `def-weil-pbc-localization-at-prime`: Mathlib `Localization.AtPrime` and
  `Ideal.IsMaximal` (whose localization carries the local structure).
* `def-weil-pbc-adic-completion`: Mathlib `AdicCompletion` and its canonical
  `algebraMap`.

Edge cases checked: maximal ideals are represented by the typeclass binder used
throughout the project; for a field the quantifier specializes to its unique
maximal ideal, while for a ring with no maximal ideals the right side is vacuous,
as required by the literal universal statement. The Noetherian assumption is kept
as a typeclass exactly as in the opening sentence and is not duplicated in the
conclusion.

Searches made: `msearch.py ... leanfinder "Noetherian ring is G-ring iff completion maps at maximal ideals are regular"`
returned only generic Noetherian/local-completion APIs and no criterion; `msearch.py ...
loogle "IsGRing, RingHom.IsRegular, AdicCompletion, Ideal.IsMaximal"` returned no
match (unknown project identifier); `msearch.py ... grep "G-ring|IsGRing|isGRing_iff_maximalIdeal" lean/Sheaf`
returned no criterion declaration; and `rg -n "IsGRing|isGRing_iff_maximalIdeal|G-ring"`
showed only the existing G-ring definitions and unrelated theorems. Thus no existing
declaration states this criterion.

The module compiles with `scompile.py`; the expected declaration-uses-`sorry`
warning is the only permitted omission.

## Earlier second reading (a previous round; superseded)

The statement was checked against the node clause by clause: the Noetherian hypothesis, biconditional, maximal-ideal quantifier, localization, and completion map all match. No mismatch found.

## Second reading by K1

Read the item's statement and all nine proof steps, the four statement-dependency
nodes, the landed `lean/Sheaf/RingTheory/GRing.lean`, and the Mathlib declarations
below. Read the actual Stacks TeX in `/home/ubuntu/c1-stacks-review/more-algebra.tex`
(lines 12392–12429, Lemma 07PT; 12165–12191, Definition 07GH and the formal-fibre
explanation; 10361–10389, Section 07BY and Definition 07BZ), and
`/home/ubuntu/c1-stacks-review/algebra.tex` (47104–47154, Lemma 0381 and Definition
0382). The repository's literature directory contains lists but no TeX checkout.
The source assumes commutative rings throughout; 07PT assumes only Noetherianity.
No local, domain, field, finite-dimensional, or characteristic hypothesis is required.

Node-to-Lean inventory (each verdict: exact):

1. Object: arbitrary commutative ring R — `(R : Type w) [CommRing R]`.
2. Hypothesis: R Noetherian — `[IsNoetherianRing R]`. Opened Mathlib
   `Noetherian/Defs.lean:196`: this is Noetherianity of R as its own module,
   equivalently finite generation of every ideal.
3. Left clause: R is a G-ring — `IsGRing R`. Opened the landed declaration:
   Noetherianity and regular completion maps at every prime, precisely 07GH.
4. Logical connective: if and only if — `↔`; both directions retained.
5. Right quantifiers: every maximal ideal m of R —
   `∀ (m : Ideal R) [m.IsMaximal]`. The instance binder is a universal implication,
   not an assumption that every ideal is maximal. Maximal implies prime, providing
   the localization instance automatically, with no extra hypothesis on R.
6. Local ring R_m — `Localization.AtPrime m`. Opened
   `Localization/AtPrime/Basic.lean:57`: fractions at the prime complement;
   `map_eq_maximalIdeal` identifies the extended ideal mR_m with
   `IsLocalRing.maximalIdeal (Localization.AtPrime m)`.
7. Completion at mR_m — `AdicCompletion
   (IsLocalRing.maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m)`.
   Opened `AdicCompletion/Basic.lean:171`: compatible sequences in quotients by
   powers of the ideal. With module equal to the ring, I^n • top equals I^n.
8. Canonical completion map — `algebraMap (Localization.AtPrime m) (...)`.
   Opened `AdicCompletion/Algebra.lean`'s algebra instance and `algebraMap_apply`:
   this sends an element to its residues, via `AdicCompletion.of`, not an
   arbitrary map or a map from R before localization.
9. Regularity of that map — `RingHom.IsRegular (...)`. Opened GRing's signature
   and body: flatness plus Noetherian geometrically regular fibres. Its algebra
   structure is the one induced by the stated map. `Ideal.Fiber` is the canonical
   residue-field tensor product, in the convention-approved order. Geometric
   regularity uses every finite purely inseparable extension and `IsRegularRing`,
   which includes Noetherianity and regular prime localizations. No weaker notion
   of regularity (regular sequences or regular local rings alone) is substituted.

Edge cases: the zero ring is allowed (no Nontrivial binder), Noetherian, and has
no primes or maximal ideals. Both universal conditions are vacuous, so both sides
hold. For a field the unique maximal ideal is zero and its localization's
zero-adic completion is the field. All characteristics are permitted; in
characteristic zero the geometric-regularity definition still tests the trivial
purely inseparable extension. There is no external index set, scheme, or numerical
parameter n; the internal completion includes n = 0, whose quotient by I^0 is zero
and imposes no extra condition. `w` is arbitrary and explicitly declared. The
imported geometric-regularity test uses `Type (max u v)`, sufficient to represent
all finite field extensions of the residue field; it is not vacuous from a small
independent universe. No variables or universes are unbound.

Independent searches used different wording: LeanSearch query "regularity of
formal fibers can be checked at maximal ideals of a Noetherian ring" returned
Internal Server Error (recorded unavailable, not evidence of absence). Loogle
`"isGRing"` returned no matches. LeanFinder "A Noetherian ring with regular
completion homomorphisms at each maximal localization is a G ring" returned
Noetherian-localization and quasi-finite APIs, none stating this criterion.
`msearch.py grep 'formal.?fib|geometrically.?regular|isGRing_iff'` found no Mathlib
matches. Direct rg of Mathlib, WeilConjectures, Sheaf, and the upstream names table
found no duplicate declaration. Opened `isGRing_iff_pairsOfPrimes` in
`Sheaf/RingTheory/GRingPairsOfPrimes.lean`: its quantifiers are pairs of nested
primes and quotient formal fibres (07PN), not this maximal-ideal criterion.

Mismatches and repairs: H8/H9, the theorem had no copyright header or module
source docstring, and its declaration docstring lacked the source place and the
node's nine-step proof plan. Added those, including the dependencies needed at
each proof step. H1/H4 risk: the sandbox carried an unchanged copy of the already
landed GRing module and its node, without any actual dependency repair or note.
Verified byte equality with the landed module and removed both redundant delivery
copies; the theorem imports the landed dependency directly. Also removed an empty
stray extensionless file `lean/Sheaf/RingTheory/G`. No new nodes or dependency
modules remain in this delivery. No mathematical mismatch was found: the statement
and its recorded signature are unchanged and verbatim equal. There is no
`statement_change`. The only proof is `by sorry`; no definitions or hollow data
are introduced. All Lean lines are at most 100 characters; the single import is
used. The node's objects and conclusions agree with Stacks 07PT and its explanation
of formal fibres before 07GH.

Validation: `scompile.py K1 lem-weil-pbc-g-ring-maximal-ideal-criterion
lean/Sheaf/RingTheory/GRingMaximalIdealCriterion.lean` compiled on the server
in 1.6 seconds, exit 0, with no diagnostics. Verified the unchanged
`lean.statement` against the exact signature and checked line lengths.
