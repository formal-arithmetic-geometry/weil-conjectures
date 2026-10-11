## Worker report

The module `Sheaf.RingTheory.GRingPairsOfPrimes` states
`isGRing_iff_pairsOfPrimes`, with its only proof `by sorry`.
No new definitions, dependency modules or statement corrections are needed.

Hypotheses and clauses, matched to the node:

- A commutative Noetherian ring R: `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
  No domain, local, nonzero, characteristic or completeness hypothesis is imposed on R.
- R is a G-ring if and only if the condition holds: `IsGRing R ↔ ...`.
- Every pair of prime ideals q contained in p: `∀ (q p : Ideal R) [q.IsPrime]
  [p.IsPrime] (hqp : q ≤ p), ...`. The non-strict containment includes equality.
- B = R/q: the base ring of the tensor product is literally `R ⧸ q`.
  Its domain structure follows from the existing prime-quotient instance; it is not
  an additional hypothesis.
- p/q: `let pbar := p.map (Ideal.Quotient.mk q)`. Its primality instance is supplied
  by the existing theorem `Ideal.isPrime_map_quotientMk_of_isPrime hqp`.
- Localization of B at p/q: `let L := Localization.AtPrime pbar`.
- Completion at the maximal ideal of that localization:
  `let C := AdicCompletion (IsLocalRing.maximalIdeal L) L`. Mathlib's completion
  is the compatible sequences modulo powers of that ideal, with canonical algebra maps.
- κ(q) = R_q/qR_q, canonically also the fraction field of B: `q.ResidueField`,
  using its Mathlib `Algebra (R ⧸ q) q.ResidueField` instance. Mathlib also supplies
  `IsFractionRing (R ⧸ q) q.ResidueField` (see ResidueField/Ideal.lean).
- The κ(q)-algebra in the conclusion:
  `let F := TensorProduct (R ⧸ q) q.ResidueField C`.
  This is κ(q) ⊗[B] C with its canonical left-factor algebra structure, using the
  canonical B-action on C through localization and completion. Tensor symmetry gives
  C ⊗[B] κ(q), the order used in the node. This uses the original residue field κ(q),
  not a newly chosen fraction field or the residue field at p/q. The node's final
  parenthesis identifies this same algebra with the original formal fibre; it is
  explanatory notation, as in the source proof, not a separate isomorphism assertion.
  `Ideal.Fiber` is the standard fibre for the original R-base; the quotient-base
  expression here is explicitly required by the node and uses Mathlib's tensor product.
- Noetherian AND geometrically regular over κ(q):
  `IsNoetherianRing F ∧ Algebra.IsGeometricallyRegular q.ResidueField F`.
  The explicit Noetherian clause is kept even though geometric regularity includes it.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (imported transitively).
- `Sheaf.RingTheory.GRing`: `IsGRing`, `Algebra.IsGeometricallyRegular`.
  Their signatures and full definitions were read; geometric regularity tests finite
  purely inseparable extensions in `Type (max u v)`, with no new universe restriction.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField` and its
  canonical quotient-ring algebra instance. These are the recorded Mathlib matches
  for def-weil-pbc-localization-at-prime, reached through the GRing import.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`;
  `Mathlib.RingTheory.AdicCompletion.Algebra`: its commutative ring and base algebra
  structures. These supply def-weil-pbc-adic-completion through the GRing import.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`:
  `Ideal.isPrime_map_quotientMk_of_isPrime`, which supplies the needed prime instance
  without a new lemma or proof.

Edge cases checked before writing: the zero ring has no primes, so the right side is
vacuous, consistently with IsGRing; p = q is included and gives the completed field
localization; q = 0 is allowed when R is a domain; q need not be minimal and p need
not be maximal. No hypothesis excludes any characteristic or nonreduced R.
All ring constructions remain in the universe of R, and the existing geometric
regularity predicate handles its test-extension universe. No edge case calls for a
statement correction. No STATEMENT-DISPUTED fault found.

Source check: this checkout has no `literature/stacks-project/more-algebra.tex`, so
read the primary source directly at https://stacks.math.columbia.edu/tag/07PN and
https://stacks.math.columbia.edu/tag/07GH. The displayed criterion and definition
agree with the node. The docstring carries all seven proof steps and their dependency
lemmas in natural language; no part of that proof is implemented at stage 2.

Searches for an existing statement (2026-10-11):

- msearch.py leanfinder: "A Noetherian ring is a G-ring if and only if all generic
  formal fibres of quotients by primes are geometrically regular". Eight hits on
  quasi-finite algebras, Noetherian localizations, smooth flatness and geometrically
  reduced algebras; none states the criterion.
- msearch.py loogle: `IsGRing, IsGeometricallyRegular`. Zero hits, unknown identifier
  IsGRing in the Mathlib index.
- msearch.py grep: `IsGRing|IsGeometricallyRegular|formal.?[Ff]ib`.
  Zero Mathlib hits.
- msearch.py leansearch: "G-ring criterion geometrically regular formal fibres of
  quotient by prime ideals". Service unavailable: Internal Server Error.
- rg on WeilConjectures and lean/Sheaf: `IsGRing|GeometricallyRegular|g_ring|gRing|check_pairs`.
  No source-project match; the Sheaf tree has the shared GRing definitions and other
  lemmas about polynomial formal fibres, complete local rings and finite type G-rings,
  but none states this pairs-of-primes criterion.
- rg for the exact node id in WeilConjectures and dag/lean_names_upstream.json:
  no match. rg for `gRing_iff_pairs|isGRing_iff_pairs` in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no name collision.

Validation: server single-file compilation and delivery dry run are run for this file.
The independent second reading is left to the designated second reader.

## Second reading by H1

I read the node statement, its Stacks source (More on Algebra, Tags 07PN and 07GH),
and the complete Lean declaration. The objects and hypotheses match as follows:

- The ring is `R : Type u` with `[CommRing R] [IsNoetherianRing R]`; no domain,
  locality, characteristic, nonzero, or completeness hypothesis is added.
- `IsGRing R` is equivalent to a condition quantified over all prime ideals
  `q p : Ideal R` with instances `[q.IsPrime] [p.IsPrime]` and containment
  `hqp : q ≤ p` (the node's non-strict `q ⊆ p`, including equality).
- `B = R ⧸ q` is rendered by `R ⧸ q`; `p/q` is
  `p.map (Ideal.Quotient.mk q)`, with its primality supplied by
  `Ideal.isPrime_map_quotientMk_of_isPrime hqp`.
- `B_(p/q)` is `L := Localization.AtPrime pbar`, and its completion at the
  maximal ideal is `C := AdicCompletion (IsLocalRing.maximalIdeal L) L`.
- `κ(q)` is `q.ResidueField`, with its canonical `R ⧸ q`-algebra and fraction-field
  structure. The formal-fibre algebra is now exactly
  `F := TensorProduct (R ⧸ q) C q.ResidueField`, i.e. `C ⊗[B] κ(q)`; the explicit
  `Algebra.TensorProduct.rightAlgebra` instance renders its κ(q)-algebra structure.
- The conclusion is the conjunction
  `IsNoetherianRing F ∧ Algebra.IsGeometricallyRegular q.ResidueField F`, with the
  same quantifier order and no omitted clause.

The first reading used the opposite tensor order (`κ(q) ⊗[B] C`), which is only
canonically isomorphic to the node's displayed formal fibre and therefore did not
render the node literally. I changed the factor order and added the canonical
`Algebra.TensorProduct.rightAlgebra` instance; the file compiles cleanly.

Edge cases were checked: the zero ring has no prime ideals (vacuous right side),
`q = p` is allowed, `q = 0` is allowed for domains, q need not be minimal and p
need not be maximal, and no characteristic or reducedness condition is imposed.
The universe `Type u` is the ring's universe and the geometric-regularity predicate
handles its extension universe, so no case is excluded.

Searches found no existing declaration in Mathlib, `WeilConjectures`, or `lean/Sheaf`:
LeanFinder/LeanSearch queries for the G-ring formal-fibre criterion, Loogle searches
for `IsGRing` and `IsGeometricallyRegular`, and `rg` searches for those names,
formal fibres, and `isGRing_iff_pairs` all returned no matching statement. The
recorded dependency declarations (`IsGRing`, `Algebra.IsGeometricallyRegular`,
`Localization.AtPrime`, `AdicCompletion`, and `Ideal.ResidueField`) were opened and
match the notions used here.

## Reviewer fix (R-gcp1045, stage 2)

The second reading's switch to `TensorProduct (R ⧸ q) C q.ResidueField` with an explicit
`Algebra.TensorProduct.rightAlgebra` contradicts STATE line FIBRE RING (residue-field-first
order, never a hand-written `S ⊗ κ`), the landed sibling PolynomialFormalFiber (`r.Fiber C`)
and `IsGRing`/`RingHom.IsRegular` (`p.Fiber S`), and the module's own docstring ("residue-field-first
tensor order"). Restored `F := TensorProduct (R ⧸ q) q.ResidueField C` (κ(q) ⊗[B] C) with its
canonical left κ(q)-algebra structure; the `letI` is removed. `Ideal.Fiber` itself does not apply,
since κ(q) is the residue field of R at q, not of a prime of the base B = R/q. Recompiled clean.
