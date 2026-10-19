## Worker report

The module `Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood` states
`RingTheory.exists_isRegular_localizationAway_of_isRegular_localizationAtPrime` with proof
`sorry`. It introduces no definitions and does not alter the mathematical statement.
The source is Stacks Project, `algebra.tex`, Tag 061L,
`lemma-regular-sequence-in-neighbourhood`, specialized from a finite module to the ring.

The Lean statement is:

- `R : Type u` with `[CommRing R]` renders a commutative ring, and
  `[IsNoetherianRing R]` renders the Noetherian hypothesis.
- `p : Ideal R` with `[p.IsPrime]` renders the prime ideal.
- `r : ℕ` and `x : Fin r → R` render a finite sequence
  `x₁,…,xᵣ`; `r = 0` is allowed.
- `hreg` states that the sequence of canonical images
  `algebraMap R (Localization.AtPrime p) (x i)`, packaged as `List.ofFn`, is
  `RingTheory.Sequence.IsRegular` in the localization at `p`.
- The conclusion is an existential `g : R` with `g ∉ p`, followed by
  `RingTheory.Sequence.IsRegular` for the same canonical image list in
  `Localization.Away g`, i.e. the principal localization `R[1/g]`.

The existing dependency declarations used are:

- `def-weil-pbc-noetherian-ring`: Mathlib `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs` (the `IsNoetherian R R` abbreviation).
- `def-weil-pbc-regular-sequence`: Mathlib `RingTheory.Sequence.IsRegular` from
  `Mathlib.RingTheory.Regular.RegularSequence`; its weak-regularity clauses and
  nonzero quotient condition are exactly the dependency notion.
- `def-weil-pbc-localization-at-prime`: Mathlib `Localization.AtPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; the theorem uses its canonical
  `algebraMap`.
- `def-weil-ring-localization-away`: Mathlib `Localization.Away` from
  `Mathlib.RingTheory.Localization.Away.Basic`; the theorem uses its canonical
  `algebraMap`.

Edge cases checked before writing: `r = 0` gives `List.ofFn` of the empty list and
Mathlib's regularity condition allows it when the localized ring is nontrivial;
`g = 1` is permitted when the finite kernel-generator indexing set is empty; the
prime ideal is proper, so `g ∉ p` is meaningful; the zero ring is not excluded by
`CommRing` and the input regularity hypothesis itself rules out an impossible
nontriviality case; no domain, reducedness, finite-type, characteristic, or
nonempty-sequence assumption is added.

Searches made on 2026-10-16:

- `msearch.py ... leanfinder "A regular sequence at a prime of a Noetherian ring spreads to a principal localization"` returned eight generic regular-sequence/localization declarations (`IsWeaklyRegular.isRegular_of_isLocalization_of_mem`, `of_isLocalizedModule`, and related results); none asserts existence of one principal localization.
- `msearch.py ... loogle "RingTheory.Sequence.IsRegular, Localization.AtPrime, Localization.Away"` returned zero hits.
- `msearch.py ... grep "regular.*(principal|neighbou?r)|IsRegular.*Localization" Mathlib/RingTheory` returned zero hits.
- Direct `rg` searches over `WeilConjectures/` and the project `lean/Sheaf/` for regular-sequence principal-neighbourhood names found no matching declaration or node module. The only related hits were unrelated regular-principal-ideal results.

No statement correction, dependency module, new definition node, or
`STATEMENT-DISPUTED` flag is needed. The required `scompile.py` check compiled both
the sandbox probe and the library module successfully after shortening the module
source line to satisfy the 100-character linter.

## Earlier second reading (a previous round; superseded)

I reread the target node, all four statement dependencies and the complete declaration signatures recorded for them. The binders match hypothesis by hypothesis: Noetherian commutative `R`, prime `p`, arbitrary finite length `r` including zero, and sequence `x : Fin r → R`; the premise and conclusion use the same elements through the canonical maps into `Localization.AtPrime p` and `Localization.Away g`. The conclusion retains the required witness `g ∉ p` and the full `RingTheory.Sequence.IsRegular` predicate, including its nonzero quotient clause. The dependency records are exact Mathlib notions and no private replacement was introduced. I also reread the six source proof clauses in the node docstring: finite kernels, quotient localization, injectivity at the prime, common denominator, transfer to the principal localization, and nonzero final quotient. No statement correction or edge case omission was found.

## Second reading by N5

Step 1 list and verdicts:

- `R` is a commutative Noetherian ring: `[CommRing R] [IsNoetherianRing R]`.
  PASS; `IsNoetherianRing` is the recorded Mathlib notion of every ideal finitely generated.
- `p ⊂ R` is a prime ideal: `(p : Ideal R) [p.IsPrime]`.
  PASS; the typeclass supplies exactly primality and properness.
- `r ≥ 0` and `x₁,…,xᵣ ∈ R`: `(r : ℕ) (x : Fin r → R)` and `List.ofFn`.
  PASS; all finite lengths, including `r = 0`, are represented in order.
- The images are regular in `R_p`: `hreg` uses
  `Sequence.IsRegular (Localization.AtPrime p)` and the canonical `algebraMap` list.
  PASS; this is Mathlib's weak nonzerodivisor conditions plus the nonzero final quotient.
- There is `g ∈ R \ p` whose images are regular in `R[1/g]`: the conclusion is
  `∃ g, g ∉ p ∧ Sequence.IsRegular (Localization.Away g)` with the same list.
  PASS; `Localization.Away g` and its canonical map are the recorded principal localization.

The source place was reread at Tag 061L (`lemma-regular-sequence-in-neighbourhood`): its
Noetherian ring, finite module, prime, localized regular sequence, and principal-neighborhood
conclusion specialize to the module `M = R` with precisely this Lean statement. The six proof
steps in the node were checked against the source: finite kernels, quotient localization,
vanishing at the prime, one common denominator, transfer of injectivity, and preservation of
the nonzero final quotient. No mismatch was found and no change was made.

Edge cases checked: `r = 0` gives the empty regular sequence and permits `g = 1`; a zero ring
has no prime ideal instance, so the theorem is vacuous there; `g ∉ p` is meaningful because a
prime is proper; no domain, reducedness, finite-type, characteristic, or nonempty-sequence
hypothesis is introduced; universes use one `u` for `R`, its ideals, and the localizations.

Searches: direct `rg` over the repository, `WeilConjectures`, and Mathlib; `msearch.py` with
LeanFinder, Loogle, and grep queries for regular sequences spreading to a principal localization.
The hits only localize already weakly regular sequences or state regularity criteria; none is
this existence theorem. The four dependency declarations were opened and match exactly:
`IsNoetherianRing`, `Sequence.IsRegular`, `Localization.AtPrime`, and `Localization.Away`.

The module compiled successfully with the prescribed `scompile.py`; no warning occurred except
the permitted `sorry` declaration warning. No statement correction, dependency repair, new node,
or duplicate declaration was needed.


## Maintainer review correction

The independent maintainer review found the theorem signature correct and unchanged.
H8: the delivered declaration docstring summarized the argument but did not carry all
six node proof steps or name the dependencies used. The replacement module now gives
those steps, including quotient comparison, vanishing at the prime, the finite product
of annihilators, and the nonzero final quotient. H9 / brief §3: added ordinary imports
of `Mathlib.RingTheory.Noetherian.Basic` and
`Mathlib.Algebra.Module.LocalizedModule.Exact` for the recorded proof dependencies
`Submodule.FG.of_le` and `LocalizedModule.map_exact`. No mathematical statement,
node record, or proof was changed. Both the original and replacement module were
checked separately through `scompile.py` using its local side overlay; both compiled
cleanly. The proof remains solely `sorry`.
