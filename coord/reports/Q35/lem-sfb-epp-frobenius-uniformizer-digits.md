## Worker report

The module `Sheaf.RingTheory.FrobeniusUniformizerDigits` states
`IsDiscreteValuationRing.exists_frobenius_digits_or_root`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record.

Hypothesis and conclusion correspondence:

- The prime `p` is `(p : ℕ) (hp : p.Prime)`.
- The two rings are `R : Type u` and `S : Type v`, with independent explicit universes.
  Their `CommRing`, `IsDomain`, and `IsDiscreteValuationRing` instances express precisely
  the complete DVR statement's ring and domain hypotheses.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]` and the analogous
  instance for `S`: these are the maximal-ideal adic completions, with separatedness.
- Characteristic `p` is `[CharP R p] [CharP S p]`.
- The injective local inclusion is `(f : R →+* S) (hf : Function.Injective f)
  [IsLocalHom f]`. This presents an inclusion without requiring equal universes.
- Uniformizers are `(t : R) (s : S) (ht : Irreducible t) (hs : Irreducible s)`.
  Mathlib's `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies these
  hypotheses with generators of the respective maximal ideals.
- The relation `s^p=t` is `(hst : s ^ p = f t)`, with the inclusion displayed.
- The arbitrary element `u` of the node is the binder `(x : R)`; renaming avoids
  confusion with the universe `u`.
- The alternatives are joined by `∨`, so they are not asserted to be exclusive.
- The finite alternative quantifies `∃ (m : ℕ) (c : Fin m → R) (b : R)`.
  Natural `m` renders the integer condition `m ≥ 0`, and `Fin m` supplies exactly
  the digits indexed by `0 ≤ i < m`, with no extraneous digits.
- Its equality is `x = (∑ i : Fin m, c i ^ p * t ^ (i : ℕ)) + b * t ^ m`.
- The nonpower residue condition is
  `¬ ∃ z : R ⧸ Ideal.span ({t} : Set R),
    z ^ p = Ideal.Quotient.mk (Ideal.span ({t} : Set R)) b`.
  It uses the quotient by `(t)` itself, as in the node, rather than an unspecified residue map.
- The root alternative is `∃ w : S, w ^ p = f x`, so the root lies in the specified
  ring `S`, and the equation uses the given inclusion.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: Mathlib module
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`. The class is the local
  principal ideal ring structure on a domain with nonzero maximal ideal.
- `def-weil-pbc-adically-complete-ring`: recorded module
  `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete`; its data comprise
  `IsHausdorff` and `IsPrecomplete`. The recorded `AdicCompletion` and
  `AdicCompletion.of`, with `AdicCompletion.of_bijective_iff`, confirm that this
  is exactly the inverse-limit definition in the node.
- Proof dependency `def-weil-ring-frobenius`: recorded module
  `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`, `iterateFrobeniusOfPrime` and
  `iterateFrobeniusOfPrime_apply`. This module is a plain proof import; the statement
  itself uses ordinary powers, and `Mathlib.Algebra.CharP.Basic` supplies `CharP`.
- Additional statement syntax uses Mathlib's finite sums, `IsLocalHom`,
  `Ideal.span`, and `Ideal.Quotient.mk`; no private copies of these notions appear.

Edge cases checked before writing:

- `m = 0`: `Fin 0` is empty, the sum is zero, and `t ^ 0 = 1`, giving exactly
  the immediate residue obstruction with `b = x`.
- `x = 0`: the root alternative admits `w = 0`; no nonzero or unit condition is added.
- Perfect residue field: the first alternative has no witness, but the second
  remains available by completeness of `S`, without a coefficient-field section.
- Imperfect residue field: a nonpower residue gives the first alternative at `m = 0`;
  it need not remain a nonpower after passing to the residue field of `S`.
- Nonunits and arbitrarily divisible elements are included. No finite-degree,
  residue-field equality, perfection, coefficient section, or surjectivity hypothesis is added.
- Prime `2` is included; `p = 0` and `p = 1` are correctly excluded by primality.
  The zero ring and fields are excluded by the source's DVR hypotheses, not by
  an additional restriction. Both completeness assumptions are retained even
  though the supplied proof primarily uses completeness of `S`.

Source check: read `literature/stacks-project/more-algebra.tex`,
`lemma-purely-inseparable-case` (Tag 09EY), including both final proof paragraphs.
The node already records the complete-ring formulation and supplies the precise
root ring `S` to resolve the printed undefined `B_1`. No statement correction is needed.
The theorem docstring includes all four steps of the node's complete-ring proof.

Searches for an existing statement:

- `msearch.py leanfinder`, query: "In complete discrete valuation rings of
  characteristic p with s^p=t every element has a finite Frobenius digit expansion
  ending in a nonpower residue or a pth root in the larger ring". Eight hits,
  including `PerfectClosure.r_iff`, `PreTilt.instPerfectRing`, and
  `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow`; these concern perfect closures,
  pretilts, or untilts and do not state this uniformizer-digit alternative.
- `msearch.py loogle`, query `IsDiscreteValuationRing, IsAdicComplete`: zero hits.
- `msearch.py grep`, query `frobenius|digit|pth` in `RingTheory/DiscreteValuationRing`:
  zero hits.
- `msearch.py leansearch`, query: "For a complete DVR in characteristic p, an
  element either has a finite expansion in Frobenius digits ending in a
  non-pth-power residue or has a pth root after adjoining a pth root of a uniformizer".
  Eight hits, including `Perfection.frobenius_pthRoot`, `surjective_frobenius`,
  `MvPowerSeries.map_iterateFrobenius_expand`, and `frobenius`. These provide
  Frobenius constructions and perfect-ring or power-series identities, not the
  finite-obstruction/root dichotomy for the given extension of complete DVRs.
- `rg` in the project's `WeilConjectures` and `Sheaf` trees for the item id,
  `uniformizer.*(digit|frobenius)|frobenius.*uniformizer`, and the proposed name:
  no matching statement. The prescribed `grep -rn` of the item id in
  `lean/WeilConjectures` also found none. A name search of `dag/lean_names_upstream.json`
  and Mathlib found no declaration named `exists_frobenius_digits_or_root`.

Validation: the prescribed `scompile.py` compiled the sandbox and library module
cleanly, with no errors or non-sorry warnings. `autoImplicit` is disabled and all
variables and universes are explicitly bound. No new nodes, dependency repairs,
statement disputes, or node faults were needed. The dry-run and delivery checks
are run after this report is written.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
