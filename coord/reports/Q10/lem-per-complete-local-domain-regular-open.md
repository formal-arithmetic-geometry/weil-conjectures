## Worker report

The module `Sheaf.RingTheory.CompleteLocalDomainRegularOpen` states
`IsLocalRing.exists_nonempty_open_regular_of_complete_domain`, with `sorry` as its entire
proof. It introduces no definitions. The item node changes only in `lean`.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-complete-Noetherian-domain-J-0` (Tag 07PI), lines 11912–11949, and
`definition-J` (Tag 07P7), lines 11582–11594. The former says a Noetherian complete local
domain is J-0; the latter defines J-0 as the regular locus containing a nonempty open.
The preceding paragraph defines the regular locus by regularity of prime localizations.
These are exactly the node's hypotheses and conclusion, with no correction needed.

Hypothesis and clause correspondence:

- The commutative ring R is `(R : Type u) [CommRing R]`, with `universe u` explicitly
  declared. No size bound or auxiliary field is imposed.
- Noetherianity is `[IsNoetherianRing R]`, the recorded Mathlib notion that all ideals
  are finitely generated.
- Being local with unique maximal ideal m is `[IsLocalRing R]`; m is canonically
  `IsLocalRing.maximalIdeal R`. No independent ideal or extra choice is needed.
- Being a nonzero ring without zero divisors is `[IsDomain R]`, including nontriviality.
- Being m-adically complete, including separatedness, is
  `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
- A subset U of Spec R is `U : Set (PrimeSpectrum R)`. This is the underlying topological
  space of the recorded affine scheme `AlgebraicGeometry.Spec (CommRingCat.of R)`;
  there is no change to its points or topology.
- Zariski openness is `IsOpen U`, using Mathlib's topology on `PrimeSpectrum R`.
- Nonemptiness is the explicit conjunct `U.Nonempty`.
- For every prime p in U is `∀ p ∈ U`; the inferred type of p is `PrimeSpectrum R`.
- Its local ring is `Localization.AtPrime p.asIdeal`; primality is supplied by the
  bundled spectrum point.
- Regular local is `IsRegularLocalRing (Localization.AtPrime p.asIdeal)`, including
  localness, Noetherianity and the maximal-ideal generator/Krull-dimension equality.
  No claim about openness of the entire regular locus or regularity of all of R is added.

Statement dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its docstring and `isNoetherianRing_iff_ideal_fg` identify the node's
  notion exactly (source lines 191–204).
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`; its class extends `IsHausdorff` and `IsPrecomplete`
  (source lines 46–56). This includes separation and completeness, not just convergence.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map` (source lines 469–480); the theorem uses its
  underlying topological space `PrimeSpectrum R`.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`
  (source lines 54–57), localization at the complement of the prime ideal.
- `def-weil-regular-scheme`: imported its recorded module
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, whose docstring explicitly retains
  Mathlib's ring predicates. For the node's ring clause, used its unchanged
  `mathlib_match`, `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`
  (lines 48–54), rather than the scheme predicate `AlgebraicGeometry.IsRegularScheme`.
  Both records are usable; no dependency repair is required.

All statement-dependency modules are public imports. All recorded proof-dependency
modules, including the Mathlib leaves, are plain imports. The full ten-step node proof
is recorded in the theorem docstring: the finite regular subring, concrete intermediate
models B(M), their fraction fields, the separable part, the pth-root tower induction,
the degree-p presentation, derivation and shrinking, regularity after localization,
common denominators relating C and E, and the final nonempty principal open.

Edge cases checked before writing:

- R a field, hence dimension zero and maximal ideal zero: completeness is zero-adic,
  Spec R has its zero prime, and the whole spectrum supplies the required open.
- The zero ring and the empty spectrum cannot accidentally satisfy the hypotheses:
  `IsDomain R` includes nontriviality. Nonemptiness is asserted, not dropped.
- Positive and zero characteristic both remain unrestricted. The finite tower can be
  empty in the separable case; the proof plan treats that case at step 4.
- A singular complete local domain is permitted; the conclusion only requires an open
  subset, not that the closed point be regular.
- R can live in any explicit universe u; localization and the prime spectrum are
  formed directly from R, with no test-object universe that could make a hypothesis
  vacuous.

Searches actually run with `msearch.py Q10 lem-per-complete-local-domain-regular-open`:

- LeanFinder: `A complete Noetherian local integral domain has a nonempty Zariski open
  subset of its spectrum with regular local rings` returned eight hits, concerning DVR
  equivalences, Noetherian spectra, quasi-finiteness, finite Krull dimension, and
  integral spectra. None states this node.
- Loogle: `IsAdicComplete, IsRegularLocalRing` returned zero hits.
- Mathlib grep: `exists_nonempty_open_regular|complete.*domain.*regular|IsAdicComplete.*IsRegular`
  returned zero hits.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `exists_nonempty_open_regular|complete.*domain.*regular|lem-per-complete-local-domain-regular-open`
  found the finite-over-regular theorem and the separable-ascent theorem, which have
  different conclusions/hypotheses, but no declaration of this item. An additional
  search for `J.?0|nonempty.*regular|regular.*nonempty` in the two RingTheory directories
  found related J-0 descent/ascent and residue-model criteria, not an exact match.
- The item's `lean_removed` records deletion of its old module as dead, with no surviving
  declaration elsewhere. The module path and declaration name are currently absent in
  the sources; restoring a statement here does not create a duplicate.

No new nodes, dependency modules, statement correction, or statement dispute.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
