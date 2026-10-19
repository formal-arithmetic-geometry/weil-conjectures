## Worker report

This repairs the returned stage-1 handoff at `1707d55c0a2b` by supplying a genuine
stage-2 statement. The delivery introduces only
`Sheaf.RingTheory.RegularRingUniversallyCatenary`, with the one theorem
`IsRegularRing.isUniversallyCatenary` and proof `sorry`. The module and theorem
have source/blueprint docstrings; the latter includes both proof steps and their
DAG dependencies. No definition or instance is introduced. No statement correction,
new node, dependency repair, or statement dispute is needed.

Return points repaired:

- H1: added the Lean module, complete `lean` record (`existing: false`), this
  worker report, and the second reading below.
- H2: copied the current published node, preserving its stage-1
  `split_report.summary` exactly. Only `lean` differs; the rejected stage-1
  summary addition is absent. The immutable returned head had no Lean module
  or record to preserve; the retained sandbox initially contained only launcher
  markers. The delivery wrapper rebases the packet on current `newtargets-dag`.
- H10: per-file compilation uses the authorized `scompile.py` wrapper; results
  are recorded below after the compile completes.
- H11: reread the item, source, module, and expanded dependency definitions, with
  a specific universe check, in the section below. No other worker was started;
  this is a disclosed second pass by the same Q24 session. The maintainer supplies
  the independent review, as required by the current worker brief.

Hypothesis and clause matching:

| Node text | Lean rendering |
| --- | --- |
| A commutative ring R | `(R : Type u) [CommRing R]`, with explicit `universe u` |
| R is Noetherian | `[IsRegularRing R]` extends `IsNoetherianRing R` |
| Every prime localization R_p is regular local | The field `IsRegularRing.isRegularLocalRing_localization (p : Ideal R) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p)` of that same hypothesis |
| R is universally catenary | `IsUniversallyCatenary R` from the recorded Q21 dependency |
| Every finite type commutative R-algebra A | The definition quantifies over `(A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]` |
| Every comparable pair of prime ideals a ≤ b in A | `IsCatenaryRing A` quantifies over `(p q : Ideal A) [p.IsPrime] [q.IsPrime]`, with premise `p ≤ q` |
| A finite bound on all finite strict-chain lengths, for the fixed pair | `∃ N : ℕ, ∀ (n : ℕ) (c : Fin (n + 1) → Ideal A), IsPrimeChain A p q n c → n ≤ N` |
| All saturated chains between those endpoints have equal length | The two-chain clause of `IsCatenaryRing` concludes `n = m` from `IsSaturatedPrimeChain A p q n c` and `IsSaturatedPrimeChain A p q m d` |
| Every chain term is prime, endpoints fixed, length counts strict inclusions | `IsPrimeChain` requires primeness of every `c i`, first term `p`, last term `q`, and `c i.castSucc < c i.succ` for each `i : Fin n` |
| Saturated means no intermediate prime can be inserted | `IsSaturatedPrimeChain` forbids `∃ r : Ideal A, r.IsPrime ∧ c i.castSucc < r ∧ r < c i.succ` |
| No finite bound on all local dimensions of R | No `FiniteRingKrullDim R`, global dimension parameter, or uniform bound is assumed; the conclusion's bound is per pair of primes in each A |

Dependency declarations read and used (all five `stmt_deps` are usable):

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg`. Noetherianity is finite
  generation of every ideal, not finite Krull dimension.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  It is `Localization p.primeCompl`, used by the regular-ring class.
- `def-weil-regular-scheme`: `Mathlib.RingTheory.RegularLocalRing.Defs`,
  `IsRegularRing` and `IsRegularLocalRing`. The former includes exactly
  Noetherianity and regular local prime localizations. The latter includes localness,
  Noetherianity, and maximal-ideal generator rank equal to Krull dimension.
  No scheme clause is used by this ring statement.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`,
  `IsUniversallyCatenary`, `IsCatenaryRing`, `IsPrimeChain`, and
  `IsSaturatedPrimeChain`. All four definitions were read in full. We use universal
  catenarity alone, with no G-ring, J-2, or excellence assumption.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `Algebra.FiniteType`. Its field says the top subalgebra is finitely generated;
  this is finite generation as an algebra, not as a module.

The published proof-dependency modules are imported non-publicly:
`Mathlib.RingTheory.KrullDimension.Basic`,
`Mathlib.RingTheory.Regular.RegularSequence`, `Sheaf.RingTheory.Depth`,
`Sheaf.RingTheory.DepthLeSupportDimension`, and
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`. The other recorded
proof dependencies are already public statement imports.
`lem-trf-cm-ring-universally-catenary` has no `lean` record in the read base, so
there is no module to import for that proof-only prerequisite yet; it is named
in the theorem's proof docstring for stage 3. It is not needed to type this
statement and is not being restated here.

Source read: local `literature/stacks-project/algebra.tex`,
`definition-catenary` (00NI, lines 25463 onward),
`definition-universally-catenary` (00NL, lines 25489 onward),
`lemma-CM-ring-catenary` (00NM, lines 25607 onward), and
`lemma-regular-ring-CM` (00NQ, lines 25732 onward).
00NQ supplies local Cohen–Macaulayness, and 00NM supplies universal catenarity.
The full two-step proof in the node is preserved in the declaration docstring,
including the depth upper bound, empty regular sequence for dimension zero,
and the absence of any uniform local dimension bound.

Searches performed through `msearch.py Q24 lem-trf-regular-ring-universally-catenary`:

- LeanSearch: `Every Noetherian regular commutative ring is universally catenary`.
  Eight hits, including `Ideal.isLasker`, `Polynomial.isNoetherianRing`,
  `Algebra.FiniteType.isNoetherianRing`, and Noetherian criteria; none proves
  universal catenarity or the saturated-chain equality.
- LeanFinder: the same plain-language query. Eight hits about finite local Krull
  dimension, locally Noetherian spectra, ideal height, and Noetherian criteria;
  none is this statement.
- Loogle: `IsRegularRing, IsUniversallyCatenary`. Zero hits; the service reports
  `IsUniversallyCatenary` as unknown (it is a project-side definition).
- Mathlib grep: `catenar|Cohen.?Macaulay` in `RingTheory`: zero hits.
- Direct Mathlib `rg` for `IsRegularRing.isUniversallyCatenary|[Cc]atenar`:
  no matches. Direct `rg` in upstream `WeilConjectures` and side `lean/Sheaf`
  for `isUniversallyCatenary|universally.?[Cc]atenary|regular.*catenar|catenar.*regular`:
  upstream has no match; side hits are the Q21 definition, other catenarity
  statements, and prose references to this item (including `IntegersExcellent`),
  with no existing regular-ring universal-catenarity declaration.
- Upstream `rg` for the exact node id: no matches. The upstream name index
  `dag/lean_names_upstream.json` has no `isUniversallyCatenary` or
  `UniversallyCatenary` match. The theorem name is new.

Edge cases checked before writing: the zero ring has no prime localizations and
is allowed; a finite type algebra over it is again the zero ring. A field has
only the zero prime and local dimension zero. Equal prime endpoints use a chain
of length zero (`Fin 1`), and saturation ranges over empty `Fin 0`. An adjacent
prime pair has length one. Incomparable primes are outside the `p ≤ q` premise.
Finite type algebras need not be domains, local rings, regular rings, or nonzero.
No characteristic restriction is present. Regular Noetherian rings with unbounded
local dimensions are included. No hypothesis of finite global dimension is added.

## Second reading by Q24

This is a separate rereading by the same session, not a claimed independent
worker review; the brief forbids starting another agent and assigns independent
review to the maintainer. I reopened the node, the actual module, Mathlib's
regular-ring definition, and Q21's four chain predicates.

The declaration has exactly three binders: the arbitrary carrier `R : Type u`,
its `CommRing` instance, and the `IsRegularRing` instance (whose inherited
Noetherianity and prime-localization field are precisely the two ring hypotheses).
Its only conclusion is the existing `IsUniversallyCatenary R`; it does not
replace that predicate by ordinary catenarity of R or by finite dimension.
Expanding the conclusion gives Noetherianity and all the finite-type algebra,
prime-pair, bound, saturation, and length clauses listed in the table above.
The extra appearance of Noetherianity in the conclusion is already entailed by
regularity and is part of the recorded definition. There are no unbound
variables or universes (`set_option autoImplicit false`). The zero-ring and
equal-endpoint checks survive this expansion.

Same-universe quantification was checked explicitly: Q21's predicate tests
`A : Type u`, with exactly the universe of `R`, not an independent smaller
universe. A finite type R-algebra B carried in any larger universe admits a
surjection from `MvPolynomial (Fin n) R` for some natural n. Its kernel quotient
is a ring in `Type u`, with an R-algebra equivalence to B. This equivalence
identifies their prime ideal orders, preserves strict inclusions, intermediate
prime ideals, endpoint pairs, and the number of steps in every finite chain.
Consequently it preserves both bounded chain lengths and saturation and hence
catenarity. Thus quantifying over the same-universe quotient models covers every
finite type algebra up to isomorphism. No algebra or characteristic is silently
excluded, and there is no added universe equality hypothesis on the theorem.

The node's `lean.statement` was extracted from the actual keyword-through-type
signature, retaining its newline, and the node matches the current base in every
field except `lean`. No mismatch in the mathematical statement was found. The
returned packet's defects were missing artifacts, the forbidden stage-1 summary
edit, missing compile evidence, and the missing reading; each is addressed above.

Validation: `scompile.py Q24 lem-trf-regular-ring-universally-catenary
lean/Sheaf/RingTheory/RegularRingUniversallyCatenary.lean` returned exit code 0;
the sandbox compile took 12.1 seconds and the library-path compile 8.3 seconds.
Both produced no errors or warnings. The file has no line exceeding 100 characters,
contains exactly one theorem with proof `sorry`, and no new definition. A JSON
comparison with the read base confirmed that `lean` is the only changed field.

Delivery dry run: `deliver2.py Q24 lem-trf-regular-ring-universally-catenary --no-push`
returned `OK (dry run)` at `d9810c20a2`: preflight passed and the file compiled cleanly.
Only the item node, its Lean module, and the required report were staged.
