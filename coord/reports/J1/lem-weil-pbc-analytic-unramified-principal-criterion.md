## Worker report

The module `Sheaf.RingTheory.AnalyticallyUnramifiedPrincipalCriterion` states
`isAnalyticallyUnramified_of_principal_quotient`, with its proof left as `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.
The statement agrees with Stacks Project, Algebra, Tag 0330
(https://stacks.math.columbia.edu/tag/0330), checked directly because the local literature
file is absent on this machine. The declaration docstring carries all eight proof steps
and their named dependencies from the DAG node.

Clause-by-clause correspondence:

- A Noetherian local integral domain `(A,m)` is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]`. The maximal ideal is
  `IsLocalRing.maximalIdeal A`; it is uniquely determined, so no independent ideal binder
  is needed. The universe `u` is explicitly declared and unrestricted.
- The chosen nonzero element of the maximal ideal is `(t : A) (ht : t ≠ 0)
  (htm : t ∈ IsLocalRing.maximalIdeal A)`.
- The principal quotient `A/tA` is `A ⧸ Ideal.span {t}`, with the canonical `A`-module
  structure. Its associated primes are `associatedPrimes A (A ⧸ Ideal.span {t})`.
  Mathlib uses radicals of element annihilators in its general definition, but
  `isAssociatedPrime_iff` under `[IsNoetherianRing A]` identifies this with prime ideals
  equal to annihilators themselves. Such an element is automatically nonzero: zero has
  annihilator `⊤`, which cannot be prime. Thus this is exactly the node's explanatory
  definition, with no extra primes introduced.
- No embedded associated primes is `hnoEmbedded`: every member of that set satisfies
  `(Ideal.span {t}).IsMinimalPrime p`. Mathlib defines this as minimal among prime ideals
  containing the principal ideal, precisely the clause in the node.
- Regularity of every localization `A_p` is `hregular`. The subtype
  `p : associatedPrimes A (A ⧸ Ideal.span {t})` ranges over exactly those primes;
  Mathlib's instance supplies `p.1.IsPrime` from membership. Its localization is
  `Localization.AtPrime p.1`, and regularity is `IsRegularLocalRing`.
- Analytic unramifiedness of each prime quotient is `hunramified`, rendering
  `p.IsAnalyticallyUnramified` for every member of the same associated-prime set.
  The recorded definition requires primality (already automatic here) and reducedness
  of the completion of `A ⧸ p` at the image of `m`; this is `m/p` as in the node.
- The conclusion is `IsAnalyticallyUnramified A`: reducedness of the `m`-adic completion.
  Both conclusion and prime-quotient hypotheses use the dependency's actual definitions.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the ring part of
  `def-weil-regular-scheme`'s `mathlib_match`. Its signature includes localness,
  Noetherianity and the equality of maximal-ideal generator rank with Krull dimension.
  The scheme clause is not involved in this statement, so its absence from Mathlib
  does not make this dependency record unusable.
- `Sheaf.RingTheory.AnalyticallyUnramified`: `IsAnalyticallyUnramified` and
  `Ideal.IsAnalyticallyUnramified`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, available
  through `RegularLocalRing.Defs`. Also read the recorded residue-field and fiber
  definitions; these additional clauses of the dependency are not needed here.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, used inside the recorded
  analytic unramifiedness definitions, with ring operations from `AdicCompletion.Algebra`.

The additional Mathlib primitives are `associatedPrimes` / `IsAssociatedPrime` from
`Mathlib.RingTheory.Ideal.AssociatedPrime.Basic` and `Ideal.IsMinimalPrime` from
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic`. All notions already exist; none is copied.
The analytic unramifiedness import provides the completion and Noetherian imports;
associated primes provides minimal primes; regular local rings provides localization.

Edge cases checked before writing:

- The zero ring is excluded by the node's integral-domain hypothesis (`IsDomain`).
- A field has maximal ideal zero and admits no `t` satisfying both element hypotheses;
  the Lean statement is vacuous in exactly that case.
- `t = 0` and units are excluded by `ht` and `htm`, respectively. In particular, the
  principal quotient is not the zero module under the hypotheses.
- A zero-dimensional Noetherian local domain is a field, so again has no such `t`.
- Empty associated-prime sets are not artificially excluded or assumed nonempty.
  Both universal hypotheses and the subtype quantifier retain their usual empty-set
  meaning. Under the actual hypotheses the quotient is nonzero and Noetherian, hence
  its associated-prime set is nonempty, but no extra hypothesis is needed.
- There is no characteristic, dimension, finiteness-of-prime-set or countability
  restriction in the binders. Primes at which regularity is required are precisely the
  associated primes, not all primes containing `t`.

Searches for an existing statement (all service searches made with `msearch.py`, recorded
in `searches.jsonl`):

- LeanSearch: `Noetherian local domain analytically unramified principal quotient associated
  primes regular reduced completion`. Service unavailable (`Internal Server Error`);
  no negative mathematical verdict inferred from that failure.
- LeanFinder: `A local domain is analytically unramified if a principal quotient has no
  embedded associated primes and regular localizations and analytically unramified prime
  quotients`. Eight results, about formally unramified algebras and localization;
  none states the reduced-completion criterion.
- Loogle: `IsRegularLocalRing, IsReduced`. Zero hits.
- Mathlib grep: `analytically|IsReduced.*AdicCompletion|AdicCompletion.*IsReduced`
  under `RingTheory`. Zero hits.
- `rg` over source `WeilConjectures/` and project `lean/Sheaf/` for `analytically`,
  `AnalyticallyUnramified`, and the item ID found only the project's recorded
  `AnalyticallyUnramified.lean` definitions, no existing criterion. Direct `rg` over
  Mathlib, the source, project Lean, and `dag/lean_names_upstream.json` for the new
  theorem name and analytic unramifiedness names found no declaration with that name.
- Read Mathlib's associated-prime and minimal-prime definitions and the Noetherian
  equivalence `isAssociatedPrime_iff`, so no new definition of either was necessary.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by J1

I independently compared the node statement with the Lean signature. The introduced
objects and hypotheses render as follows, and each matches the corresponding clause of
Stacks Algebra Tag 0330:

- A commutative Noetherian local integral domain is `(A : Type u)` with
  `[CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]`; no universe or
  finiteness restriction is added.
- The nonzero element in the maximal ideal is `(t : A)`, `ht : t ≠ 0`, and
  `htm : t ∈ IsLocalRing.maximalIdeal A`.
- The principal quotient is `A ⧸ Ideal.span {t}` and its associated primes are
  `associatedPrimes A (A ⧸ Ideal.span {t})`; Mathlib's associated-prime subtype supplies
  primality and represents the annihilator-of-a-nonzero-class notion under the stated
  Noetherian hypothesis.
- No embedded associated primes is exactly `hnoEmbedded`, requiring
  `(Ideal.span {t}).IsMinimalPrime p` for every associated prime.
- Regularity of each localization is exactly `hregular`, with
  `IsRegularLocalRing (Localization.AtPrime p.1)`.
- Analytic unramifiedness of each prime quotient is exactly `hunramified`, using
  `p.IsAnalyticallyUnramified` for every associated-prime subtype element.
- The conclusion is `IsAnalyticallyUnramified A`, the reduced maximal-ideal-adic
  completion from `Sheaf.RingTheory.AnalyticallyUnramified`.

No mismatch was found. In particular, the quantifier order and universal hypotheses are
unchanged, and no hypothesis about characteristic, dimension, nonempty associated-prime
set, or finiteness of that set was introduced. The zero ring and zero-dimensional field
cases are excluded or vacuous exactly as in the node; `t = 0` and units are excluded by
the two element hypotheses. Empty associated-prime sets retain their ordinary vacuous
meaning.

I searched Mathlib, `WeilConjectures/`, project `lean/Sheaf/`, and
`dag/lean_names_upstream.json` for the theorem and for analytic-unramified criteria.
LeanFinder returned only formally-unramified declarations; no existing criterion was
found. The associated-prime, minimal-prime, localization, regular-local-ring, and
completion notions are existing declarations used directly. The source place was checked
against Algebra Tag 0330 and agrees clause by clause. No repair was necessary.
