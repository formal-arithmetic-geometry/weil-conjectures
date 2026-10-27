## Worker report

The module `Sheaf.RingTheory.ParameterProductStrictLocalBranches` states
`Algebra.parameterProduct_strictLocal_branches`, with `sorry` as its entire proof.
No definition, dependency interface, or informal statement was changed. The theorem's
docstring supplies all seven steps of the DAG proof with their dependency names.

Hypothesis and clause correspondence:

- The commutative regular local ring is `(A : Type u) [CommRing A]
  [IsRegularLocalRing A]`. Mathlib's class includes locality and Noetherianity, so these
  are not missing assumptions. It is the ring clause of `def-weil-regular-scheme`.
- A full ordered system is `t : List A` with
  `IsLocalRing.IsRegularSystemOfParameters t`. The selected distinct positions are
  `positions : Fin r ↪ Fin t.length`. Its `i`th selected element is `t.get (positions i)`.
  Unlike an injectivity condition on parameter values, this states exactly the given
  condition on positions. No order-preservation condition is imposed.
- The chosen separable closure is `K`, with `Field K`,
  `Algebra (IsLocalRing.ResidueField A) K` and `IsSepClosure` for that extension.
  `Algebra A K` and `IsScalarTower A (IsLocalRing.ResidueField A) K` specify that the
  structural map factors through the residue field.
- The strict henselization is `H`, with `CommRing H`, `Algebra A H`, and the recorded
  `StrictHenselizationPresentationIn.{u, v} A K H`. `K`, `H` and the pointed etale
  algebras have common arbitrary universe `max u v`, at least that of the base.
- `F`, `I`, and `J` are names introduced by explicit equality binders, not extra
  mathematical assumptions: `_hF` says `F = ∏ i : Fin r, t.get (positions i)`, `_hI`
  says `I = Ideal.span {F}`, and `_hJ` says `J = Ideal.span {algebraMap A H F}`.
  In particular the node's product in `H` is `algebraMap A H F`, which equals the
  product of the images because the algebra map preserves finite products.
  These universally quantified equality binders avoid statement-local `let` binders.
- For each `i`, the first conjunct asserts regular locality and `IsDomain` of the
  quotient by `Ideal.span {algebraMap A H (t.get (positions i))}`. `IsDomain` includes
  nontriviality. The same conjunct asserts `.IsPrime` and `≠ ⊤` of that ideal.
- The second conjunct is exactly the nonmembership for all `i ≠ j`. Since the ideals
  are principal, this also says neither principal ideal is contained in the other.
- `J.minimalPrimes = Set.range (...)` identifies all and only the specified minimal
  primes over the product ideal, including the empty range when `r = 0`.
- The next equality identifies the minimal primes of
  `(H ⧸ J) ⧸ nilradical (H ⧸ J)` with the images of those principal ideals under
  the composite of the two quotient maps. Mathlib's `mem_nilradical` identifies the
  nilradical with the ideal of all nilpotent elements. `Ideal.minimalPrimes` uses
  `Minimal` for inclusion among prime ideals containing the ideal in question;
  ring `minimalPrimes` specializes this to the zero ideal.
- `Nonempty (↥(minimalPrimes (...)) ≃ Fin r)` states that the reduction has exactly
  `r` minimal primes. An equivalence, rather than just `Nat.card`, also rules out
  an infinite set in the `r = 0` case.
- For `0 < r`, the theorem supplies the local structure on `A ⧸ I`, the action of
  that quotient on `K`, and the induced residue-field algebra, separable-closure
  property and scalar tower. The first map equality forces the action on `K` to
  descend the original action of `A`; surjectivity of the quotient map makes it
  unique. The residue-field action then factors this specified quotient action.
- It supplies an action of `A ⧸ I` on `H ⧸ J`. The second map equality requires it
  to descend the original structural map, so this action is likewise uniquely
  determined, not arbitrary additional data. `Nonempty
  (StrictHenselizationPresentationIn ... (A ⧸ I) K (H ⧸ J))` is the assertion that
  this explicit quotient is a strict henselization with the induced choice.
- The following universal quantification covers every `C` in the same arbitrary
  common universe, with a commutative ring and quotient-algebra structure and a
  strict-henselization presentation for the same `K` and induced quotient action.
  It asserts exactly `r` minimal primes of `C ⧸ nilradical C`.
- Finally `r = 0` implies `F = 1`, `Subsingleton (H ⧸ J)` (the zero ring), and
  `IsEmpty (PrimeSpectrum (H ⧸ J))` (no prime ideals).

Dependency declarations used:

- `def-weil-regular-scheme`: its exact ring match is Mathlib's `IsRegularLocalRing`
  in `Mathlib.RingTheory.RegularLocalRing.Defs`, imported publicly through the recorded
  parameter-system module. I read `Sheaf.AlgebraicGeometry.IsRegularScheme` too; that
  module supplies the separate scheme clause, which this purely ring statement does
  not use and therefore does not import.
- `def-weil-pbc-regular-system-of-parameters`:
  `WeilConjectures.RingTheory.IsRegularSystemOfParameters`,
  `IsLocalRing.IsRegularSystemOfParameters`.
- `def-sc-ring-strict-henselization`:
  `Sheaf.RingTheory.StrictHenselizationPresentationIn`,
  `Algebra.StrictHenselizationPresentationIn`. I read its full colimit cocone,
  universal property, specified identification and residue-map construction.
- The stated proof dependencies are imported without `public`:
  `WeilConjectures.RingTheory.StrictHenselizationRegular`,
  `StrictHenselizationLocalMaximalIdeal`, `StrictHenselizationDimension`,
  `RegularLocalGeneratorsRegularSequence`,
  `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`,
  `Mathlib.RingTheory.Regular.RegularSequence`,
  `Mathlib.RingTheory.LocalRing.Quotient`, and
  `Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore`.
  Their declarations include `Algebra.isRegularLocalRing_iff_strictHenselization`,
  `Algebra.strictHenselization_local_maximalIdeal`,
  `Algebra.ringKrullDim_eq_of_isStrictHenselization`,
  `IsRegularLocalRing.isRegular_and_quotients_of_generators`,
  `IsRegularLocalRing.isDomain`, `RingTheory.Sequence.IsRegular`,
  `IsLocalRing.of_surjective'` and
  `Algebra.strictHenselization_surjective_quotient_core`.
  The parameter and strict-henselization definition proof dependencies are already
  public imports. No proof import cycle was found.

Edge cases checked before writing: an empty full parameter list (a field), an empty
selected set even in positive dimension, one selected parameter, arbitrary reorderings
of selected positions, arbitrary characteristic, and larger common algebra universes.
No `Nonempty (Fin r)` or positive-dimension assumption appears. The quotient local and
separable-closure data are only asserted under `0 < r`, avoiding local structures on
zero rings in the empty case. No regularity, locality, or domain hypothesis on `H` or
its quotients was added to the inputs.

Sources read locally: Stacks `algebra.tex`, `lemma-regular-domain` (00NP),
`lemma-regular-ring-CM` (00NQ), `lemma-quotient-strict-henselization` (05WS), and
`more-algebra.tex`, `lemma-henselization-regular` (06LN) and
`lemma-dumb-properties-henselization` (07QM). The node's complete seven-step proof
and every recorded statement dependency were read. No source-based correction or
STATEMENT-DISPUTED issue was needed.

Searches for existing statements (2026-10-24; the wrapper also records searches.jsonl):

- LeanFinder via `msearch.py`: "Minimal primes of a product of distinct regular
  parameters in a strict henselization are precisely the principal parameter ideals".
  Eight results about strongly transcendental elements, localizations, heights and
  general minimal-prime operations; none states the parameter-product theorem.
- Loogle via `msearch.py`: `IsRegularLocalRing, minimalPrimes`: zero hits.
- LeanSearch via `msearch.py`: "Minimal primes of the product of distinct regular
  parameters after strict henselization". Eight results, including `minimalPrimes`,
  `Ideal.minimalPrimes`, localization transport, and prime-spectrum minimality;
  none includes the regular-parameter or strict-henselization assertions.
- Mathlib grep via `msearch.py`, RingTheory:
  `strictHensel|strict_hensel|henselization|minimalPrimes.*prod|prod.*minimalPrimes`:
  zero hits. Direct `rg` read Mathlib's minimal-prime, regular-local, nilradical,
  quotient-algebra and local-ring/residue-field interfaces.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for strict-henselization,
  parameter-product and minimal-primes/product patterns found the already used
  presentation and proof interfaces, and unrelated root-tower results; no exact
  statement. The item id has no source declaration under `lean/WeilConjectures`.
  The proposed declaration name has no hit in either source root or
  `dag/lean_names_upstream.json`.

Validation: the delivered file compiled through the prescribed `scompile.py Q34
lem-trf-parameter-product-strict-local-branches <file>` against the live library,
exit 0, clean sandbox and library passes (12.7 s and 1.6 s respectively).

## Second reading by Q34

The same dispatcher worker performed a separate second pass over the saved node and
saved Lean file; no other agent was started. The maintainer performs the independent
review after delivery. This pass checked the mapping above against the actual theorem:
regular-local includes both required ring hypotheses; the embedding concerns positions;
`F` is named in the base and its image is used in `H`; no empty case is excluded;
the domain clause includes nonzeroness; the minimal-prime equality is over `J`, not
merely over zero in `H`; the reduced images use both quotient maps; the finite count
uses an equivalence; and the induced actions have explicit commuting equalities.
The universal last clause quantifies all strict henselizations for those same induced
actions, rather than only a chosen presentation. The zero-ring conclusion is separated
from the nonempty-product implication. No mismatch or change was found in this pass.
