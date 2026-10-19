## Worker report

The module `Sheaf.RingTheory.PolynomialAlgebraCohenMacaulay` states
`MvPolynomial.isNoetherianRing_and_local_depth_eq_dimension` with one `sorry` proof.
It defines no new notion. The node is unchanged except for its `lean` record.

The source is Stacks Project, Algebra, Tag 00ND (`lemma-CM-polynomial-algebra`),
read in `literature/stacks-project/algebra.tex`, together with the definition
`definition-ring-CM` immediately before it and the full polynomial-induction proof
of Tag 0AAI (`lemma-maximal-CM-polynomial-algebra`). The module docstring records
all ten steps of the node's proof, including the residue-field localization and
its zero/nonzero fibre-prime cases. The theorem is stated, not proved.

Each hypothesis and clause is rendered as follows:

| Node text | Lean |
| --- | --- |
| A commutative ring R | `{R : Type u} [CommRing R]`, with `universe u` explicitly declared |
| R is Noetherian | `[IsNoetherianRing R]` |
| For every prime ideal p in R | `hCM : ∀ (p : Ideal R) [p.IsPrime], ...` |
| The local ring R_p | `Localization.AtPrime p` |
| Depth of R_p as a module over itself equals its Krull dimension | `(IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p) : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime p)` |
| Every nonnegative integer n | `(n : ℕ)`, with no positivity restriction |
| P = R[x₁,...,xₙ] | `MvPolynomial (Fin n) R`; `Fin n` indexes exactly n variables |
| P is Noetherian | The first conjunct `IsNoetherianRing (MvPolynomial (Fin n) R)` |
| For every prime ideal q in P | The second conjunct `∀ (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime], ...` |
| Depth of P_q equals its Krull dimension | `(IsLocalRing.depth (R := Localization.AtPrime q) (Localization.AtPrime q) : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime q)` |
| Thus P is Cohen–Macaulay in the displayed sense | Exactly the Noetherianity and prime-local depth equalities above, with no additional predicate |

Depth takes values in `ℕ∞` and dimension in `WithBot ℕ∞`; the displayed coercion
embeds depth without changing its value. A localization at a prime is nonzero,
so its dimension is never bottom. The depth definition already provides the
maximal ideal and the self-module is finite without adding a hypothesis.
There are no hidden `let` binders, file-local notation, or auto-bound variables.

Statement dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, whose definition is self-module Noetherianity; the same file's
  `isNoetherianRing_iff_ideal_fg` identifies it with every ideal being finitely generated.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`,
  the quotient localization at `p.primeCompl`. Its local-ring instance supplies
  the local structure used by depth. The recorded residue-field and fibre clauses
  (`Ideal.ResidueField`, `Ideal.Fiber`) were also read, in their Mathlib source files;
  the signature only needs the prime-localization clause.
- `def-weil-pbc-depth`: `Sheaf.RingTheory.Depth`, `Ideal.depth` and
  `IsLocalRing.depth`. I read the full definitions: the supremum of regular-sequence
  lengths (infinity when the ideal generates the whole module), then specialize to
  the maximal ideal. The statement uses the recorded local-ring definition.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, defined as `Order.krullDim (PrimeSpectrum R)` in `WithBot ℕ∞`.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`, the monoid algebra on finitely supported exponent vectors.
  I also read `MvPolynomial.algHom_ext` and `MvPolynomial.aeval` in Basic/Eval;
  the signature uses the polynomial-ring clause.

The statement-dependency modules are public imports. All other recorded proof
prerequisites have corresponding ordinary imports for stage 3:
`Mathlib.RingTheory.Regular.RegularSequence` (regular sequences),
`Mathlib.Algebra.Polynomial.FieldDivision` and `Mathlib.RingTheory.PrincipalIdealDomain`
(the polynomial Euclidean-domain/PID instances),
`Sheaf.RingTheory.DepthLeSupportDimension` (`IsLocalRing.depth_le_supportDim`),
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
(`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`),
`Sheaf.RingTheory.FlatLocalDepthFormula` (`IsLocalRing.depth_eq_add_of_flat_local`),
`Mathlib.RingTheory.RingHom.Flat` (`RingHom.Flat.localRingHom`),
`Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`
(`MvPolynomial.ringKrullDim_localizationAtMaximal`), and
`Mathlib.RingTheory.Flat.Basic` (`Module.Flat.of_projective`, `Module.Flat.of_free`).
These imports retain the node's proof plan without asserting any new theorem.

Edge cases checked before writing:

- For `n = 0`, the polynomial ring is the zero-variable copy of R, so the conclusion
  specializes to the hypotheses. `Fin 0` is permitted.
- If R is the zero ring, its polynomial rings are zero and Noetherian. There are
  no prime ideals, so both local conditions are vacuous. No `[Nontrivial R]` is added.
- No locality, domain, reducedness, base-field, or finite global-dimension assumption
  is imposed on R. In particular `k[ε]/(ε²)` and CM rings of unbounded global dimension
  are not excluded.
- The quantifiers are over every prime, not merely maximal ideals. For `Z[X]`, the
  primes `0` and `(p)` have a zero fibre prime, whereas `(p,X)` has nonzero fibre prime;
  both cases are retained in the statement and in the natural-language proof.
- R is in arbitrary universe u. The finite-index polynomial ring and its localizations
  stay in that universe; no independently smaller universe of test rings is introduced.

Searches for an existing statement (all through the prescribed wrapper where applicable):

1. `msearch.py ... leanfinder "A polynomial ring in finitely many variables over a
   Noetherian Cohen Macaulay ring has depth equal to dimension at each prime localization"`:
   8 hits, led by `MvPolynomial.ringKrullDim_of_isNoetherianRing`,
   `Polynomial.ringKrullDim_of_isNoetherianRing`, and bounds on polynomial dimension.
   None asserts equality with depth or CM preservation.
2. `msearch.py ... leansearch "A polynomial algebra over a Noetherian Cohen Macaulay
   ring is Cohen Macaulay"`: 8 hits, including `Polynomial.isNoetherianRing`,
   `MvPolynomial.isNoetherianRing`, and finite-type/Jacobson declarations. They do not
   include the required depth conclusion.
3. `msearch.py ... loogle '"depth", "MvPolynomial"'`: 0 hits.
4. `msearch.py ... grep 'Cohen.?Macaulay|depth.*[Pp]olynomial|[Pp]olynomial.*depth'
   RingTheory`: 0 Mathlib hits.
5. `rg -n 'Cohen.?Macaulay|depth.*[Pp]olynomial|[Pp]olynomial.*depth|lem-trf-polynomial-algebra-cm'`
   over the prescribed slopmaster2 `WeilConjectures` and shared `lean/Sheaf` trees:
   no upstream match; the shared tree has other CM results, the universal-catenarity
   consumer and polynomial-chart flatness criteria, but no theorem for this node.
6. The exact blueprint id search in upstream `WeilConjectures` gives no declaration.
   The proposed full declaration name was also searched in the upstream name index,
   Mathlib, upstream `WeilConjectures`, and shared `lean/Sheaf`, with no hit.

The initial dispatcher note confused Q17's completed Stage 1 split with a Stage 2
statement delivery: the current node and Q17 report have no Lean statement record.
This delivery supplies the missing statement and preserves Q17's reviewed split.
No new node, dependency repair, statement correction, or statement dispute is needed.

Validation: `scompile.py Q20 lem-trf-polynomial-algebra-cm` passed for the module
in both sandbox and library contexts (21.2 s and 18.3 s), without errors or warnings.
The module has exactly one theorem and one `sorry`. Only the node's `lean` field changes,
and its recorded signature is verbatim through the theorem result before `:= by`.
The prescribed `deliver2.py ... --no-push` gate runs before the final delivery.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
