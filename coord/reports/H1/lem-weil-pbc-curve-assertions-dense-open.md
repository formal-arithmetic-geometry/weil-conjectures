## Worker report

Item: `lem-weil-pbc-curve-assertions-dense-open`.
Module: `Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions`.
Declaration: `AlgebraicGeometry.IsCurve.dense_open_assertions`.
Stage 2 only: the one theorem has proof `sorry`; no definitions, auxiliary theorems,
new nodes, dependency modules, or statement corrections were needed.

The module states all three clauses of the node together as a conjunction. Its docstring
contains all twelve natural-language proof steps from the node and their dependencies.
The theorem was compiled on the server with `scompile.py`: exit 0, 3.6 seconds, no warnings.

Hypotheses and objects, individually:

- Algebraically closed base field: `{k : Type u} [Field k] [IsAlgClosed k]`.
  No algebraicity over another field is assumed; the node only requires an algebraically
  closed base field, not a selected algebraic closure of a specified smaller field.
- Separated, finite-type scheme of dimension at most one: `P : CurveCoefficientPair k`
  supplies `P.C`, `P.toSpec`, and `P.isCurve : IsCurve P.toSpec`. This uses precisely the
  dependency node's recorded structure, without assuming connectedness, reducedness,
  smoothness, properness, nonemptiness, or dimension exactly one.
- Torsion abelian etale sheaf: the same pair supplies `P.F` and `P.isTorsion`. It is an
  abelian sheaf in `Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Constructibility: `(hP : P.IsConstructible)` is the dependency's predicate on the
  underlying sheaf of sets (finite constructible locally closed partition, finite locally
  constant restrictions). No different constructibility predicate is substituted.
- Dense open inclusion: `(U : P.C.Opens) (hU : Dense (U : Set P.C))`, with inclusion `U.ι`.
  Every dense open subscheme is represented by its open subset; there is no extra choice
  of open, no finiteness assumption on the complement, and no smoothness of the open.
- Inverse image: `(Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F`.
- Extension by zero: the abelian sheaf `F'` is the above inverse image followed by
  `Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι`. This is precisely the
  recorded extension functor, not a new construction or a Zariski restriction.
  Its torsion is a consequence, not an extra hypothesis; the underlying functors do not
  require a torsion instance in order to state the eight predicates.
- The eight implications: `IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F` and the same
  predicate with `G`. Read the complete upstream structure and `assertions_iff`: all
  eight fields include their respective applicability hypotheses. No assertion is
  asserted unconditionally when the source makes it conditional.

The abelian-to-module coefficient conversion is exactly the expression `E` from the
landed `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions`, declaration
`AlgebraicGeometry.IsCurve.finite_pushforward_assertions`:
`(forget₂ (ModuleCat ℤ) AddCommGrpCat).inv` followed by restriction of scalars along
`ULift.ringEquiv`. It is an equivalence of coefficient categories. `F` is this conversion
of `P.F`, and `G` this conversion of the actual abelian extension by zero `F'`.
This is the prescribed shared form; it defines no second bridge and introduces no finite
coefficient ring or bound on the torsion. The conversion makes the recorded module-valued
assertions and primary-torsion predicates usable for the recorded abelian curve pair.

Conclusions, individually:

1. The first conjunct is `Assertions ... G → Assertions ... F`, with no further torsion
   restriction. It is exactly the transfer from extension by zero to the original sheaf.
2. The second conjunct assumes
   `Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
    ∃ p : ℕ, p.Prime ∧ CharP k p ∧ Scheme.IsPrimaryTorsionSheaf (ULift ℤ) F p`
   and then `Assertions ... F → Assertions ... G`.
   The first alternative is prime-to-characteristic torsion, element by element in
   geometric stalks. The second is primary torsion for the positive prime characteristic.
   This is exactly the node's disjunction, with no global annihilator in this clause.
   In characteristic zero every positive integer is invertible in the base field, so the
   first alternative holds for every torsion sheaf; the second alternative cannot occur.
   Using the characteristic prime rather than the exponent causes no change: the only
   other characteristic exponent is one in characteristic zero, covered by the first side.
3. The third conjunct universally quantifies `r : ℕ`, assumes `r.Prime` and
   `r • 𝟙 P.F = 0`, and concludes `Assertions ... F ↔ Assertions ... G`.
   The identity annihilator says that multiplication by that prime on the abelian sheaf
   is zero, exactly 'F killed by a prime number'. This is a consequence asserted separately
   in the node, not an extra condition imposed on either preceding clause.

Dependency declarations read and used:

- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (read its defining class and docstring;
  also inspected `IsAlgClosure` and `AlgebraicClosure`, which are not needed here).
- `def-weil-pbc-curve-setting`: `AlgebraicGeometry.CurveCoefficientPair`,
  `Sheaf.AlgebraicGeometry.CurveCoefficientPair` (imported transitively).
- `def-weil-pbc-constructible-torsion`: `AlgebraicGeometry.CurveCoefficientPair.IsConstructible`,
  `Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf`.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (imported through LowerShriek).
- `def-weil-pbc-extension-by-zero`: `AlgebraicGeometry.Etale.openImmersionLowerShriek`,
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `def-weil-pbc-eight-curve-assertions`: `AlgebraicGeometry.IsCurve.Assertions`,
  `WeilConjectures.AlgebraicGeometry.Curve.Assertions`; read all eight fields and
  `AlgebraicGeometry.IsCurve.assertions_iff`.
- `def-weil-pbc-primary-torsion`: `AlgebraicGeometry.Scheme.IsPrimaryTorsionSheaf`, same
  Assertions module, and `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder`,
  `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf` (transitive import).

Edge cases checked before writing:

- Empty scheme: its only dense open is empty, and all assertions have zero cohomology;
  the pair and the theorem allow it. Density is not replaced by nonemptiness.
- Dimension zero: density forces the open to contain all points in this finite-type case;
  nothing requires dimension one.
- Identity open `U = ⊤`: inverse image and extension are canonically identities, so all
  three clauses agree with the tautological transfer.
- Zero sheaf: constructible and torsion of both allowable kinds, killed by every prime;
  the conclusions agree with the zero cohomology assertions.
- Mixed torsion: the forward clause applies; the converse retains exactly the node's
  disjunction instead of silently assuming it for every torsion sheaf.
- Positive characteristic: characteristic-prime torsion and other prime torsion are both
  included. Characteristic zero imposes no converse torsion restriction beyond torsion.
- No common torsion exponent is assumed except in the final prime-killed specialization.
- Universe `u` for the base and schemes, `u + 1` for coefficient categories, agrees with
  the existing pair and assertion dependencies, including their geometric-point and
  field-extension universes; no smaller independent test universe was introduced.

Searches made (tools, queries, results):

- `msearch.py ... leanfinder "The eight etale cohomology curve assertions pass between a
  constructible torsion sheaf and its restriction to a dense open extended by zero"`:
  eight hits, all unrelated (Zariski section restriction, tilde module sections, or etale
  ring locus), no exact theorem.
- `msearch.py ... loogle "\"DenseRange\", \"Sheaf\""`: zero hits.
- `msearch.py ... grep "Assertions|lowerShriek|extensionByZero" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch "For a dense open immersion j into a curve, the eight etale
  cohomology assertions transfer between F and j_! j^* F"`: UNAVAILABLE, Internal Server
  Error; no verdict inferred from this unavailable search.
- `rg` of `lem-weil-pbc-curve-assertions-dense-open|assertions.*dense|dense.*assertions`
  in upstream `WeilConjectures` and project `lean/Sheaf`: upstream Reductions has
  `IsCurve.exists_dense_assertions_iff_lowerShriek` and its componentwise variant.
  Read the full first signature and docstring: these are existential choices of special
  dense opens for reduced curves, over finite coefficient rings with a fixed prime
  annihilator. Neither states the present transfer for an arbitrary dense open and an
  arbitrary constructible torsion abelian sheaf. No exact declaration was found.
- `rg` of `Assertions|dense|restrict.*open` in the project and upstream curve modules:
  located the shared eight predicates, finite pushforward module, and those same
  existential reductions. The chosen declaration name has no collision.

Source checked: the local Stacks TeX file is absent on this machine, so read the official
page https://stacks.math.columbia.edu/tag/0GJA (Lemma 59.83.6). It gives the dense-open
open/closed sequence and the same transfer argument; the node explicitly restricts the
converse to homogeneous primary or prime-to-characteristic torsion and explains that
restriction in its proof. This delivery preserves the node verbatim, with no correction.
No STATEMENT-DISPUTED or dependency fault was found.

Dry run: the initial preflight found that the stored signature included the terminal `:=`.
The record now ends immediately before that token, as the preflight requires.
The required independent second reading is left for the second reader, as instructed.

## Second reading by H1

I opened the node and the Lean declaration independently. The node introduces: an
algebraically closed field `k` (with characteristic exponent), a separated finite-type
scheme `X` of dimension at most one, a constructible torsion abelian etale sheaf `F`, a
dense-open inclusion `j : X' ⟶ X`, its inverse image `j⁻¹F`, and its extension by zero
`j_!j⁻¹F`. The Lean renders these as `k`, `P : CurveCoefficientPair k`,
`hP : P.IsConstructible`, and `U : P.C.Opens` with `hU : Dense (U : Set P.C)` and
`U.ι`; `P.C`, `P.toSpec`, `P.isCurve`, `P.F`, and `P.isTorsion` supply exactly the
scheme and sheaf data. `F'` is the recorded `openImmersionLowerShriek` of the recorded
`upperStar`, so it is the node's `j_!j⁻¹F`. The required coefficient bridge is the same
`forget₂.inv ⋙ restrictScalars (ULift.ringEquiv)` used by the finite-pushforward node;
the Lean predicates `IsCurve.Assertions ... F` and `... G` therefore render the node's
abelian-sheaf assertions without introducing a second notion.

The first conclusion clause is exactly `Assertions G → Assertions F`. The second is the
node's converse implication under the disjunction “prime to characteristic or primary in
the characteristic prime”, rendered as `IsTorsionSheafOfInvertibleOrder ... F ∨
∃ p, p.Prime ∧ CharP k p ∧ IsPrimaryTorsionSheaf ... F p`, followed by
`Assertions F → Assertions G`. The final Lean conjunct universally quantifies a prime
`r`, assumes `r • 𝟙 P.F = 0`, and states the iff; this is the node's “in particular,
killed by a prime” sentence made explicit. Quantifier order and all three implication
directions agree with the node.

I checked empty schemes and opens, the identity open, zero and mixed-torsion sheaves,
characteristic zero and positive characteristic, and the universe levels. No hypothesis
is strengthened: separatedness, finite type, and dimension are supplied only by
`CurveCoefficientPair`; density is the sole open condition. Searches of Mathlib,
`WeilConjectures`, and `lean/Sheaf` found no declaration of this transfer theorem;
the existing dense-assertion declarations are existential reduction lemmas with different
hypotheses and conclusions.

The worker report's statement that no correction was needed is accurate. I changed no
Lean code or node statement; the only change in this second reading is this independent
item-by-item verification. The module recompiles cleanly with `scompile.py`.
