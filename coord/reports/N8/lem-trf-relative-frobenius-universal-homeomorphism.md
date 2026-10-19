## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism` states
`AlgebraicGeometry.Scheme.relativeFrobenius_integral_universalHomeomorphism`, with one
`sorry` and no definitions. It follows Stacks Varieties Tag 0CCB and the canonical
construction in Tag 0CC9, read in `literature/stacks-project/varieties.tex`.
The node has no proof steps or proof dependencies; the docstring supplies the source's
proof plan, including naturality and the pullback universal property.

Hypotheses and clauses correspond as follows:

- The prime `p` and characteristic-p scheme `X` are `(p : ℕ)` and
  `(hX : X.IsCharacteristic p)`. This existing predicate includes primality as `hX.1`
  and vanishing on every open as `hX.2`; a second prime assumption would be redundant.
- Schemes `X` and `V` are `(X V : Scheme.{u})`; an arbitrary morphism is `(v : V ⟶ X)`.
  There are no weakly-etale, finite-type, quasi-compactness or perfection assumptions.
- The inherited characteristic of `V` is the conclusion `∃ hV : V.IsCharacteristic p`.
  It is not assumed. Existence follows by applying `v.appTop` to the vanishing of `p`,
  and then restriction to every open of `V`.
- Absolute Frobenius is exactly the dependency's `Scheme.iterateFrobenius` with iteration
  argument `1`: `X.iterateFrobenius hX.1 (hX.2 ⊤) 1`, and the same expression for `V`.
  The upstream construction is identity on points and raises sections to `p ^ 1 = p`.
- The specified twist is literally `pullback v (X.iterateFrobenius hX.1 (hX.2 ⊤) 1)`.
  Its projections to `V` and `X` are `pullback.fst` and `pullback.snd`, respectively.
- The canonical relative map is the existentially bound `r` with both equations
  `r ≫ pullback.fst ... = V.iterateFrobenius ... 1` and
  `r ≫ pullback.snd ... = v`. Its existence includes Frobenius naturality and the
  pullback lift. The final `∀ s, ... → ... → s = r` asserts uniqueness from those
  equations alone, independently of the two geometric properties.
  This specifies the unique canonical map, rather than using an arbitrary map as a
  hypothesis or selecting data from an undetermined existence statement. No new
  definition of relative Frobenius is introduced: the result uses existing pullback
  operations and characterizes the map by its universal property.
- Integrality is `IsIntegralHom r`, the dependency's Mathlib notion.
- Universal homeomorphism is exactly the dependency's recorded specialization
  `(topologically IsHomeomorph).universally r`, quantifying over all scheme base changes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.SchemeCharacteristic`: `Scheme.IsCharacteristic`.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`: `Scheme.iterateFrobenius`,
  `iterateFrobenius_apply`, and `iterateFrobenius_app_apply` (the latter two explain
  its meaning; the signature uses the definition).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; scheme pullbacks are supplied by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom`, the integral half
  of `def-weil-finite-integral-morphism`; finiteness is not asserted.
- `Mathlib.CategoryTheory.MorphismProperty.Limits`: `MorphismProperty.universally`;
  `Mathlib.AlgebraicGeometry.Morphisms.Constructors`: `topologically`;
  `Mathlib.Topology.Homeomorph.Defs`: `IsHomeomorph`. These are available through the
  integral-morphism imports, and their full definitions were read.

Edge cases checked before writing: the empty source and the empty base (including zero
section rings) remain admitted by `IsCharacteristic` and the upstream actual Frobenius
construction. Nonreduced schemes remain admitted; the Frobenius need not be invertible.
No finite Frobenius assumption is made, so imperfect fields of infinite p-degree and
infinite-dimensional schemes are included. All primes, including 2, are included;
0 and 1 are correctly excluded by the characteristic predicate. The construction uses
the first iterate, so it imposes no extra positive-iteration parameter. The arbitrary
universe `u` is shared with all scheme base changes in `universally`, as required by the
recorded Mathlib definition. Characteristic witnesses are proofs and do not introduce
choices of Frobenius maps. Naturality yields exactly the required commutative square;
pullback uniqueness proves the final uniqueness clause without extra geometric assumptions.

Searches performed with `msearch.py N8 lem-trf-relative-frobenius-universal-homeomorphism`:

- LeanFinder: `The relative Frobenius of schemes in characteristic p is integral and a
  universal homeomorphism`. Eight results: integral-morphism base-change/composition
  infrastructure, normalization and `bijective_frobenius`; no exact theorem.
- Loogle: `"frobenius", "integral"`. Zero hits.
- Mathlib grep: `relative.?[Ff]robenius|[Ff]robenius.*[Hh]omeomorph` in
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: `relative Frobenius of schemes is an integral universal homeomorphism`.
  Eight hits about integral morphisms and affine/universally-closed characterizations;
  none states the relative Frobenius theorem.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for
  `relativeFrobenius|relative_frobenius`; and `grep -rn` of the exact item id upstream.
  No exact-id occurrence or theorem with this unrestricted statement. The upstream
  `ProEtale.relativeFrobenius` is the opposite-order pullback lift. Its
  `isUniversalHomeomorphism_relativeFrobenius` assumes both absolute Frobenius maps
  finite, and its combined theorem assumes locally finite type over a finite field.
  Those hypotheses cannot be imposed here. The side `FiniteFieldDatum.relativeFrobenius`
  concerns a finite-field geometric-fiber model, a different construction.
- `rg` checked the new declaration name in upstream and side sources: no collision.

There is no statement correction, new node, dependency repair, or disputed statement.
Only the item's `lean` field changes; its inherited status is preserved.
The single module compiled cleanly through `scompile.py` (sandbox and library passes),
with no errors or unexpected warnings. The delivery dry run is the final check; the
independent second reader supplies their own reading and performs delivery.

## Second reading by N8

I independently read the node, its six statement-dependency records and their actual
declarations, the delivered module, and Stacks `varieties.tex`, Section Frobenii,
Tags 0CC7--0CCB, including the section's characteristic convention. In the source,
the base is named S and its scheme is named X; the node names these X and V.
There is no finite-type, Noetherian, separatedness, or nonemptiness assumption.

The complete object/hypothesis/conclusion checklist is:

- Prime p: `(p : ℕ)` and the first component of `(hX : X.IsCharacteristic p)`.
  The actual definition is `Nat.Prime p ∧ ∀ U : X.Opens, (p : Γ(X, U)) = 0`.
  Verdict: exactly the prime and sheaf-characteristic conditions, with no redundant
  extra characteristic instance or nontrivial-ring assumption.
- Base scheme X and arbitrary scheme V: `(X V : Scheme.{u})`, using Mathlib's
  locally affine locally ringed spaces. Verdict: correct objects.
- Arbitrary scheme morphism v: `(v : V ⟶ X)`, Mathlib's `Scheme.Hom`.
  Verdict: no extra geometric property or structure over a field is assumed.
- Inherited characteristic of V: `∃ hV : V.IsCharacteristic p` in the conclusion.
  Verdict: correctly concluded, rather than required as a hypothesis.
- Absolute Frobenii: `X.iterateFrobenius hX.1 (hX.2 ⊤) 1` and
  `V.iterateFrobenius hV.1 (hV.2 ⊤) 1`. I read the upstream definition and its
  `iterateFrobenius_apply` / `iterateFrobenius_app_apply` signatures and bodies:
  identity on points and p^1-th powers on sections. Verdict: the recorded notion,
  including on zero section rings, with the correct first iterate.
- Twist and its two projections: `pullback v (X.iterateFrobenius ... 1)`,
  `pullback.fst v ...`, and `pullback.snd v ...`. I read their definitions and
  the scheme `HasPullbacks` instance. Verdict: exactly V ×_{X,F_X} X, in the
  node's factor order; no abstract or unrelated substitute for the twist.
- Canonical relative Frobenius: `∃ r : V ⟶ pullback v ...`, followed by
  `r ≫ pullback.fst ... = V.iterateFrobenius ... 1` and
  `r ≫ pullback.snd ... = v`. Verdict: these are precisely π₁r = F_V and π₂r = v.
  Existence includes the naturality square, and so does not assume that square
  or an unconstrained auxiliary map. Proof irrelevance removes dependence on
  the characteristic witnesses.
- Uniqueness: the final `∀ s, s ≫ pullback.fst ... = ... →
  s ≫ pullback.snd ... = v → s = r`. Verdict: uniqueness among all maps having
  the two equations, independently of integrality/homeomorphism. This is exactly
  the canonical map specified by the fibre-product universal property.
- Integrality: `IsIntegralHom r`. I read its class: affineness plus integral
  section-ring maps over every affine open. Verdict: the integral component of
  `def-weil-finite-integral-morphism`, with no finiteness assertion.
- Universal homeomorphism: `(topologically IsHomeomorph).universally r`.
  I read `topologically`, `universally`, and `IsHomeomorph`: this asserts a
  continuous open bijection after every scheme pullback square. Verdict: exactly
  the recorded topological notion, rather than only a bijection on points or
  the unqualified homeomorphism of the original map. The purely inseparable
  residue-field clause also stated in Tag 0CCB follows from this property
  (Tag 01S4); the node requests the two displayed geometric properties.

Edge cases: the empty source, empty base whenever a morphism exists, and zero
section rings are admitted, since neither a field instance nor `Nontrivial` is
required. Nonreduced schemes, imperfect fields, non-quasi-compact schemes and
non-finite Frobenius are included. Every prime including 2 is admitted; p = 0
and p = 1 are excluded precisely by the source's prime hypothesis. There is no
index set or zero-object assumption. There is no iteration parameter n to
exclude n = 0: this node concerns absolute p-Frobenius, hence the literal 1.
The explicit arbitrary universe u is the standard scheme-category universe;
all scheme pullbacks/base changes in `universally` range over that category,
and no independent smaller test-object universe makes the property vacuous.
Every variable and universe in the signature is explicitly bound.

Independent H4 searches through the prescribed `msearch.py` wrapper:

- LeanFinder: "For a morphism to a scheme of prime characteristic, the map to
  its Frobenius twist is universally closed, radicial, and surjective".
  Eight hits, about universal closedness and integral morphisms; no match.
- Loogle: `"iterateFrobenius"`. Twelve ring-Frobenius hits, including
  `RingHom.iterateFrobenius_comm`; none is this scheme theorem.
- LeanSearch: "The canonical morphism from a characteristic p scheme to its
  Frobenius base change is integral and a universal homeomorphism".
  Eight hits, about integral morphisms and ring Frobenius; no match.
- Direct `rg` in Mathlib/AlgebraicGeometry, upstream WeilConjectures and side
  lean/Sheaf for `relativeFrobenius|relative_frobenius|frobenius.*[Ii]ntegral|
  [Ii]ntegral.*frobenius`, plus the upstream-name index and DAG concept search.
  No exact unrestricted theorem or duplicate declaration name was found.
  I opened upstream `ProEtale.relativeFrobenius`, its two projection lemmas,
  and `isUniversalHomeomorphism_relativeFrobenius`: the construction uses the
  reversed pullback order, and the theorem requires both absolute maps finite.
  The combined theorem also requires finite-field models locally of finite type.
  The side `FiniteFieldDatum.relativeFrobenius` instead acts on a geometric fibre.
  None can be recorded as an exact existing match. This delivery defines no
  second relative-Frobenius notion: it states the universal-property result
  directly using the dependency's pullback and absolute Frobenius.

Mismatches found and repaired: the worker report says there are no proof steps
or proof dependencies, but the actual node has eight steps and eighteen proof
dependencies. The former docstring gave a shorter valid argument instead of
those eight steps. I replaced that proof paragraph with the complete numbered
plan, including prime-field specialization, affine/universally-closed integrality,
separated cancellation, field-point injectivity, point-set surjectivity, and the
final criterion. I added ordinary imports for the available proof-dependency
modules, as required by stage 2 §3(7), including the absolute-Frobenius theorem,
finite-field datum, algebraic closure and universal-homeomorphism criterion.
The original Worker report is retained as requested; this section corrects it.

There is no H3 statement mismatch, statement correction, new definition node,
dependency-module repair, hollow definition, or proved theorem. The theorem's
signature is unchanged and was checked verbatim against `lean.statement`.
All lines satisfy the 100-character limit. The only postponed proof is the
single named theorem, with its matching node and source/blueprint docstring.
