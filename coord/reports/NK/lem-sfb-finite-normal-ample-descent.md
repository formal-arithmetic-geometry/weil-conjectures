## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteNormalAmpleDescent` states
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_finite_surjective_normal`.
Its sole theorem has proof `sorry`; there are no definitions, auxiliary theorems,
new nodes, dependency repairs, or statement corrections.

Source read: `literature/stacks-project/divisors.tex`, Tag 0BD4,
`proposition-push-down-ample`, case (2), and its proof; also Tag 0BD0,
`lemma-norm-ample`, and the adjacent norm lemmas 0BCY, 0BCZ, and 0BD3.
The node is precisely the existence assertion of case (2).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and their morphism: `{X Z : Scheme.{u}} (f : X ⟶ Z)`.
  The universe `u` is explicitly declared and unrestricted.
- Finiteness of the morphism: `[IsFinite f]`, Mathlib's affine-local finite-ring-map
  definition, exactly the finite part of `def-weil-finite-integral-morphism`.
- Surjectivity: `[Surjective f]`, surjectivity of the underlying point map.
- Integrality of the target: `[IsIntegral Z]`, including nonemptiness; no
  integrality or reducedness hypothesis is put on `X`.
- Normality of the target: `hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
  IsIntegrallyClosed (Z.presheaf.stalk z)`. These are exactly its local rings,
  each required to be an integrally closed domain. This uses the recorded
  inline normal-domain form, without introducing a second normality definition.
- Existence of an ample invertible module on `X`: the hypothesis
  `hX : ∃ L : X.Modules, ∃ hL : L.IsInvertible, @IsAmple X L hL`.
  The dependent existential supplies the invertibility instance explicitly.
- Existence of an ample invertible module on `Z`: the conclusion
  `∃ N : Z.Modules, ∃ hN : N.IsInvertible, @IsAmple Z N hN`.
  The conclusion concerns existence and imposes no descent datum or requirement
  that a specified bundle pull back to `L`.
- There are no extra flatness, group-action, Noetherian, properness, finite-type,
  base-field, separatedness, or characteristic binders. The finiteness of `f`
  of course already has its usual consequences.

The dependency declarations and their source signatures/docstrings were read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom` (locally ringed spaces locally affine, and their maps).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  with Mathlib's `IsDomain` this renders each stalk's normal-domain condition.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, local triviality of rank one.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`. Its two clauses are quasi-compactness
  and an affine nonvanishing neighbourhood from a positive tensor power at every
  point. This is the absolute predicate required here, not the separate relative
  notion in `Modules.Ample`.

All these statement dependencies are public imports. Available proof dependencies
are ordinary imports: the reduced induced closed subscheme module, closed-immersion
ample restriction, finite principal affine section neighbourhoods, affine intersection
with a section locus, and Mathlib proper/quasi-finite morphisms. Scheme sobriety,
integrality, closed-immersion finiteness and composition are already provided by the
imported Mathlib modules. The two proof nodes
`lem-sfb-normal-integral-finite-sheaf-norm` and
`lem-sfb-finite-norm-invertible-sections` have no Lean records yet, so their modules
cannot be imported. They are named in the seven-step proof docstring, and all DAG
proof dependencies remain unchanged. They are not needed to type this statement.

Edge cases checked before writing:

- Empty `Z` is excluded by the node's integrality assumption itself. Empty `X`
  cannot surject onto nonempty `Z`; no extra nonemptiness hypothesis is needed.
- The identity map gives the same ample-existence proposition on both sides.
- A finite field extension gives finite surjective spectra with normal integral
  target, and both spectra have an ample structure sheaf, in all characteristics.
- Reducible or nonreduced `X`, and finite maps that are not flat, remain in scope;
  the proof's passage to an integral reduced closed subscheme is not a hypothesis.
- The conclusion chooses one invertible module on `Z`. The proof docstring fixes
  its norm construction before selecting positive powers and sections.
- No `n = 0` shortcut changes ampleness: the imported absolute predicate requires
  `0 < n` for its section neighbourhoods.

Searches actually run with `msearch.py NK lem-sfb-finite-normal-ample-descent`:

- LeanFinder: `A finite surjective morphism to an integral normal scheme descends
  existence of an ample invertible sheaf`. Eight hits, concerning normalization,
  integral morphisms, and finite morphisms; none states ample existence descent.
- LeanSearch: `Existence of an ample invertible sheaf descends along a finite
  surjective morphism onto a normal integral scheme`. Eight hits, including flat
  descent of morphism properties, finite affine morphisms, and normalization;
  none matches this theorem.
- Loogle: `AlgebraicGeometry.Scheme.Modules.IsAmple, AlgebraicGeometry.IsFinite`.
  Zero hits; it reports unknown identifier for the project-only `IsAmple`, so this
  query alone gives no evidence of absence. The source searches below supply that.
- Mathlib grep: `ample.*finite|finite.*ample|ample.*surj|normal.*ample`, restricted
  to `AlgebraicGeometry`. One hit, an unrelated introductory sentence in
  `Morphisms/AffineAnd.lean:22`; no theorem match.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for the same words, `IsAmple`, and normal-stalk
  signatures: found the reused absolute ampleness definition, section lemmas,
  and finite-surjective reflection of ampleness of a specified pullback. The
  reflection theorem assumes a bundle downstairs, and does not give existence
  downstairs for an arbitrary bundle upstairs, so it is not this statement.
  `IntegralDimOneAmple` proves existence only for Noetherian separated curves.
  Normal-scheme interfaces use the same stalk predicates used here.
- `grep -rn 'lem-sfb-finite-normal-ample-descent' lean/WeilConjectures`:
  no hits. `rg` for the proposed declaration name and finite/normal/ample word
  combinations in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing declaration of this theorem.

No mathematical node fault or disputed statement was found. The example
`Sheaf.CategoryTheory.CompactObject` is now a withdrawn module with no declarations;
this delivery follows the current required module/public-import/exposed-section
convention and the extant ample modules instead.

Validation: `scompile.py` compiled the delivered module as both
`Sheaf.Stage2.Sandbox0` and `Sheaf.AlgebraicGeometry.FiniteNormalAmpleDescent`
on the server, each in 2.3 seconds, with no errors or unexpected warnings.
`set_option autoImplicit false` prevents auto-bound variables. All Lean lines
are at most 100 characters. Only the node's `lean` record changed, with the
signature copied verbatim from the file and the UTC date 2026-10-22.

## Second reading by NK

Author's final rereading, not an independent review; the dispatcher brief assigns
independent review to the maintainer and forbids starting another agent.
With both the node and Lean file open, I checked the seven binders/conditions
above and the dependent existential conclusion against 0BD4(2). In particular,
`hZ` quantifies over every target stalk; `[IsIntegral Z]` does not accidentally
restrict the source; `hX` asserts existence rather than a prescribed bundle;
and the conclusion introduces a new bundle rather than a pullback isomorphism.
No mismatch was found and no mathematical change was made. The sole `sorry`
is the named theorem carrying the node's complete seven-step proof docstring.
