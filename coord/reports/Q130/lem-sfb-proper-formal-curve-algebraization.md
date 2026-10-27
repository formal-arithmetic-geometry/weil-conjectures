## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFormalCurveAlgebraization` states
`AlgebraicGeometry.proper_formal_curve_algebraization`, with its entire proof `sorry`.
It also supplies three concrete canonical-map helpers belonging to this statement:
`formalCurveBase`, `formalCurveBaseι`, and `formalCurveBaseStep`. These definitions
have actual data, using Mathlib quotient rings, quotient homomorphisms, and `Spec.map`;
all four declarations are recorded in `lean.declarations`. No new independent notion,
new node, dependency replacement, or statement correction is needed.

I read the node's full statement, eight proof steps, source, and statement-dependency
records. The source read was `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-formal-algebraic-space-proper-reldim-1` (Tag 0E7R), including its proof,
lines 10338–10394. The source's proof assumes properness; the node already explicitly
includes it. The formal base is the one-variable specialization of the recorded
multivariate power-series definition, not a new power-series object.

Hypothesis and conclusion correspondence:

- The arbitrary field is `(k : Type u) [Field k]`. `universe u` is explicit and the
  same universe accommodates its power-series ring, quotient rings and schemes.
- `R = k[[t]]` is `PowerSeries k`, Mathlib's abbreviation `MvPowerSeries Unit k`.
  The variable is `PowerSeries.X`. The positive paper index is represented by `n+1`,
  for every `n : ℕ`; in particular no zeroth quotient or positive stage is omitted.
- `R_(n+1)` is the explicit ring
  `PowerSeries k ⧸ (Ideal.span {PowerSeries.X}) ^ (n+1)` in `formalCurveBase k n`.
  The equality `(t)^(n+1) = (t^(n+1))` identifies this with the node's notation.
  The node's alternative polynomial-quotient description names the same ring up
  to the canonical truncation isomorphism and adds no additional condition.
- The schemes and structure morphisms are `X : ℕ → Scheme.{u}` and
  `f : ∀ n, X n ⟶ formalCurveBase k n`.
- Properness is `[∀ n, IsProper (f n)]`; flatness is `[∀ n, Flat (f n)]`.
- Finite presentation is rendered in full as `LocallyOfFinitePresentation`,
  `QuasiCompact`, and `QuasiSeparated` of each `f n`, exactly the comparison clause
  of `def-sbc-locally-finite-presentation`. The latter two follow also from properness;
  they impose no restriction beyond the node's stated finite presentation.
- The supplied identifications are encoded by transition morphisms `i n` and
  `hcart : ∀ n, IsPullback (i n) (f n) (f (n+1)) (formalCurveBaseStep k n)`.
  `IsPullback` includes commutativity and the pullback universal property, so is
  equivalent to the specified isomorphism with the base change. Its uniquely
  induced iterated identifications provide all longer transitions and coherence.
  `formalCurveBaseStep` is induced by `Ideal.Quotient.factor` and the actual
  containment of consecutive powers, not by an arbitrary ring map.
- The special-fibre bound is `topologicalKrullDim (X 0) ≤ (1 : WithBot ℕ∞)`;
  `X 0` denotes paper `X_1`.
- The conclusion quantifies `Y : Scheme.{u}` and `g : Y ⟶ Spec (.of (PowerSeries k))`.
  `Flat g` is flatness; `LocallyOfFinitePresentation g ∧ QuasiCompact g ∧
  QuasiSeparated g` is finite presentation; `IsHProjective g` is exactly the finite
  projective-space embedding convention of `def-kun-projective`.
- `e : ∀ n, pullback g (formalCurveBaseι k n) ≅ X n` is the family of reductions.
  The equation `(e n).hom ≫ f n = pullback.snd g (formalCurveBaseι k n)` explicitly
  requires each isomorphism to be over `R_(n+1)`, not just an abstract scheme iso.
- The last equation says that the induced maps `X n → Y` commute with `i n`.
  Along with the preceding base equation, this is precisely compatibility with
  the canonical maps between the pullbacks: equality into the pullback is tested
  on its two projections. The second projection equality follows from `hcart.w`
  and the inverse of the over-base equation; the first is the displayed equation.
  Thus the condition includes the full transition compatibility, not only separate
  isomorphisms at each order.

Recorded statement dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, line 180, a commutative
  division ring with the nontriviality inherited from `DivisionRing`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  Mathlib.AlgebraicGeometry.Morphisms.Proper, lines 40–43, with separated,
  universally closed and locally finite type parent classes.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  Mathlib.AlgebraicGeometry.Morphisms.Flat, lines 36–46; the stalkwise equivalence
  `Flat.iff_flat_stalkMap` at lines 106–107 verifies the node's local-ring meaning.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation, lines 41–48; combined with
  quasi-compactness and quasi-separatedness for finite presentation.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, and `pullback.lift`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, lines 94–130.
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs, lines 50–64,
  supplies the universal-property form of the same fibre-product identifications.
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective, lines 30–41; it demands a
  closed immersion into projective space with a finite type of coordinates.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  Mathlib.RingTheory.MvPowerSeries.Basic, lines 84–87, and its one-variable
  abbreviation `PowerSeries`, Mathlib.RingTheory.PowerSeries.Basic, lines 58–61.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  Mathlib.Topology.KrullDimension, lines 35–40, valued in `WithBot ℕ∞`.

The recorded and available proof modules are imported non-publicly: power-series
completeness, quotient base-change ideal, ample line bundles in dimension one,
Picard lifting, tensor-pullback adjunction, flat-module powers, field flatness,
and the constant-coefficient unit criterion. The polarized formal algebraization
node has no recorded module and its anticipated source module is unavailable
(`scompile.py --source Sheaf.AlgebraicGeometry.PolarizedFormalAlgebraization`);
it is a proof prerequisite, not a notion needed to type this theorem, so no
invented import or duplicate theorem was added. The docstring carries every step
of the existing eight-step proof, including Stacks 089A at that step.

Edge cases checked before finalizing: an empty special fibre has dimension minus
infinity and satisfies the bound; the empty system and empty algebraization are
permitted. Dimension zero is included; no pure-dimension or nonempty hypothesis
appears. Arbitrary characteristic and non-algebraically-closed fields are allowed.
Index zero denotes exponent one, and all positive orders occur. There is no extra
flatness assumption on the unknown Y: it is part of the existential conclusion.
Compatibility includes the scalar maps, preventing non-base-linear automorphisms
of the quotients from serving as the claimed identifications. All auxiliary maps
are concrete definitions; there are no choices from unproved existence results.
No mathematical fault or disputed statement was found.

Searches performed:

- `msearch.py ... leanfinder`: “A compatible proper flat formal curve over k[[t]]
  with special fibre dimension at most one admits a projective flat finitely
  presented algebraization”. Eight hits included `Flat`, universally open flat
  morphisms, Proj properness and smoothness approximation; no matching algebraization.
- `msearch.py ... loogle`: `PowerSeries, AlgebraicGeometry.IsHProjective`.
  No hits; service reported unknown identifier `AlgebraicGeometry.IsHProjective`.
- `msearch.py ... leansearch`: “proper formal curve projective algebraization
  complete local ring dimension one”. Eight hits included Proj, its properness,
  DVR cotangent dimension and smooth loci; none states this theorem.
- `msearch.py ... grep`: `algebraiz|algebrais|[Ff]ormal[Cc]urve`, restricted to
  Mathlib AlgebraicGeometry. Twenty-five hits use the `algebraize` tactic; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for formal algebraization/curve
  names, plus the exact item id in `lean/WeilConjectures`: found coherent-module
  algebraization and the smoothing parent, no declaration stating this theorem.
  Searches for `formalCurveBase` and `proper_formal_curve_algebraization` in both
  roots and `dag/lean_names_upstream.json` found no name collision.

Validation: `scompile.py Q130 lem-sfb-proper-formal-curve-algebraization <module>`
compiled both sandbox and library modes cleanly, 2.2 seconds each. No errors or
non-sorry warnings. `autoImplicit` is explicitly false. All theorem proofs are
whole `sorry` proofs, and definitions contain no postponed proof or data.

## Second reading by Q130

I reread the node and the completed file after compilation. This is a separate
self-review pass; the dispatched brief forbids starting another agent, so it is
not represented as an independent-agent review. The maintainer's independent
review remains the external second reading.

I checked the index shift and first quotient, all three finite-presentation
components on both sides, and the exact H-projective predicate rather than a
weaker projectivity convention. The three helper definitions give precisely the
base quotient and its canonical maps. I checked that `IsPullback` is ordered with
`X n` at the upper left and `Spec R_(n+2)` at the lower right, and that the
compatibility equation uses the inverse isomorphisms in the correct direction.
The over-base equation is present independently of the transition equation;
therefore no scalar-linearity clause is missing. The dimension convention
includes the empty case. No statement mismatch required a correction. The sole
postponed theorem and all helpers name this node and its source in their
docstrings. Only the node's `lean` field changed.
