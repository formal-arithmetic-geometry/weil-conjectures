## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings` states
`AlgebraicGeometry.Scheme.smooth_connected_curve_local_rings`. It has one theorem,
whose proof is `sorry`, and introduces no definitions. The original statement and all
other node fields are preserved; only `lean` is added. No new nodes or dependency
modules are needed.

Hypotheses, matched individually:

- An algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- A scheme C over k: `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`.
  The explicit structure morphism is the form required by the recorded curve declaration.
- Separated and finite type, of dimension one, nonempty and connected:
  `[IsConnectedCurve f]`. This extends `IsCurve f`, which supplies `IsSeparated f`,
  `LocallyOfFiniteType f`, `QuasiCompact f`, and dimension at most one. The connected
  class adds `ConnectedSpace C` (including nonemptiness) and
  `topologicalKrullDim C = 1`. Its full signature and docstring were read in
  `WeilConjectures/AlgebraicGeometry/Curve.lean`.
- Smooth over k: `[Smooth f]`. Properness, affineness, and relative dimension as a
  separate structure are not assumed.

Conclusions, matched individually:

1. Integrality is `∃ hC : IsIntegral C`; the following `letI := hC` makes the
   *concluded* integrality available for the generic point, fraction field, and domain
   instances. This is not an extra hypothesis. Noetherianity is `IsNoetherian C`.
   The generic point is the canonical `genericPoint C`, with
   `IsGenericPoint (genericPoint C) (Set.univ : Set C)` explicitly asserted. Scheme
   sobriety gives uniqueness, so using this canonical point loses no choice of eta.
   Mathlib's `C.functionField` is definitionally `C.presheaf.stalk (genericPoint C)`;
   its field property is explicitly `IsField C.functionField` (and the Field instance
   supplied by Mathlib is used for integer powers). This is exactly the integral
   specialization of `def-sc-function-field`, rather than the general component product.
   For each nonempty open V and each point x in it, the germ injection is
   `∀ (V : C.Opens) (_ : Nonempty V) (x : V),
   Function.Injective (C.presheaf.germ V x x.property)`.
   The next injection is
   `∀ x : C, Function.Injective (algebraMap (C.presheaf.stalk x) C.functionField)`.
   The algebraMap is Mathlib's canonical `stalkFunctionFieldAlgebra`: it is the
   structure-sheaf specialization map from x to the generic stalk. Its compatibility
   with germs is built into `Scheme.algebraMap_germ_eq_germToFunctionField`, whose
   signature and proof were read. Thus the two maps are the actual maps in the node.
2. Nongeneric points are closed:
   `∀ x : C, x ≠ genericPoint C → x ∈ closedPoints C`.
   Eta is not closed: `genericPoint C ∉ closedPoints C`.
   A closed point exists: `∃ P : C, P ∈ closedPoints C`.
   `closedPoints C` is exactly the set of points whose singleton is closed.
3. For every `P : C` with `P ∈ closedPoints C`, the statement asserts
   `IsDiscreteValuationRing (C.presheaf.stalk P)` and
   `IsFractionRing (C.presheaf.stalk P) C.functionField`, using precisely the algebraMap
   of clause 1. The domain and local-ring structures of stalks are the existing
   Mathlib instances, with the domain following from the concluded integrality.
   A uniformizer is expressed literally by
   `IsLocalRing.maximalIdeal (C.presheaf.stalk P) = Ideal.span {t}`.
   For every uniformizer t and every nonzero function g, represented by
   `g : C.functionFieldˣ`, the `∃! q : (C.presheaf.stalk P)ˣ × ℤ` clause says that
   `(g : C.functionField) = algebraMap ... (q.1 : C.presheaf.stalk P) *
   (algebraMap ... t) ^ q.2`. Uniqueness is of the ordered pair, hence of both the
   stalk unit and the integer exponent. Exponentiation is field integer exponentiation,
   so negative exponents are included.
   The same `v : C.functionFieldˣ →* Multiplicative ℤ` is chosen *before* all
   uniformizers. Every representation has `Multiplicative.toAdd (v g) = q.2`;
   therefore the exponent is independent of t. A homomorphism to `Multiplicative ℤ`
   says exactly that v(gg') = v(g) + v(g') and v(1) = 0. Surjectivity is the explicit
   `Function.Surjective v` conjunct. Finally, for every g, existence of a nonzero
   stalk element r with `algebraMap ... r = (g : C.functionField)` is equivalent to
   `0 ≤ Multiplicative.toAdd (v g)`. This is the claimed equality of the embedded
   nonzero stalk with the nonnegative-valuation subset of the function field group.

Dependency declarations used (full declarations and docstrings read):

- `def-sc-curves`: module `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.IsCurve` and `AlgebraicGeometry.IsConnectedCurve` from that
  same recorded module; smoothness is the existing `AlgebraicGeometry.Smooth`.
- `def-pc-integral-scheme`: module `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `def-sc-generic-point`: module `Mathlib.Topology.Sober`, `IsGenericPoint`,
  with the canonical `TopologicalSpace.genericPoint` for an irreducible sober space.
- `def-sc-function-field`: imported module `Sheaf.AlgebraicGeometry.FunctionField`,
  whose recorded `AlgebraicGeometry.Scheme.functionFieldOfComponents` is for the
  general component-product notion. Its docstring and the node explicitly delegate
  the integral-scheme clause used here to `AlgebraicGeometry.Scheme.functionField`
  in `Mathlib.AlgebraicGeometry.FunctionField`; we use that existing declaration.
- `def-weil-closed-points`: module `Mathlib.Topology.JacobsonSpace`, `closedPoints`.
- `def-sc-discrete-valuation-ring`: module
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`;
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` confirms the literal
  maximal-ideal generator condition is the existing uniformizer notion.

The module docstring carries all eight proof steps of the node, with the relevant
node names, ready for stage 3. Local Stacks TeX files were absent on this machine;
read the actual sources instead at [033M](https://stacks.math.columbia.edu/tag/033M),
[02IZ](https://stacks.math.columbia.edu/tag/02IZ), and
[00PD](https://stacks.math.columbia.edu/tag/00PD). They provide respectively the
Noetherian normal decomposition, the local-ring codimension identification, and the
regular dimension-one DVR characterization used in the node's proof.

Edge cases checked before writing:

- Empty schemes and dimension-zero points are excluded by the node's connected
  dimension-one condition, exactly as by `IsConnectedCurve`; they have not been
  silently excluded by an added hypothesis.
- Affine and proper curves are both covered, as are nonproper nonaffine curves
  whenever the hypotheses hold; no completeness condition is used.
- The generic point is not among the closed points, avoiding a false assertion
  that its field stalk is a DVR.
- The empty open is excluded only in the node's germ-injectivity clause.
  Points x are in V, so each germ map is well typed. The canonical stalk injection
  exists for every point, as asserted in clause 1.
- g = 0 is excluded by the multiplicative unit group exactly as by k(C)*.
  The local nonzero subset is stated explicitly using r ≠ 0.
- For g = 1 the exponent is zero; positive and negative powers of a uniformizer
  are both allowed. Replacing t by a unit times t changes the local unit but not
  v(g); the statement does not mistakenly demand uniformizer-independent units.
- All characteristics, including positive characteristic, remain allowed.
  The standard common universe for a scheme and its base field is the same as
  the recorded curve declarations; every variable and universe is explicitly bound.

Searches (2026-10-11):

- `msearch.py ... leanfinder "A smooth connected curve over an algebraically closed
  field is integral with discrete valuation rings at closed points and normalized
  valuations on its function field"`: eight hits, including Mathlib's field
  instance for the function field; other hits were Weierstrass-curve reduction or
  normalization results. No match for the whole node.
- `msearch.py ... loogle "IsDiscreteValuationRing, AlgebraicGeometry.Scheme"`:
  one hit, `AlgebraicGeometry.Scheme.ord_add`, a valuation inequality under a DVR
  hypothesis, not the asserted conclusion for smooth connected curves.
- `msearch.py ... grep "IsDiscreteValuationRing|ringKrullDim_stalk"
  AlgebraicGeometry`: nine hits; `ringKrullDim_stalk_eq_coheight` is a tool,
  `OrderOfVanishing` assumes DVRs, and elliptic reduction results do not match.
- `msearch.py ... leansearch "smooth connected curve integral discrete valuation
  ring stalk closed point"`: UNAVAILABLE, service Internal Server Error.
  Other searches and direct source inspection supplied the search evidence.
- `rg` of `WeilConjectures/AlgebraicGeometry/Curve` for
  `IsDiscreteValuationRing|normalized.*valuation|closedPoints|genericPoint`:
  `Scheme.isDiscreteValuationRing_stalk_of_isClosed` in SerreDuality has the
  different `SmoothOfRelativeDimension 1` hypothesis and states only the DVR
  part. Other partial results include `eq_genericPoint_of_not_isClosed` and
  `genericPoint_notMem`; none states the whole node. The full signature and
  docstring of the DVR candidate were read.
- `rg` of `lean/Sheaf` for the same concepts and `IsConnectedCurve`: existing
  closed-point, genus, Picard, and DVR saturation modules; no matching theorem.
- `rg` of all `WeilConjectures` for the item ID: no hits.
- `rg` of `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`, and
  `lean/Sheaf` for `smooth_connected_curve_local_rings|SmoothConnectedCurveLocalRings`:
  no collisions with the proposed declaration or module name.

No statement dispute or node fault was found. Initial server compile passed in
2.1 seconds with no warnings or errors. The final delivery dry run is required
before the READY handoff; the independent reader supplies the second reading.

## Second reading by F1

Independent second reading, 2026-10-11. I opened the sandbox node and module,
each of its six statement dependencies, their recorded Lean definitions, and the
source declarations rather than relying on the first reader's report.

Objects and hypotheses, listed before comparing the conclusion:

- The algebraically closed field k is `(k : Type u) [Field k] [IsAlgClosed k]`:
  exact; no characteristic or perfection assumption added.
- The k-scheme C is `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`: exact, using
  the explicit morphism expected by the recorded curve classes.
- Nonempty, connected, separated, finite type, dimension exactly one is
  `[IsConnectedCurve f]`: exact. I read both class signatures in
  `WeilConjectures/AlgebraicGeometry/Curve.lean`. The parent supplies separated,
  locally finite type and quasi-compact; the child supplies `ConnectedSpace C`
  and `topologicalKrullDim C = 1`, not merely dimension at most one.
- Smoothness over k is `[Smooth f]`: exact. Integrality, regularity,
  Noetherianity, properness and relative dimension one are not hypotheses.

Every conclusion clause, with its rendering and verdict:

1. Integral and Noetherian: `∃ hC : IsIntegral C, letI := hC IsNoetherian C ∧ ...`.
   Exact: the integral instance is obtained in the conclusion. I read Mathlib's
   `IsIntegral` fields and its reduced/irreducible characterization.
2. Generic point eta: `IsGenericPoint (genericPoint C) (Set.univ : Set C)`.
   Exact: `IsGenericPoint` is equality of singleton closure with the set;
   scheme sobriety makes the canonical choice equivalent to the node's eta.
3. Function field equals the generic stalk and is a field: `IsField C.functionField`.
   Exact: Mathlib's abbreviation is literally that stalk. The recorded
   `Sheaf.AlgebraicGeometry.FunctionField` module explicitly delegates the integral
   specialization to this declaration; its product over components is not copied.
4. Every nonempty open V, x in V, has an injective germ map:
   `∀ (V : C.Opens) (_ : Nonempty V) (x : V), Function.Injective
   (C.presheaf.germ V x x.property)`. Exact, with the node's quantifier order.
5. The subsequent stalk-to-generic-stalk map is injective for every x:
   `∀ x : C, Function.Injective (algebraMap (C.presheaf.stalk x) C.functionField)`.
   Exact. I read `stalkFunctionFieldAlgebra`, built from `stalkSpecializes`, and
   `Scheme.algebraMap_germ_eq_germToFunctionField`; this is the actual germ-compatible
   map, not an arbitrary embedding of the rings.
6. Nongeneric points are closed, eta is not closed, and a closed point exists:
   the three conjuncts beginning `∀ x : C, x ≠ genericPoint C`,
   `genericPoint C ∉ closedPoints C`, and `∃ P : C, P ∈ closedPoints C`.
   Exact. Mathlib's `closedPoints` is precisely the closed-singleton predicate.
7. Each closed stalk is a DVR with the specified fraction field:
   `∀ P : C, P ∈ closedPoints C → IsDiscreteValuationRing ... ∧ IsFractionRing ...`.
   Exact. I read the DVR class (local PID domain with nonzero maximal ideal);
   the fraction ring uses the same canonical algebraMap as clause 5.
8. For each uniformizer and nonzero rational function, the unit and integer are
   uniquely determined: maximal ideal `= Ideal.span {t}`, `g : C.functionFieldˣ`,
   and `∃! q : (C.presheaf.stalk P)ˣ × ℤ` satisfying the displayed `u * t ^ n`
   equality. Exact: pair uniqueness asserts uniqueness of both coordinates.
9. The exponent is uniformizer-independent: `∃ v` precedes `∀ t`, and every
   pair giving a representation satisfies `Multiplicative.toAdd (v g) = q.2`.
   Exact: units may change with t, exponents cannot.
10. The normalized valuation is a surjective group homomorphism:
    `v : C.functionFieldˣ →* Multiplicative ℤ` and `Function.Surjective v`.
    Exact: the target wrapper expresses additive integer values.
11. The embedded nonzero stalk is precisely the nonnegative-value subset:
    `(∃ r, r ≠ 0 ∧ algebraMap ... r = (g : C.functionField)) ↔
    0 ≤ Multiplicative.toAdd (v g)`. Exact, including both directions.

Source reading: local Stacks TeX is absent, so I independently read the raw
`properties.tex`, `algebra.tex`, and `divisors.tex` from the official
stacks/stacks-project repository, alongside the rendered tags
[033M](https://stacks.math.columbia.edu/tag/033M),
[02IZ](https://stacks.math.columbia.edu/tag/02IZ),
[00PD](https://stacks.math.columbia.edu/tag/00PD), and
[0BE9](https://stacks.math.columbia.edu/tag/0BE9).
The labels are `lemma-normal-Noetherian`, `lemma-codimension-local-ring`,
`lemma-characterize-dvr`, and `lemma-local-rings-UFD-c1-bijective`.
033M assumes Noetherianity; 02IZ has no locally Noetherian assumption;
00PD identifies regular local dimension one with DVRs and gives uniformizer
factorization and extension of the valuation to fractions. 0BE9 assumes locally
Noetherian integral schemes, which are consequences here, not new hypotheses.
There is no statement correction, new node, or dependency module to review.

Edge cases: empty schemes and dimension-zero schemes are excluded by the node's
own connected-curve hypothesis. Only the stated germ clause excludes the empty
open; no extra condition is put on other opens. Zero functions are excluded
exactly by the unit group, and the nonzero stalk condition is explicit. Integer
exponents include zero and negative values; g = 1 has exponent zero. The generic
stalk is not incorrectly required to be a DVR. All field characteristics remain
allowed. Universe u is arbitrary, shared with the recorded curve declarations;
objects originally placed in different universes can both be lifted to a common
universe. There are no free universes or implicitly introduced variables.

Independent searches, with different wording from the worker:

- `msearch.py ... leanfinder "Connected smooth one dimensional scheme is integral;
  non generic points closed; fraction field uniformizer gives unique unit times
  integer power"`: eight hits, all partial integral-scheme/function-field results;
  no theorem for the whole statement.
- `msearch.py ... loogle "IsConnectedCurve"`: unknown identifier in the Mathlib
  service, zero hits; the project class was inspected directly instead.
- `msearch.py ... leansearch "normalized valuation of closed stalk of connected
  smooth curve with function field"`: service unavailable (Internal Server Error),
  recorded as unavailable, not as a negative result.
- `rg` on Mathlib algebraic geometry for `IsDiscreteValuationRing`,
  `germ_injective_of_isIntegral`, and `stalkFunctionFieldAlgebra`: existing tools
  give injectivity and fraction rings, while `ord_add` assumes a DVR. No whole match.
- `rg` on WeilConjectures curve modules and `lean/Sheaf/AlgebraicGeometry` for
  `IsConnectedCurve`, `eq_genericPoint_of_not_isClosed`, `genericPoint_notMem`,
  `normalized.*valuation`, and `unit.*uniformizer`: only partial results.
  I opened `eq_genericPoint_of_not_isClosed`, `genericPoint_notMem`, and
  `isDiscreteValuationRing_stalk_of_isClosed`. The last assumes
  `SmoothOfRelativeDimension 1` and concludes only DVR existence; none replaces
  this item. Searches for the item ID and the proposed module/declaration in
  the upstream-name index, Mathlib, WeilConjectures, and Sheaf found no collision.

No mathematical mismatch was found; no correct Lean or node text was rewritten.
All imports serve recorded notions; there is one theorem with proof `sorry`, no
hollow definition, and the declaration docstring includes the source and all eight
proof steps. The second reading adds this report only. The server single-file
compile passed in 2.0 seconds with no errors or warnings. The signature was also
read using `tools/stage2_delivery.py signature`; delivery preflight checks it
against the node's `lean.statement`.
