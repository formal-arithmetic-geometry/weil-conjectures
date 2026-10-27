## Worker report

The module `Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion` states
`AlgebraicGeometry.isStrictNormalCrossingsBoundary_iff_parameters`, with proof `sorry`.
It introduces no definitions and changes only the item's `lean` field.

Hypotheses and clauses, read against the node and Stacks etale.tex 0BI9/0BIA:

- An arbitrary regular Noetherian scheme is `{X : Scheme.{u}} [IsNoetherian X]
  (_hX : IsRegularScheme X)`. `u` is explicit and unrestricted. The recorded
  `IsRegularScheme` means locally Noetherian with regular local rings; Mathlib's
  `IsNoetherian` additionally imposes quasi-compactness, as the node requires.
- The closed subscheme is `H : X.IdealSheafData`, precisely the representation
  required by the recorded boundary definition. Its canonical closed immersion
  is `H.subschemeι`. This permits every closed subscheme, without reducedness or
  Cartier hypotheses; those are conclusions of the criterion.
- The assertion that H is a strict normal crossings boundary is exactly
  `IsStrictNormalCrossingsBoundary H`, using the dependency's declaration.
- The equivalence is `↔`, so both implications are stated.
- Every ambient point, including points outside H, is `∀ x : X`.
- An ordered full system of d regular parameters is
  `t : List (X.presheaf.stalk x)` with `IsLocalRing.IsRegularSystemOfParameters t`.
  The recorded predicate says that the entries span the maximal ideal and
  `(t.length : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)`, so d is t.length.
- The integer `0 ≤ r ≤ d` is `(r : ℕ)` and `r ≤ t.length`; the natural-number
  binder supplies the lower bound and does not exclude r = 0.
- The ideal stalk is `(H.ideal U).map (X.presheaf.germ U.1 x hx).hom` for
  an affine neighbourhood `(U : X.affineOpens) (hx : x ∈ U.1)`.
  Quasi-coherent ideal data localizes on affine opens, and affine stalks are
  localizations, so this is the ideal stalk, not an ideal on an open substituted
  for its stalk. Existentially choosing a chart adds no mathematical hypothesis:
  every scheme point has one, and this extension is independent of that choice.
- The equation `(t₁ ... tᵣ)` is `Ideal.span {(t.take r).prod}`. The bound on r
  ensures that the initial segment has exactly r entries.
- The empty product is List.prod of the empty list, hence 1. Its principal ideal
  is the unit ideal. Thus the r = 0 case expresses precisely points off H.
- The final assertion is included in the reverse implication: unfolding its
  conclusion `IsStrictNormalCrossingsBoundary H` gives `H.IsInvertible`,
  `H.radical = H`, a finite family `C : Fin n → X.IdealSheafData`, injectivity
  of component supports, integral and regular component schemes, support union,
  and regularity plus the exact dimension equality for every finite component
  intersection. Radicality gives reducedness of the closed subscheme.
  These clauses are not replaced by a weaker normal-crossings predicate.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the needed stalk
  instances come from `Mathlib.AlgebraicGeometry.Noetherian` via the regular-scheme
  dependency. No independent stalk Noetherian hypothesis was added.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, underlying the ideal-sheaf subscheme
  representation (rather than a separate choice of an unrelated map).
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.

Statement dependencies are public imports (the regular-scheme module is public
through the boundary module). Recorded proof modules are plain imports, including
`regularLocalUFDBoundaryFactorization`,
`Scheme.Modules.closedImmersion_ideal_stalk_range`,
`Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
`IsRegularLocalRing.isRegular_and_quotients_of_generators`, and
`RingTheory.exists_parameters_regularLocalQuotient`. Mathlib proof leaves are
provided by the localization, prime spectrum and Noetherian-space imports.
The theorem docstring contains all nine proof steps and their node references.

Edge cases checked before writing:

- Empty X: the pointwise equation condition is vacuous, and the boundary's empty
  component family and empty support satisfy its conditions.
- Empty boundary on nonempty X: H is the unit ideal sheaf, r = 0 gives generator 1,
  and the finite component family is empty.
- At a point outside a nonempty boundary, the ideal stalk is again the unit ideal.
- A zero-dimensional regular local ring is a field; its parameter list is empty,
  so r must be 0. A boundary cannot pass through such a point.
- r = d is permitted; the intersection quotient has dimension zero.
- Intersections with no points impose no pointwise dimension requirements; the
  empty index subset represents X and has codimension zero.
- The zero ideal defining H = X is not inadvertently accepted on nonempty X:
  products of regular parameters, and the empty product 1, are nonzero in each
  regular local domain.
- No characteristic, base field, global equation, or uniform dimension is assumed.

Searches performed with the authorized wrapper:

- `leanfinder`: "A strict normal crossings boundary on a regular Noetherian scheme
  is locally defined by a product of distinct regular system parameters".
  Result: 8 hits about standard smooth charts, reducedness, smooth loci, standard
  etale pairs and normalization; none states this equivalence.
- `loogle`: `"IsRegularSystemOfParameters", "IsStrictNormalCrossingsBoundary"`.
  Result: 0 hits.
- Mathlib `grep`: `NormalCrossing|normal_crossing|IsRegularSystemOfParameters`
  in `AlgebraicGeometry`. Result: 0 hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the boundary predicate,
  parameter predicate and criterion names: found the recorded definitions and
  other normal-crossings statements, not this criterion. Read the definition of
  `IsNormalCrossingsDivisor` too: it allows etale neighbourhoods and is not the
  ordinary-local boundary equivalence here.
- `grep -rn lem-sfb-snc-boundary-parameter-criterion lean/WeilConjectures`:
  no existing statement. The Sheaf nodal-resolution consumer mentions the lemma
  in its proof docstring but does not declare it.
- Read the full dependency signatures/docstrings and the local Stacks 0BI9/0BIA
  definitions and proof. The affine germ representation agrees with the existing
  normal-crossings definitions; no new notion or interface repair is needed.

No statement correction, disputed statement, new node or dependency repair.

Validation: scompile.py compiled this file separately in sandbox mode and at its
library module path, with no errors or warnings (3.6 s and 4.9 s).

## Second reading by N8

A separate pass by this worker compared the completed signature against the node
and opened boundary and parameter definitions; the maintainer supplies the
independent review. The ambient scheme, regularity and Noetherianity hypotheses,
closed-subscheme representation, equivalence, all ambient points, full parameter
list, allowed r interval and ideal-stalk equation all match. In particular the
local equation is an equation of ideals, not an equality to a specially normalized
generator. Taking the first r entries is no restriction because the full parameter
list is chosen existentially. The reverse implication returns the full recorded
boundary predicate, including its finite component-intersection dimension clause.
The empty-product and empty-scheme cases remain present. No mismatch or correction
was found in this second pass. All public variables and universes are explicitly
bound; no local notation, hidden instance or copied definition is used.
