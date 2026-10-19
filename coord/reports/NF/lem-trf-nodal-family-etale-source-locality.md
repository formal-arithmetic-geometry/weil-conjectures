## Worker report

The module `Sheaf.AlgebraicGeometry.NodalFamilyEtaleSourceLocality` states
`AlgebraicGeometry.isNodalRelativeCurve_iff_etale_source_cover` with proof `sorry`.
The real predicate `AlgebraicGeometry.IsNodalRelativeCurve` names the notion explicitly
introduced by the item's own sentence “Call a morphism nodal of relative dimension one…”.
It is a helper owned by this item, rather than a new independent notion or a copy of
`HasNodalGeometricFibres`: that existing predicate requires connected, nonempty fibres,
which this node does not require. There are no postponed helper theorems or hollow data.

Read the full item and its statement dependencies, the recorded declarations and their
docstrings, Stacks `curves.tex`, `lemma-nodal-family`, `definition-nodal-family`,
`lemma-nodal-family-precompose-etale` and `lemma-nodal-family-etale-local-source`
(Tags 0C59/0C5A, 0C5C and 0C5D). The theorem follows the last lemma exactly.
No statement correction, new node or dependency repair is needed.

Hypotheses and clauses, individually matched:

- Schemes and the morphism `f : X → S` are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The arbitrarily indexed family is `(I : Type v) (U : I → Scheme.{u})`
  and `(h : ∀ i : I, U i ⟶ X)`. The independent index universe imposes no bound
  on the cardinality of the covering family.
- Each family member is étale: `hetale : ∀ i : I, Etale (h i)`.
- Every point of X has a lift: `hcover : ∀ x : X, ∃ (i : I) (y : U i), h i y = x`.
- Flatness in the inline nodal notion is `Flat f`.
- Local finite presentation is `LocallyOfFinitePresentation f`.
- Each algebraically closed geometric base field and point is quantified by
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S)`.
  These are the usual geometric tests in the scheme universe, without a smaller
  independent field universe that could make the tests vacuous.
- The geometric fibre scheme is `pullback (C := Scheme.{u}) f g`, with structural
  map `pullback.snd f g`.
- Pure dimension one for each nonempty fibre is
  `Scheme.IsPureDimension (pullback (C := Scheme.{u}) f g) 1`.
  The same assertion is true on empty fibres because there are no irreducible
  components; thus this formulation does not strengthen the nonempty-fibre clause.
- Every nonsmooth point is expressed by quantifying `x` in that same fibre and
  negating `∃ V : (pullback f g).Opens, x ∈ V ∧ Smooth (V.ι ≫ pullback.snd f g)`.
  This means failure of smoothness on any neighbourhood of the point, with no
  closed-point or rational-point restriction and no assertion about a neighbourhood
  of its image on the base.
- Its completed local ring is `AdicCompletion (IsLocalRing.maximalIdeal
  ((pullback f g).presheaf.stalk x)) ((pullback f g).presheaf.stalk x)`.
- The prescribed ring is `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`;
  `Nonempty (... ≃+* ...)` states the isomorphism of the completed local rings
  required by the node, without choosing arbitrary ring data.
- The equivalence is `IsNodalRelativeCurve f ↔ ∀ i : I,
  IsNodalRelativeCurve (h i ≫ f)`. Categorical composition is in the order h_i then f.
- No quasi-compactness, separatedness, Noetherian, properness, connectedness,
  surjectivity of f, or nonemptiness assumption occurs.

Statement dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.snd` for geometric fibre schemes.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` on
  fibre open neighbourhoods.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, its
  ring structure, and the maximal ideal of the scheme stalk.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`;
  `Ideal.span` and the quotient use Mathlib's existing constructions.

The public mathematical dependencies are all available through the imports. The
already-stated proof dependencies are imported as the stage-3 plan:
`RelativeFlatnessSourceCover`, `Sites.MorphismProperty`, `FiniteStability`,
`Noetherian`, `FlatCompositeFibreDimensionAtPoint`, `EtaleSmoothZeroDimensionalFibres`,
`EquidimensionalOpenLocalDimension`, `ConstantLocalDimensionComponents`.
The node's other proof dependencies (lfp-fppf source locality, étale source smoothness,
and nodal point étale locality) currently have no Lean declaration in the DAG and
are named in the nine-step proof docstring; they are not needed to type this statement.

Edge cases checked against the definition and Stacks:

- `I` may be empty. Then `hcover` implies X has no points, while the universal
  conclusion has no indices to test.
- If X is empty, every U_i is empty because it maps to X; flatness and local finite
  presentation are local conditions, and geometric fibres have no points/components.
- Empty geometric fibres and disconnected fibres are permitted. Purity is measured
  component by component, never by total dimension alone.
- A smooth pure one-dimensional fibre satisfies the condition with no nodes to test.
  A zero-dimensional nonempty smooth fibre fails the pure-dimension clause.
- Every nonsmooth point is tested, not just closed points. No characteristic assumption
  or restriction on the number of components appears; the Fin 2 indices mean exactly
  the two local formal variables, not a two-point fibre.

Searches actually run through `msearch.py NF lem-trf-nodal-family-etale-source-locality`:

- LeanFinder, `Nodal family of curves is etale local on the source`: eight hits about
  étale morphisms, smoothness and ring-map locality, none about nodal families.
- LeanSearch, the same query: eight hits about local morphism properties and étale
  schemes, none stating the node.
- Loogle, `"nodal"`: twelve hits concerning Lagrange interpolation, no geometric notion.
- Grep, `nodal|semistable|0C5D`, Mathlib `AlgebraicGeometry`: zero hits.
- Direct `rg` for `nodal|Nodal` in the upstream WeilConjectures sources: no hit.
  The node-id grep in upstream sources also gives no hit. The upstream name table
  and direct source/Mathlib/project searches for the two proposed declaration names
  give no collision.
- Direct `rg` in project `lean/Sheaf` located `HasNodalGeometricFibres` (connected and
  nonempty, unusable here) and the nodal local-model theorem (a chart theorem, not
  this source-cover equivalence). The full signatures and docstrings were read.
  `Scheme.IsPureDimension` is reused, including its empty-scheme convention.

Validation: `scompile.py NF lem-trf-nodal-family-etale-source-locality` successfully
compiled both its sandbox probe and the delivery's real module path, with no errors
or non-sorry warnings. Initial compilation with a `module` header exposed the
pre-existing legacy-format `FlatCompositeFibreDimensionAtPoint` proof dependency.
The delivered file uses the compatible legacy import format so it can retain all
available proof imports without changing any shared dependency.

## Second reading by NF

No independent worker second reading was performed: the dispatcher explicitly says
not to start other agents and that the maintainer independently reviews this delivery.
I reread the node and final file, checked each clause using the correspondence above,
and checked the source's empty-family case. The one implementation adjustment was
using legacy file format to import the recorded legacy proof dependency. No mathematical
hypothesis or conclusion changed, and the connected/nonempty predicate was deliberately
not substituted for the node's own broader inline definition.
