## Worker report

The module `Sheaf.AlgebraicGeometry.CurveRiemannHurwitzNumerical` states
`AlgebraicGeometry.curve_riemannHurwitz_numerical`, with its sole proof `sorry`.
No definitions, additional nodes, dependency repairs, or statement corrections are needed.
The node was read together with all nine statement dependencies, their full statements,
records, and the source definitions and docstrings used below. No repair note exists for this item.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The two schemes over that field are `(X Y : Scheme.{u})` with their respective
  `Over (Spec (.of k))` instances; `X ↘ Spec (.of k)` and `Y ↘ Spec (.of k)` are
  their structure morphisms.
- The curve conditions (separated, finite type, dimension at most one) are the two
  `IsCurve` instances. The node's dimension-one conditions are separately the exact
  equalities `hX : topologicalKrullDim X = 1` and `hY : topologicalKrullDim Y = 1`.
- Smoothness and properness are the respective `Smooth` and `IsProper` instances on
  the two structure morphisms.
- Integrality is `[IsIntegral X] [IsIntegral Y]`, and geometric integrality is the
  respective `GeometricallyIntegral` instances. Integrality supplies the nonempty
  irreducible schemes and the field structures on their generic stalks. These are
  the same integral curves of the node, not independently chosen function fields.
- The morphism is `(f : X ⟶ Y)`. Its being a k-morphism is `hf`, the equality of
  its composite with the target structure morphism and the source structure morphism.
- The node explicitly defines nonconstant as not factoring through a k-rational
  point. `hnonconstant` is exactly the negation of existence of `p : Spec k ⟶ Y`
  which is a section of the target structure morphism and whose composite with the
  source structure morphism is `f`. No replacement by an unrelated topological
  nonconstancy predicate is made.
- The extension is `[Algebra Y.functionField X.functionField]`. Its being induced
  by this particular `f` is `hfield`: the spectrum of its algebra map, followed by
  the canonical `Spec k(Y) ⟶ Y`, equals `Spec k(X) ⟶ X ⟶ Y`. This is the
  generic-point square defining pullback of rational functions. It forces the map
  on the generic stalks to be the one induced by `f` and implies dominance; it
  does not add an independent dominance hypothesis or allow an arbitrary extension.
- Finiteness and separability are precisely `Module.Finite Y.functionField
  X.functionField` and `Algebra.IsSeparable Y.functionField X.functionField`.
- The integer degree is represented by the natural-number dimension
  `Module.finrank Y.functionField X.functionField` of this finite extension.
  Its positivity is the first conjunct `0 < Module.finrank ...`.
- The existing recorded genus is `(X ↘ Spec k).genus`, respectively for Y.
  `Scheme.Hom.genus` is the dimension of global differential forms. Its docstring
  explicitly identifies it with arithmetic genus by the existing theorem
  `Scheme.genus_eq_arithmeticGenus` in
  `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`, whose signature and proof
  were read. Smooth proper integral one-dimensional curves meet the
  smooth-relative-dimension-one condition there. Thus these are exactly the node's
  dimensions of H¹(O); no new genus or cohomology definition is introduced.
- The second conjunct is `∃ r : ℤ, 0 ≤ r ∧ ...`. Its equality is exactly
  `2 * (gX : ℤ) - 2 = (d : ℤ) * (2 * (gY : ℤ) - 2) + r`.
  Every subtraction occurs in ℤ, so genus zero is retained correctly.
- There is no restriction on characteristic, tameness, or invertibility of `d`.

Dependency declarations used:

- `Field` in `Mathlib.Algebra.Field.Defs`, through the field imports, is
  def-weil-field. `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic` is the
  algebraically-closed clause of def-weil-algebraic-closure's Mathlib match.
- `AlgebraicGeometry.IsCurve` in `WeilConjectures.AlgebraicGeometry.Curve` is
  def-sc-curves. Its separate dimension-one conditions retain the node's exact scope.
- `AlgebraicGeometry.GeometricallyIntegral` in
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` is the geometric-integrality
  clause of def-pc-geometrically-irreducible; `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties` is def-pc-integral-scheme.
- `WeilConjectures.AlgebraicGeometry.FunctionField`, recorded on
  def-sc-function-field, imports Mathlib's `Scheme.functionField`. Its documentation
  explicitly directs integral schemes to this generic stalk, rather than the
  component-product carrier `Scheme.functionFieldOfComponents` used for general
  curves. The exact generic stalk and its field instance are used here.
- `Algebra` in `Mathlib.Algebra.Algebra.Defs` supplies def-pc-field-extension.
  `Sheaf.FieldTheory.FieldTower` (def-pc-field-tower) explicitly uses
  `Module.Finite`, `Algebra.IsSeparable`, and `Module.finrank` for the finite
  separable extension and its dimension; its `FieldExtension.degree` agrees with
  this dimension when finite. Its infinite-degree value is not needed because
  the node assumes finiteness.
- `Scheme.Hom.genus` in `WeilConjectures.AlgebraicGeometry.Curve` supplies
  def-sc-genus, with the existing arithmetic-genus identification above.
- `Scheme.fromSpecFunctionField` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField` is the existing
  canonical generic-point morphism needed to express the induced extension.

The stated proof dependencies are imported as plain proof imports: the recorded
EulerChar, RiemannRoch, Differentials, Invertible, InvertiblePullbackTensor,
CochainTensorUniverses, CurveDegreeTensorAdditive, and CurveSectionDegreePositivity
modules. Curve itself is already a public statement import and supplies def-sc-pic0.
The proof nodes lem-sfb-separable-curve-differential-nonzero and
lem-sfb-proper-curve-bundle-pullback-degree have no recorded Lean declarations yet,
so there are no module imports available for them. They are retained in the node's
proof dependencies and in the complete six-step proof docstring. Neither is needed
to type the present statement. No proof-dependency cycle or new assumption is used.

Edge cases checked mathematically before writing:

- Identity: d=1, r=0, with the induced field square commuting.
- A separable degree n map P¹ to P¹: genus zero gives r=2n-2 ≥ 0; the integer casts
  avoid truncated natural subtraction.
- Genus one target: the right-hand canonical-degree contribution is zero, without
  imposing genus at least two.
- Wild example t ↦ t^p-t on P¹ in characteristic p: d=p and r=2p-2. The theorem
  covers it even though p divides d; it does not replace the different by the tame sum.
- Pure Frobenius on a curve of genus at least two is excluded by separability.
- Constant maps fail hnonconstant and cannot have this induced function-field
  square. The empty scheme and dimension-zero schemes are excluded by the node's
  integrality and dimension-one assumptions, as intended. Finite extensions of
  fields have positive dimension, so d=0 is impossible.

Searches for an existing theorem:

- `msearch.py`, leanfinder: “Riemann Hurwitz formula for finite separable morphism
  smooth proper integral algebraic curves genus nonnegative different”. Eight hits,
  including FunctionField.classNumber, Weierstrass maps, relative smooth dimension,
  and number-field infinite-place ramification. None states this curve-genus formula.
- `msearch.py`, loogle: `"Hurwitz"`. Twelve hits, all HurwitzKernelBounds
  analytic theta-function estimates; none is a geometric Riemann--Hurwitz statement.
- `msearch.py`, grep in Mathlib AlgebraicGeometry:
  `[Rr]iemann.?[Hh]urwitz|genus.*ramif|ramif.*genus`. Zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for Riemann--Hurwitz,
  riemannHurwitz, Hurwitz, and the node id: only the downstream
  FiniteCurveGenusMonotonicity module's proof docstring mentions the result.
  That theorem compares genera and assumes no separability; it does not supply
  the degree-positive/nonnegative-different numerical conclusion.
- `grep -rn` of the item id in WeilConjectures and searches of
  `dag/lean_names_upstream.json` for the id and the proposed declaration return
  no match. The proposed declaration and module names are unused.

Source checked: the full Riemann--Hurwitz calculation in local Stacks curves.tex,
section-riemann-hurewitz (0C1B), and the finite-separability equivalence in
lemma-generically-etale (0C1C). They use the degree of the effective different,
without assuming tame ramification. The theorem docstring carries every step of
this node's proof, including the degree-convention comparison.

Validation: `scompile.py NU lem-sfb-curve-riemann-hurwitz-numerical` compiled both
its sandbox and library module form cleanly, with no errors or warnings (3.1 s and
2.9 s). Every variable and universe is explicitly bound. The node changes only
its `lean` field, with the exact source signature and current UTC date.

## Second reading by NU

No independent worker was started, as the dispatch brief prohibits subagents.
This is a direct worker delivery; the maintainer's independent review reads it.
