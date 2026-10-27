## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothPointedCurvesDense` states
`AlgebraicGeometry.exists_smooth_pointed_curves_dense`, with `sorry` as its only proof.
It defines no new notions. The item's JSON changes only in `lean`.

The node and Lean agree hypothesis by hypothesis and clause by clause:

- An algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The scheme over this field is `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`.
- Smoothness is `[Smooth f]`; separatedness is `[IsSeparated f]`, whose defining
  field is `IsClosedImmersion (pullback.diagonal f)`, exactly the node's convention.
- Geometric integrality is `[GeometricallyIntegral f]`. This is the existing
  Mathlib geometric-integrality predicate, testing integral geometric field fibres.
- Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`, as the recorded
  dependency explicitly prescribes.
- The fixed rational point is `(x₀ : f.fieldPoints k)`. These are sections of the
  structure morphism, the rational-point encoding used and documented by
  `Scheme.Hom.baseChangeFieldPoint` in the recorded dependency module.
- The existential set and family of schemes are `∃ (I : Type u) (C : I → Scheme.{u})`.
  The structure morphisms are `g : ∀ i : I, C i ⟶ Spec (.of k)`.
- The rational points are `c : ∀ i : I, (g i).fieldPoints k`, so they are rational
  for the chosen structure morphisms, not arbitrary scheme-valued points.
- For each index, `IsCurve (g i)` supplies separatedness, locally finite type,
  quasi-compactness and dimension at most one. `Smooth (g i)` and
  `GeometricallyIntegral (g i)` give the two further geometric conditions.
  `topologicalKrullDim (C i) = 1` strengthens the curve dimension bound to the
  dimension exactly one required by the node.
- The maps are `ι : ∀ i : I, C i ⟶ X`. The equation `ι i ≫ f = g i` makes each
  one a k-morphism. The equation `(c i).1 ≫ ι i = x₀.1` is exactly `u_i(c_i)=x_0`
  as equality of rational-point morphisms. No immersion or nonconstancy is required.
- The final clause `Dense (⋃ i : I, Set.range (ι i))` uses the underlying point maps
  of the scheme morphisms and says that the union of their images has closure all
  of the underlying space of X.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (available through the imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed
  predicate explicitly identified in `def-weil-algebraic-closure.mathlib_match`.
  The algebraic closure construction itself is unnecessary: k is already closed.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.DensePoints`: the rational-point encoding
  documented at `Scheme.Hom.baseChangeFieldPoint`; the theorem uses its input
  type `f.fieldPoints k` directly, without a private rational-point definition.
- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`.

Proof dependencies already stated are imported non-publicly:
`Mathlib.AlgebraicGeometry.Noetherian` for finite type over a Noetherian base,
`Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete` for
`finite_and_discreteTopology_of_topologicalKrullDim_le_zero`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` for
`AffineSpace.smoothOfRelativeDimension_over`, and
`Mathlib.RingTheory.KrullDimension.Polynomial` for
`MvPolynomial.ringKrullDim_of_isNoetherianRing`. The two other proof nodes,
`lem-sfb-point-tangent-cone-dimension` and
`lem-sfb-smooth-prescribed-tangent-hypersurface`, have no recorded declaration
or Mathlib match; there is consequently no module to import for them. They
are proof prerequisites, not missing objects needed to type this statement.
The docstring carries all four steps of the node's induction and indexing proof.

Edge cases checked before writing:

- Dimension-zero X is included: there is no positivity condition on X and no
  nonconstancy condition on the maps. The affine line with its zero point and
  the constant map to x₀ is an eligible witness for the singleton target.
- If X has dimension one, the singleton family with C=X and the identity map
  is eligible, demonstrating that no projectivity or properness was introduced.
- The empty scheme has no rational point and is already excluded by x₀ (also
  by geometric integrality over this field); no separate nonemptiness hypothesis
  was added. Curves must have dimension one and rational marked points.
- An empty index is not prohibited by an extra binder, but cannot have dense
  union in a nonempty X; the conclusion itself enforces what is needed.
- Positive characteristic is allowed without restrictions. Smoothness and
  geometric integrality are stated over k, not replaced by generic smoothness.
- `I : Type u` suffices: nonempty opens of the underlying space form such a
  set, and the node's last proof step selects one eligible curve for each.
  The field and schemes share the usual scheme universe u; no independent,
  possibly too small test-field universe is introduced.

Searches (the msearch wrapper also recorded the exact outputs in searches.jsonl):

- `msearch.py ... leanfinder "The union of images of smooth geometrically integral
  curves mapping to a smooth variety through a fixed rational point is dense"`:
  eight hits about dense domains of rational/partial maps and dominance; none
  states density of a family of pointed curve maps.
- `msearch.py ... loogle '"IsCurve", "Dense"'`: zero hits.
- `msearch.py ... leansearch "Images of smooth curves through a prescribed point
  are dense in a smooth variety"`: eight hits, including Dense, DenseRange image
  facts, rational-map dense domains and differential-geometric integral curves;
  no algebraic-geometric pointed-curve density theorem.
- `msearch.py ... grep 'smooth.pointed|pointed.curve|curves.*dense|dense.*curves'
  AlgebraicGeometry`: zero Mathlib hits.
- Source `rg` for `smoothPointed|smooth_pointed|pointed.*dense|curves.*dense` in
  both `lean/WeilConjectures` and `lean/Sheaf`: only unrelated pointed condensed
  sets and trace-function documentation. Source search for the node id in
  `lean/WeilConjectures`: no hits. Search for the chosen declaration name in
  Mathlib and both project roots: no existing declaration.
- Read the complete `IsCurve` class and its documentation (including its
  separatedness/finite-type inheritance), and the recorded rational-point
  dependency's full signature and documentation, before using them.

Source checked directly with `pdftotext`: Milne, Abelian Varieties, PDF pages
24–25, printed pp.18–19, Lemmas 3.5(b), 3.6 and proof of Theorem 3.4. The
node's explicit dimension-zero addition is valid. The latest blueprint's
direct-images proof (3) was read; it is the historical context recorded in
this node, not an alternative statement of this auxiliary geometric lemma.
No statement dispute or correction is needed.

Validation: scompile.py compiled this single module in sandbox and library
modes successfully, with no errors or unexpected warnings. Every universe and
variable is explicit, and `set_option autoImplicit false` enforces this.

## Second reading by Q21

Final rereading by the assigned worker; no independent second agent was started,
as the dispatcher expressly prohibits this. The maintainer's independent review
remains the independent reading. I reopened the node and completed module and
checked every item in the correspondence above. In particular, `IsCurve` alone
would allow dimension zero, so the explicit `topologicalKrullDim = 1` conjunct
is present; fieldPoints alone does not make a map a k-morphism, so the explicit
`ι i ≫ f = g i` equation is present; density uses the entire underlying curves,
not only their rational points. Both the constant-map case and the index set
are preserved. There were no mathematical mismatches to repair. One leading
space in the declaration docstring was removed after the first successful
compile; the prescribed dry run recompiles the final file.
