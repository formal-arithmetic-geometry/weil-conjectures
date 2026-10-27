## Worker report

`Sheaf.Geometry.Manifold.KahlerLaplacianIdentity` states
`ComplexManifold.kahler_laplacian_identity`, with one postponed theorem and no proved
lemmas. The node's natural-language statement and proof are unchanged. The statement
expands both Laplacians directly as compositions of the specified operators.

Clause correspondence:

- The complex field is Mathlib `ℂ`, with its existing `Field` instance, as required by
  `def-weil-field` (`Mathlib.Algebra.Field.Defs`, `Field`; signature and docstring read).
- A complex manifold without boundary of dimension n is `(n : ℕ)`, `(M : Type u)`,
  `[TopologicalSpace M]`, `[ChartedSpace (Model n) M]`, and
  `[IsManifold (𝓘(ℂ, Model n)) ∞ M]`. The full-space model has no boundary.
  `[T2Space M]` is the Hausdorff condition in the usual manifold convention, not a
  compactness condition. No second countability or nonemptiness is assumed.
- The positive smooth Hermitian metric is `(g : HermitianMetric n M)`; its `hermitian`,
  `positive`, and `smooth` fields impose precisely those conditions. Kähler closedness
  is `(hclosed : IsKahlerMetric g)`, the cyclic coordinate equation for dω=0.
- Smooth complex forms and their type subspaces are the existing `smoothForms` and
  `typeForms`; the operators act on the former and their bidegrees use the latter.
  The former is constructed from actual real alternating tensors with smooth
  holomorphic-chart coefficients, not an arbitrary vector space.
- The exterior differential is `D.dbar + D.del`. The new presentation fixes its
  degree-zero output to zero and every positive-degree chart coefficient to Mathlib
  `extDerivWithin`; `dbar_type` and `del_type` fix its type components. The zero-degree
  equation is essential: the old coordinate equation only specifies degrees k+1.
- The metric volume is `(μ : MetricVolume g)`, with chart density sqrt(det(Re g));
  `[MeasurableSpace M] [BorelSpace M]` express its ordinary Borel measurable structure.
  Pairings are the existing inverse-Gram tensor contraction and integral `l2Pair`.
- The formal adjoints in the node are `D.dAdjoint` and `D.dbarAdjoint`. Their fields
  `formal_dAdjoint` and `formal_dbarAdjoint` use `IsSmoothFormalAdjoint`: every smooth
  first input with `HasCompactSupport (fun x ↦ fun k ↦ α.val k x)` and every smooth
  second input satisfy the integral adjoint identity. This implies the usual
  compact/compact test identity and pins the operator on arbitrary smooth inputs.
  It does not demand integrability of an arbitrary global L² pairing: compact first
  inputs make the tested integrands compactly supported by locality of the canonical
  derivative, and the other side contains the compact first input itself.
- The left side is `(D.dbar + D.del).comp D.dAdjoint +
  D.dAdjoint.comp (D.dbar + D.del)`, exactly dd*+d*d. The right side is `(2 : ℂ) •
  (D.dbar.comp D.dbarAdjoint + D.dbarAdjoint.comp D.dbar)`, exactly twice the
  Dolbeault Laplacian. Equality is equality of complex linear maps on all smooth forms,
  not merely equality on compact supports or harmonic forms.
- There is no `CompactSpace`, completeness, connectedness, positivity of n, or L²
  membership hypothesis.

Dependency declarations read and used:

- `Sheaf.Geometry.Manifold.HermitianDolbeaultData`: `ComplexManifold.Model`,
  `FormFields`, `smoothForms`, `typeForms`, `formCoordinates`, `HermitianMetric`,
  `MetricVolume`, `pointwiseFormPair`, `l2Pair`. Its `DolbeaultOperators` was also read;
  its all-smooth adjoint identity is unsuitable for this noncompact node.
- `Sheaf.Geometry.Manifold.KahlerCoordinateData`: `ComplexManifold.IsKahlerMetric`,
  whose defining fundamental form and cyclic derivative formula were read.
- Mathlib `extDerivWithin` from `Analysis.Calculus.DifferentialForm.Basic` supplies
  actual coordinate exterior differentiation. Mathlib `HasCompactSupport` from
  `Topology.Algebra.Support` uses compact closure of the nonzero set.
- The added definition node supplies `ComplexManifold.IsSmoothFormalAdjoint` and
  `FormalDolbeaultOperators`; all its data and predicates are written in full.

Both proof dependencies (`lem-sfb-dolbeault-acyclic-resolution` and
`lem-sfb-kahler-first-order-commutators`) have no usable Lean record in the read DAG.
They are not used to introduce any object in the statement and therefore need no
prerequisite interface here. Their future proof imports must be added when stated.
The theorem docstring carries the entire five-step proof from those dependencies,
including compact-test uniqueness, mixed-term cancellations and the final expansion.

Edge cases checked before writing: the empty manifold gives zero spaces; n=0 has
only degree-zero alternating tensors, and the new `exterior_zero` law prevents a
spurious degree-zero differential. Exterior degrees above 2n vanish as alternating
tensors on a 2n-dimensional real vector space. `typeForms` explicitly gives zero for
negative or excessive bidegrees, so bottom/top degrees are covered. Arbitrary
noncompact manifolds and forms with infinite global integral norm remain covered;
only the adjoint tests have compact support. The abstract operator fields carry
canonical coordinate and integral characterizations, never the desired identity.

Searches before writing:

- msearch LeanFinder: “On a Kahler manifold the de Rham Laplacian on smooth complex
  differential forms is twice the Dolbeault Laplacian”: eight hits, only Euclidean
  function Laplacians, `Complex.kahler`, and coordinate `extDeriv`; no match.
- msearch Loogle: `"laplacian", "form"`: zero hits.
- msearch grep: `Dolbeault|Kahler.*[Ii]dentit|Kaehler.*[Ii]dentit|HermitianMetric`:
  only `Orientation.kahler_mul`, unrelated two-dimensional linear algebra.
- msearch LeanSearch for compact-test formal adjoints returned `LinearPMap.IsFormalAdjoint`
  and Hilbert-space adjoint APIs. Their domains are inner product spaces, not the
  actual smooth forms with compact-test integration; no exact declaration.
- msearch LeanFinder for Dolbeault/bidegree/compact-test operators returned coordinate
  exterior derivatives only. Loogle `"IsFormalAdjoint"` returned four partial-linear-map
  results. Mathlib/Geometry grep `FormalAdjoint|DolbeaultOperators|dbar|KahlerMetric`
  returned zero hits. Full results are recorded in the new definition node.
- `rg` through project `lean/Sheaf` found the two geometry definition modules above,
  reused here. `rg` through `lean/WeilConjectures` found no analytic Dolbeault/Laplacian
  declaration; searching that tree for this item's id also found none.
- DAG grep found `def-sfb-hermitian-dolbeault-data` and `def-sfb-kahler-coordinate-data`,
  added to stmt_deps. `blueprint_refs.py search` for “formal adjoint” and “Dolbeault”
  returned zero matches. No existing definition gives the compact-test presentation.

The source PDF was opened online at the node's exact URL. Proposition 6.12 on PDF
page 26 (zero-based page 25) states the factor 1/2 equality and its local normal-chart
proof. Sections 3.1 and 6.1 give the type differential and metric adjoint conventions.
No statement correction or disputed mathematical claim is needed.

Validation: both delivered modules compiled individually in dependency order using
`scompile.py`, clean without warnings. Only `kahler_laplacian_identity` has `sorry`.
All variables and universes are explicitly bound; module mode is used throughout.

## New nodes

`def-sfb-formal-dolbeault-operators` defines compact-test formal adjointness and a
normalized presentation of the canonical Dolbeault/type exterior differential and
the adjoints of d and bar∂, on the already existing smooth forms, metric and volume.
Source: Kong §§3.1, 6.1, 6.4, Proposition 6.12, with the item's explicit noncompact
compact-test convention. The old `DolbeaultOperators.formal_adjoint` quantifies over
all smooth pairs: on noncompact manifolds integration by parts is not an identity
of arbitrary (possibly divergent, Lean-totalized) global integrals. It cannot be
used as a hypothesis of this item. Reusing its underlying constructions while
supplying the missing compact-test notion avoids restricting to compact manifolds
or adopting arbitrary maps. The new record is not a second definition of smooth
forms, types, metrics, volumes, pairings, or Kähler closedness. Search details and
unaltered msearch outputs are in its `mathlib_searches`; it has no postponed theorem.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
