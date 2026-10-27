## Worker report

The item is stated by `ComplexManifold.dolbeault_laplacian_elliptic` in
`lean/Sheaf/Geometry/Manifold/DolbeaultLaplacianElliptic.lean`. Its only postponed
proof is this theorem. The coordinate definitions are in the new definition node
`def-sfb-form-differential-expressions`, with its own module
`lean/Sheaf/Geometry/Manifold/FormDifferentialExpressions.lean`.

I read the source online: Wenrui Kong, Notes on Complex Geometry, April 9, 2025,
https://cims.nyu.edu/~wk805/files/Complex_Geometry_Notes.pdf, §3.1 for types,
§6.1 Lemma 6.2, printed p.21, and §6.2, the symbol definition and Lemma 6.4,
printed p.23. In particular the source computes the scalar degree-two symbol,
with the factor one half for the Dolbeault Laplacian. The node asks for its
invertibility, rather than for that numerical normalization. The actual
coefficient-based symbol below uses the node's convention without a factor of i.
I also read the current blueprint unit `sk-thm-sf-ctf-stability/_section.md`
and its direct-images proof. This item is an analytic prerequisite in the DAG's
long recorded dependency chain, not the statement of that blueprint unit.

### Hypotheses and objects, clause by clause

- A compact complex manifold without boundary of dimension n at least one:
  `n : ℕ`, `hn : 1 ≤ n`, arbitrary-universe `M : Type u`,
  `[ChartedSpace (Model n) M]`, `[IsManifold (𝓘(ℂ, Model n)) ∞ M]`,
  `[T2Space M]`, and `[CompactSpace M]`. `Model n` is exactly `Fin n → ℂ`.
  The identity complex model has no boundary or corners. No connectedness,
  projectivity, Kähler condition, or Nonempty assumption is imposed.
- The scalar field is the actual Mathlib complex field. The original dependency
  `def-weil-field` has `mathlib_match = ["Field"]`, not a Lean record. I read
  `Mathlib/Algebra/Field/Defs.lean`, lines 175–180: `Field` extends the commutative
  ring and division-ring structures. Complex scalars and real differentiation
  are already supplied by the public imports of HermitianDolbeaultData.
- Smooth positive definite Hermitian metric: `g : HermitianMetric n M` reuses
  its Hermitian matrix, positivity for every nonzero tangent vector, and
  smoothness in every holomorphic atlas chart. This is not an abstract pairing.
- The metric volume is `μ : MetricVolume g`, whose chart density is the square
  root of the real metric determinant. `[MeasurableSpace M] [BorelSpace M]`
  choose the Borel measurable structure needed for integration; they add no
  restriction to the underlying complex manifold.
- Types p and q between zero and n: `∀ (p q : ℤ), 0 ≤ p → p ≤ n →
  0 ≤ q → q ≤ n → ...`. Integers allow the adjacent types and the zero convention.
- The E^{p,q} bundle and its smooth section space are the existing
  `typeForms p q`: actual smooth alternating tensor fields supported in total
  degree p+q and satisfying the complex-structure eigenspace equation.
  This is the alternating-tensor presentation of the exterior powers of the
  i and -i cotangent eigenspaces, not a new abstract form space.
  `typeForms` is bottom outside the permitted index range.
- Canonical D and its adjoint: the conclusion begins `∃ D : DolbeaultOperators g μ`.
  Thus adjoint existence is a conclusion, not a premise. I read the full
  existing structure and its docstring. Its `dbar_type`, `del_type` and
  `exterior_derivative` fields say that dbar and del are the two type components
  of the actual coordinate exterior derivative. `adjoint_type` specifies the
  lowering bidegree, `formal_adjoint` the integral adjunction, and `square_zero`
  records the usual identity of the Dolbeault differential. These fields
  characterize the canonical maps and exclude arbitrary maps.
- The L² Hermitian products are the existing `l2Pair g μ`: inverse-real-Gram
  tensor contraction with the 1/k! normalization, integrated against metric
  volume and summed over exterior degrees. In one type only its own degree
  contributes. No unrelated inner product is introduced.

### Conclusions, clause by clause

- Existence as a complex-linear smooth first-order adjoint is expressed by the
  existential Dolbeault presentation and
  `HasFormDifferentialOrder 1 p (q + 1) p q D.adjoint`.
  The existing adjoint field is a complex-linear map; this new order predicate
  requires bidegree preservation and actual smooth coordinate coefficients.
- Adjointness for every smooth u and v is stated explicitly by the next conjunct,
  quantified over `α : typeForms p q` and `η : typeForms p (q + 1)`:
  `l2Pair g μ (D.dbar α.val) η.val = l2Pair g μ α.val (D.adjoint η.val)`.
- Characterization of the adjoint includes uniqueness: for every complex-linear
  S mapping the source type into type (p,q) and satisfying the same adjunction,
  `S η.val = D.adjoint η.val` for every η in the source type. It is equality on
  the source type, not an unjustified assertion about S on all other types.
- P = DD* + D*D is the existing `D.laplacian`, whose definition is precisely
  `D.dbar.comp D.adjoint + D.adjoint.comp D.dbar`.
  `HasFormDifferentialOrder 2 p q p q D.laplacian` gives smooth coefficients,
  order at most two, and the indicated type endomorphism.
- Complex and real ellipticity of order two are both in
  `IsFormElliptic 2 p q D.laplacian`. For each atlas chart, a coefficient family
  must represent the actual Laplacian on every smooth input of that type.
  Its degree-two symbol must satisfy `Set.BijOn` on the actual coordinate
  type fibre for every chart point and every nonzero real continuous-linear
  cotangent vector `ξ : Model n →L[ℝ] ℝ`.
  A second `Set.BijOn` explicitly uses `(A.symbol z ξ).restrictScalars ℝ`.
  The maps are respectively complex-linear and real-linear; bijectivity on
  the invariant type fibre means invertibility in the corresponding field.
- Differential order and degree-k symbol have their literal coordinate meaning:
  `FormDifferentialExpression.coefficient` gives smooth complex-linear maps
  indexed by derivative length l ≤ k and ordered real coordinate directions;
  `apply` sums their values on `iteratedFDerivWithin ℝ l`.
  Collecting ordered lists with equal multiplicities gives exactly the usual
  finite multi-index expansion. Conversely each multi-index term can be put
  in one ordered list. The symbol uses only `coefficient ⟨k, ...⟩`, multiplied
  by the product of ξ on those same coordinate directions. It cannot be
  chosen independently of the coefficients or of the operator they represent.
  Local coefficient extensions act on the ambient alternating tensor space;
  ellipticity is checked only on the type eigenspace, as required by the node.

### Dependency declarations used

`Sheaf.Geometry.Manifold.HermitianDolbeaultData` is a landed definition node
`def-sfb-hermitian-dolbeault-data`. I read its entire module, definitions and
source docstrings. It supplies `ComplexManifold.Model`, `FormFields`,
`chartTangent`, `formCoordinates`, `smoothForms`, `typeForms`,
`realCoordinateVector`, `HermitianMetric`, `MetricVolume`, `l2Pair`,
`DolbeaultOperators`, and `DolbeaultOperators.laplacian`. It is added to the
item's statement dependencies; no existing dependency is replaced or modified.

The new coordinate-expression definition node is also a statement dependency.
Its public module imports HermitianDolbeaultData. The item publicly imports the
new module and therefore the shared geometric definitions.

The proof-only import `Sheaf.Analysis.Calculus.CoordinateWeightedAdjoint`
supplies `CoordinateDifferentialOperator.weightedAdjoint_spec`, the recorded
statement of `lem-sfb-coordinate-weighted-adjoint`. I read its signature and
step-by-step proof docstring: arbitrary positive Hermitian Gram matrices,
positive smooth density, smooth first-order coefficients, and either compact
support case. The other proof-only import is
`Mathlib.Geometry.Manifold.PartitionOfUnity`; the recorded Mathlib dependency
`SmoothPartitionOfUnity.exists_isSubordinate` covers
`lem-sfb-smooth-subordinate-partition`. I read the structure at lines 122–132
and the existence theorem at lines 550–555, including its Hausdorff and
sigma-compact context. Both proof dependencies are imported privately as required.

### Edge cases checked

- Empty M is allowed. The smooth section spaces are zero, local assertions are
  vacuous, and the existential operator presentation admits zero maps. No
  `Nonempty M` binder was introduced.
- n=1 is included. n=0 is excluded exactly by the node's explicit n≥1 hypothesis.
- p=0, p=n and q=0,n are included by the non-strict inequalities.
- At q=n the adjacent source type of the displayed adjoint is zero. The type
  convention makes the restriction and its characterization valid; no type
  n+1 is silently identified with a nonzero form bundle.
- At q=0 the lower missing type is bottom by the existing definition. The
  adjoint bidegree law makes the boundary summand of the Laplacian zero.
  Ellipticity still concerns the nonzero degree-two Laplacian symbol on A^{p,0}.
- The tensor eigenspace equation in degree zero has an empty sum and gives the
  full scalar fibre for type (0,0). The zero fibre has its unique bijection.
- At k=0 there is one empty list and an empty product equal to one, so the
  helper definition correctly describes a zero-order coefficient map.
- Real cotangent vectors are real continuous-linear functionals, not arbitrary
  functions or complex covectors. Only ξ=0 is excluded from ellipticity.
- Operator-order bounds alone do not imply ellipticity: the zero coefficient
  family in positive order has zero symbol, which is not bijective on a
  nonzero type fibre. In particular the definition is not hollow.
- The model tensor spaces are finite dimensional. Smoothness of coefficient
  homomorphisms in operator norm is equivalent to smoothness in local frames;
  using these redundant ambient tensors loses no type coefficient expression.
- Both modules explicitly set `autoImplicit false`; all universes and variables
  are declared. There are no data sorries, choices, opaque objects, axioms,
  file-local definitions, or theorem helpers without matching DAG nodes.

### Searches

The prescribed msearch wrapper was used for LeanSearch, LeanFinder, Loogle and
Mathlib grep. Queries and actual result summaries are recorded in the new
node's `mathlib_searches` and in the sandbox's search log.

- LeanFinder, “Dolbeault Laplacian elliptic smooth formal adjoint on Hermitian
  manifolds”: eight results, including `LineDeriv.laplacianCLM` and the flat-space
  Laplacian; none is the statement on compact Hermitian manifolds.
- LeanSearch, “Smooth differential operators on differential forms coordinate
  coefficients principal symbol ellipticity”: eight results, headed by
  `extDeriv_extDeriv`; the derivative is reused through the existing definitions,
  but there is no principal-symbol or differential-order definition.
- LeanFinder, “Coordinate definition of smooth differential operator on type p q
  differential forms its principal symbol and ellipticity”: eight manifold
  derivative/notation results, no coordinate symbol definition.
- Loogle, `"principalSymbol"`: zero hits.
- Mathlib grep in Geometry/, `principalSymbol|principal_symbol|IsElliptic|DifferentialOperator`:
  zero hits. A direct rg over Mathlib Geometry and Analysis gave no symbol or
  geometric differential-operator definition.
- rg over `lean/WeilConjectures`, the upstream name index, and `lean/Sheaf`
  found no existing statement or coordinate symbol definition. It did find the
  recently landed HermitianDolbeaultData, which is reused. The item's blueprint
  id occurs only as a proof citation in the already landed orthogonal
  decomposition; that declaration does not state this node.
- Searching DAG text for principal symbols and differential operators found
  the surrounding analytic statements and a pseudodifferential/distribution
  definition. Reading those showed none defines the present coordinate
  differential expressions on complex type-form fibres. Blueprint search for
  “principal symbol” returned zero imported blueprint nodes.

No statement correction or STATEMENT-DISPUTED issue is reported. The item's
statement, proof, proof dependencies and all other fields are preserved; only
its Lean record and the two added statement dependencies change.

## New nodes

`def-sfb-form-differential-expressions` defines the missing coordinate notion,
not another adjoint theorem. The module reuses Mathlib continuous alternating
maps and iterated real derivatives and the existing project's form coordinates.
It contains real data definitions only: `FormTensor`, `typeTensor`,
`FormDifferentialExpression`, `apply`, `symbol`, `Represents`,
`HasFormDifferentialOrder`, and `IsFormElliptic`. Source: Kong §3.1 and §6.2,
the definition before Lemma 6.4. The three kinds of searches above show no
existing node or declaration gives this notion; the inherited blueprint
ancestor is null, as reported by blueprint_refs.py, and the new node preserves
the item's via chain with the item prepended. It is cited by the item and
itself cites exactly the field and shared Hermitian-Dolbeault definition nodes.

## Validation

Both delivered modules compiled independently in dependency order through the
prescribed `scompile.py Q160 lem-sfb-dolbeault-laplacian-elliptic` wrapper,
including their actual library module names. Both were clean; the single
postponed theorem is the allowed stage-2 sorry. The 100-character line limit
was checked on both source files. Dry-run and delivery results follow below.

The prescribed `deliver2.py --no-push` completed successfully: commit c7b48615680
passed maintainer preflight and all per-file compiles. The first dry run caught
and I repaired two record issues: the new node now includes `import_flags: []`,
and the item signature is copied through the theorem's final `:= by`, not
truncated at a named-argument `:=` inside a type. No Lean change was required.
The direct-delivery wrapper supplies the honest second-reading placeholder;
the maintainer's independent review is the review of this packet.

## Second reading by Q160

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
