## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothPrescribedTangentHypersurface` states
`AlgebraicGeometry.exists_smooth_hypersurface_prescribed_tangent`, with its sole
proof `sorry`. It adds no definition and changes only the item's `lean` record.
There is no statement correction or mathematical dispute.

I read the item, every statement dependency and its Lean record or Mathlib match,
and the recorded declarations' signatures and docstrings. The old CompactObject
example is withdrawn; its node now points to the upstream
`WeilConjectures.CategoryTheory.CompactObject`, whose module/header I also read.
There is no repair note for this item.

Clause-by-clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Scheme over k: `(Y : Scheme.{u}) (pY : Y ⟶ Spec (.of k))`. The explicit structure
  map is used because the recorded tangent-space declaration takes that map.
- Smooth: `[Smooth pY]`.
- Separated: `[IsSeparated pY]`, the Mathlib class whose defining field is
  `IsClosedImmersion (pullback.diagonal pY)`.
- Geometrically integral: `[GeometricallyIntegral pY]`, not merely irreducible.
- Finite type: `[LocallyOfFiniteType pY] [QuasiCompact pY]`, exactly the two
  properties in the dependency node's recorded convention.
- Rational point: `(p : pY.fieldPoints k)`, a section `Spec k ⟶ Y`; the underlying
  point is `p.1 default`. `Spec k` is a singleton, so this does not choose a
  special point or impose a further hypothesis.
- Dimension d at least two: `(d : ℕ) (hd : 2 ≤ d)` and
  `hdim : topologicalKrullDim Y = (d : WithBot ℕ∞)`. The topological Krull
  dimension is retained, including its negative/infinite ambient values.
- Tangent hyperplane: `H : Submodule (Y.residueField (p.1 default))
  (schemeTangentSpace k Y pY (p.1 default))` and `hH`, the assertion that the
  quotient has finrank one. This is precisely codimension one: smooth finite
  type ensures the ambient tangent space is finite dimensional.
- Scalar convention: the dependency `schemeTangentSpace` canonically has scalars
  κ(p), not an independently supplied k-module structure. At the rational point,
  the structural map k → κ(p) is an isomorphism (see upstream
  `Scheme.Hom.bijective_residueFieldAlgebraMap_of_comp_eq_id`). Thus κ(p)-linear
  subspaces and their codimensions are exactly k-linear subspaces under the
  canonical identification. No arbitrary module structure or equivalence is
  assumed or selected, and no new tangent-space definition is introduced.
- Open neighbourhood: `∃ (V : Y.Opens) (_ : p.1 default ∈ V)`; `V.toScheme` and
  `V.ι` are Mathlib's open subscheme and its canonical open immersion.
- Closed immersion: `∃ (D : Scheme.{u}) (j : D ⟶ V.toScheme), IsClosedImmersion j`.
- Every required property of D is asserted for its inherited structural map
  `((j ≫ V.ι) ≫ pY)`: `Smooth`, `IsSeparated`, `GeometricallyIntegral`,
  `LocallyOfFiniteType`, and `QuasiCompact`.
- Dimension of D: `topologicalKrullDim D = ((d - 1 : ℕ) : WithBot ℕ∞)`.
  Since `2 ≤ d`, natural subtraction expresses the indicated dimension exactly.
- Rational point q mapping to p: `q : ((j ≫ V.ι) ≫ pY).fieldPoints k` and
  `hq : q.1 ≫ (j ≫ V.ι) = p.1`. Equality is of the rational-point morphisms,
  not just equality of their underlying topological points.
- The tangent map is the dependency's canonical `schemeTangentMap`, applied to
  `j ≫ V.ι` and its inherited base map; `rfl` supplies the structural compatibility.
  The existential `he` gives the bijectivity of the induced residue-field map,
  as required by that API. It follows from the two rational points, and is a
  conclusion, not an extra hypothesis on the input.
- Identification with H: `Function.Injective (schemeTangentMap ...)` and, for
  every target vector v, `v ∈ H ↔ ∃ w, HEq (schemeTangentMap ... w) v`.
  This asserts both injectivity and exactly the prescribed image. The map's
  target is indexed by `(j ≫ V.ι) (q.1 default)`, whereas H is indexed by
  `p.1 default`; hq identifies those points. HEq expresses equality after this
  dependent index identification without inserting a chosen tangent isomorphism.
  The scalar transport inside `schemeTangentMap` is its fixed canonical one.

Dependencies used:

- `Mathlib.Algebra.Field.Defs`: `Field` (available through statement imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`.
- `WeilConjectures.AlgebraicGeometry.DensePoints`: the recorded
  `Scheme.Hom.baseChangeFieldPoint` uses the existing `Scheme.Hom.fieldPoints`
  rational-point type; this delivery uses that same type, without needing the
  optional base-change operation.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace`,
  `schemeTangentSpaceAddCommGroup`, `schemeTangentSpaceModule`, `schemeTangentMap`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; for an actual
  open V its canonical inclusion is already an open immersion.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.

All locally recorded proof-dependency modules are imported privately, together
with the Mathlib files recorded by the proof leaves. The two proof nodes
`lem-sfb-regular-separable-affine-smooth-neighbourhood` and
`lem-per-geometric-integrality-finite-field-test` have no recorded Lean module
in the read clone; no import is invented for them. They are proof prerequisites,
not missing notions needed to state this theorem. The nine-step declaration
docstring carries the item's full construction and proof route for stage 3.

Edge cases checked before writing: d = 2 gives a smooth integral curve of
 dimension 1; d = 0 or 1 is excluded by the original hypothesis. The empty Y
cannot supply p; D is likewise nonempty because q is supplied. H = 0 cannot be
a hyperplane in a smooth tangent space of dimension at least two; H = top has
quotient finrank zero and fails hH. Positive characteristic is unrestricted.
No properness, projectivity, affineness, effective-Cartier condition or fixed
local equation is added to the conclusion. The unrestricted universe u includes
all fields and schemes at a common universe, and no additional universe equality
or independent small test universe is imposed. The source construction does
produce an affine hypersurface, but the statement only asks for its original
closed immersion and geometric/dimension/tangent properties.

Source check: I read Milne's Lemma I.3.6 on printed page 18 using pdftotext. Its
proof cuts by any ambient hyperplane through P not containing Tgt_P(V), takes
the unique irreducible component through P, and identifies its tangent space
with the intersection with that hyperplane. Every hyperplane of Tgt_P(V)
extends to such an ambient hyperplane. Shrinking to the smooth component and
retaining a principal ambient neighbourhood gives the node's closed immersion.
No change to the source or the node statement is needed.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder "A smooth variety has a smooth integral hypersurface
  near a rational point realizing any prescribed tangent hyperplane"`: eight
  hits, including `AlgebraicGeometry.IsSmooth.exists_isStandardSmooth` and
  `Algebra.IsSmoothAt.exists_notMem_smooth`; none states the prescribed tangent
  hyperplane, integral hypersurface, and dimension conclusion.
- `msearch.py ... loogle "AlgebraicGeometry.schemeTangentSpace,
  AlgebraicGeometry.schemeTangentMap"`: zero hits; remote Loogle does not index
  the project declarations (`unknown identifier ...schemeTangentSpace`). Their
  actual upstream files were read directly instead.
- `msearch.py ... grep "hypersurface|tangent.*hyperplane|prescribed.*tangent"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of project `WeilConjectures` and `Sheaf` for `schemeTangentMap`, tangent
  submodules, `prescribed.tangent`, `tangent.hyperplane`, and smooth hypersurfaces:
  existing tangent criteria and slice statements found, but no exact theorem.
  In particular `exists_affine_smooth_effectiveCartier_hypersurface_slice` in
  `Sheaf.TraceFormula.SmoothSeparableHypersurfaceSlice` gives no prescribed
  tangent hyperplane or geometric integrality, so does not replace this node.
- `rg` for this item's id in `lean/WeilConjectures`: no hit.
- `rg` of `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures` and `Sheaf`
  for `exists_smooth_hypersurface_prescribed_tangent` and its proposed module
  name: no existing declaration or module found.

Validation: initial scompile.py server compile passed both sandbox and library
module checks (2.1 s and 2.3 s), without errors or warnings. The final file also
sets `autoImplicit false`, explicitly binding the universe and every variable.
The delivery dry run recompiles that final file and performs server preflight.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
