## Worker report

Item: lem-sfb-torus-fixed-euler-unit. Module:
`Sheaf.AlgebraicGeometry.TorusFixedEulerUnit`. Main declaration:
`AlgebraicGeometry.TrivialTorusCoherent.torus_fixed_euler_unit`.
All theorem proofs remain `sorry`; all helper definitions have real data.
No statement correction, no new nodes, and no dependency replacement.

Hypotheses and clauses, checked against the node:

- The field and algebraic closedness are `(F : Type u) [Field F] [IsAlgClosed F]`.
- The algebraic split torus is `T : Grp (Over (Spec (.of F)))`, with `r : ℕ` and
  `Nonempty (T ≅ MultiplicativeType.splitTorus F r)`. This retains rank zero.
  Affineness and finite type follow from the split-torus identification, rather
  than imposing additional hypotheses.
- The scheme over F is `Y : Over (Spec (.of F)))`; `[Smooth Y.hom]` and
  `[IsProjective Y.hom]` are exactly smoothness and projectivity. The algebraic
  action, with its unit and composition laws, is `[ModObj T.X Y]`.
- `W`, `i : W ⟶ Y`, and `[IsClosedImmersion i.left]` introduce the fixed closed
  subscheme. `_hfixed` quantifies over every F-algebra A, every A-valued point y,
  every algebra extension A → B, and every B-valued torus point. Factoring y
  through i is equivalent to being fixed after every such extension. This is
  precisely the established `torus_fixed_scheme_smooth` convention, including
  nonreduced test algebras; it does not replace the fixed scheme by its F-points.
- `Smooth W.hom` is the first conclusion. `∃ c : ℕ` and the following `∀ w`
  give affine neighborhoods in Y, lists generating `i.left.ker.ideal U`, the
  recorded `RingTheory.Sequence.IsRegular`, and their uniform length bound c.
  Nothing is required on charts disjoint from W.
- The ideal sheaf uses `EquivariantCoherent.IsIdeal (D := D) i.left K`, not an
  arbitrary locally free replacement. `IsInducedConormal` identifies N with
  the actual tensor pullback i*I = I/I². The action on N on EVERY test scheme
  is the inverse of the recorded ideal descent isomorphism, transported by
  canonical tensor-pullback composition comparisons. Its equalities `ha` and
  `hp` also express the fixedness of the image, on all test schemes.
  The `ActionGroupoidModel` has the actual group-coordinate multiplication
  normalization already supplied by def-sfb-equivariant-coherent-gzero.
- `N.moduleObj.IsFiniteLocallyFree` is locally finite freeness. The finite
  `IsWeightDecomposition N P` and `IsZero (P 0 : W.left.Modules)` express that
  the only possibly nonzero weights are nonzero. This is the full sheaf and
  all-test-scheme decomposition, so it remains true after every geometric
  pullback. This is equivalent to the geometric-fibre clause over this
  algebraically closed base, rather than only an assertion at closed points.
- The character group is the existing `Character T`, actual group-scheme
  homomorphisms to G_m written additively; `CharacterRing T` is the existing
  `AddMonoidAlgebra ℤ (Character T)`. Thus e^η is `single η 1`, and multiplication
  is the group-ring multiplication from the node. `eulerDenominators` is exactly
  `Submonoid.closure {a | ∃ χ, χ ≠ 0 ∧ a = 1 - single χ 1}`;
  `EulerCoefficients T` is `Localization (eulerDenominators T)`.
- The fixed-locus coherent group is the existing `EquivariantGroup T W`.
  Its generators are actual coherent linearized sheaves, relations include
  every equivariant short exact sequence, and its scalar action is normalized
  by the character-twist relations, not an arbitrary module structure.
  This is the trivial-base presentation of G₀ᵀ(W); it is appropriate because
  the fixed-locus action is trivial. The general-action self-intersection
  presentation and its `IsIdeal`/`linearization` specify the induced conormal.
  No third coherent group, representation ring, or linearization is defined.
- `E : ℕ → Linearized T W` and `IsExterior N q (E q)` are the actual exterior
  powers with their normalized action on wedge sections. Each is finite locally
  free, has tensor products with every coherent object, and `H q` is an R-linear
  tensor operator normalized by `IsEquivariantTensorOperator`. Explicit tensor
  existence prevents this normalization from being vacuous.
- For `c < q`, `IsZero (E q).moduleObj ∧ H q = 0` makes the sum finite.
  `exteriorEulerOperator c H` is the finite sum of `(-1 : ℤ)^q • H q`.
  The operator is the exterior tensor operator from the self-intersection
  statement, using the already recorded alternative fixed-base presentation
  and exterior-operation normalization. The item does not assert a new Gysin map.
- The final `L` is a linear equivalence over `EulerCoefficients T` on
  `EulerCoefficients T ⊗[CharacterRing T] EquivariantGroup T W`.
  Its `toLinearMap` is exactly the scalar extension of that finite alternating
  operator via Mathlib's `LinearMap.baseChange`. Tensor symmetry identifies
  this left-scalar tensor order with M = G₀ᵀ(W) ⊗_R R_Σ in the node.
- `IsZero N.moduleObj → exteriorEulerOperator c H = 1` explicitly retains
  the zero-conormal/codimension-zero clause. `IsEmpty W.left → ... = 1`
  explicitly retains the empty case (on the zero group its identity is zero).
  The rank-zero torus is allowed and has only weight zero, so the preceding
  weight assertion forces N=0. There is no characteristic or rationality
  restriction: the group ring has integer coefficients and only Σ is inverted.

Dependency declarations used (all read in their defining source files):

- def-weil-field: Mathlib `Field`.
- def-sc-group-scheme: `CategoryTheory.GrpObj`/`Grp`,
  `Mathlib.CategoryTheory.Monoidal.Grp` and Cartesian group/module interfaces.
- def-pc-scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- pqf-def-coherent: the recorded module
  `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the exact
  `RingedSpace.IsCoherent` of `WeilConjectures.AlgebraicGeometry.Coherent`.
- def-weil-algebraic-closure: Mathlib `IsAlgClosed` (Basic.lean:62), as specified
  in the node's mathlib_match; no chosen algebraic closure is needed here.
- def-sbc-smooth-morphisms: Mathlib `AlgebraicGeometry.Smooth`.
- def-pc-morphism-conventions is a convention: projectivity uses its named
  def-pc-projective-morphism, namely `AlgebraicGeometry.IsProjective` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- def-weil-closed-immersion: Mathlib `AlgebraicGeometry.IsClosedImmersion`.
- def-weil-pbc-regular-sequence: Mathlib `RingTheory.Sequence.IsRegular`.
- lem-sfb-equivariant-regular-self-intersection:
  `Sheaf.AlgebraicGeometry.EquivariantRegularSelfIntersection`,
  `AlgebraicGeometry.EquivariantCoherent.equivariant_regular_self_intersection`.
  Its public dependencies provide `ActionGroupoidModel`, `IsIdeal`, `underlying`,
  `linearization`, `source`, and `target`, which pin the actual induced action.
- Added existing statement dependency def-sfb-tori-multiplicative-type:
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`,
  `AlgebraicGeometry.MultiplicativeType.splitTorus`.
- Added existing statement dependency def-sfb-trivial-torus-coherent-data:
  `Sheaf.AlgebraicGeometry.TrivialTorusCoherentData`,
  `Linearized`, `Character`, `CharacterRing`, `IsWeightDecomposition`,
  `testModule`, `atComp` in `AlgebraicGeometry.TrivialTorusCoherent`.
- Added existing statement dependency def-sfb-coherent-group-presentation:
  `Sheaf.AlgebraicGeometry.CoherentGroupPresentation`, `EquivariantGroup`,
  `IsExterior`, `IsTensor`, `IsEquivariantTensorOperator` in the same namespace.

The added ids already have landed Lean records. Their notions are reused,
not copied. The small localization/finite-sum definitions and the canonical
conormal comparisons belong to this node's specified operator and are listed
in `lean.declarations`, as authorized for owning-node helpers.

All recorded proof-dependency modules are imported privately. The Mathlib
smooth-locality match is imported from Morphisms.Basic; the closed-immersion
proper result is imported from WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper.
The two proof dependencies with no declaration or mathlib_match,
lem-sfb-split-torus-representation-weight-decomposition and
lem-trf-proper-field-invertible-coherent, have no module to import and are
retained in the proof docstring and DAG. They are not needed to type this
statement. No dependency node record is changed.

Edge cases checked before drafting: W empty; r=0; i the identity; zero conormal;
a single nonzero character on a point, for which the operator is 1-e^χ; disconnected
W with different local codimensions, handled by a bound rather than a constant
rank; weight pχ in characteristic p (scheme characters, not their derivatives).
None requires inverting an integer or excluding a characteristic. Lists of
length zero are allowed, and their regularity requires a nonzero chart ring,
which is available at every point actually quantified over.

Searches:

- `msearch.py ... leanfinder "Conormal Euler operator for split torus fixed locus
  invertible after character localization"`: eight hits, Lie weights and abstract
  localized-module facts; none states the scheme-theoretic assertion.
- `msearch.py ... leansearch "Equivariant coherent Grothendieck group fixed torus
  conormal Euler operator invertible"`: eight abstract Grothendieck-group and
  group-cohomology hits, no equivariant coherent Euler theorem.
- `msearch.py ... loogle "Localization, MonoidAlgebra"`: no hits.
- `msearch.py ... loogle "LocalizedModule, Module.End, LinearEquiv"`: two
  IsLocalizedModule universal-property hits, no scheme result.
- `msearch.py ... grep "torus_fixed.*euler|TorusFixedEuler|fixed.*Euler|character.*[Ll]ocalization"`:
  ten unrelated abstract localization comments, no matching statement.
- `rg` in live `lean/WeilConjectures` and `lean/Sheaf`, by Euler/conormal/torus
  terms and by the item id: no existing matching theorem. Located and read the
  self-intersection, character-twist coherent group, and weight decomposition
  interfaces used above. `rg` on the latest blueprint for the item id returned
  no occurrence; this is the agent-formulated supporting node as its source says.
- Opened the local Milne PDF with pdftotext: Theorem 22.50 invokes the general
  fixed-point theorem and does not prove this prerequisite. The docstring
  accurately attributes the proof to the node's agent assembly, with each
  dependency and the finite inverse explained.

Validation uses only scompile.py and deliver2.py. The wrapper's local attempt
reported `OSError(28, 'No space left on device')`, then its built-in server
confirmation compiled this module cleanly in 5.8 seconds. No launcher tool
was changed or bypassed. Final validation results are recorded below.

## Second reading by Q70

Worker's second source/signature pass; the maintainer supplies the independent
review required by this assignment. I reread the node and delivered signature
side by side. The all-algebra fixedness quantifiers match the recorded smooth
fixed-scheme interface. I checked that the induced conormal action uses the
INVERSE ideal descent isomorphism, so its direction is from y to gy. Its source
and target comparisons are canonical and its underlying module is i*I, so an
arbitrary vector bundle with favorable weights cannot satisfy the conclusion.
The coherent group and character-twist action are the existing definitions,
not placeholders. Every exterior tensor operator has actual coherent outputs,
and its finite alternating sum, after the specified localization, is exactly
L.toLinearMap. I added explicit zero-conormal and empty-scheme identity clauses
in this pass, and removed an unnecessary heartbeat setting after the compiler
reported a style warning. No hypothesis, characteristic, or degenerate case is
excluded; no node statement was corrected. All helpers have docstrings, every
variable/universe is explicit, and the only postponed proof is the named theorem.

Final check: `deliver2.py Q70 lem-sfb-torus-fixed-euler-unit --no-push`
printed `OK (dry run): commit c297ea0d937 passes the preflight and compiles;
nothing pushed`. The delivered file compiled on the server with no errors or
warnings, within the unchanged 60-second limit.

## Retry on 2026-10-24

Retained the saved module and node record. Ran the required
`deliver2.py Q70 lem-sfb-torus-fixed-euler-unit --no-push` twice in this retry.
Both exited 1 during server compilation with exactly:
`sandbox Sheaf.Stage2.Sandbox0` followed by
`resource exhausted (error code: 28, no space left on device)`.
Each reported `COMPILE FAILED on the server, nothing pushed` after 10.0 seconds.
This reproduces the previous attempt's infrastructure failure; no Lean
diagnostic was emitted and no source repair was indicated. No launcher tool
or shared repository file was modified. The saved packet remains in place.

## Dispatcher retry confirmation on 2026-10-24

Started with the saved report and the prescribed dry run. Ran
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q70 lem-sfb-torus-fixed-euler-unit --no-push`
twice. Both returned exit 1 after 10.0 seconds with:

```
COMPILE FAILED on the server, nothing pushed:
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

No Lean diagnostic or packet repair was indicated. Retained the module and node
unchanged. No push was attempted, no shared repository files were edited, and
no launcher tool was modified or bypassed. Server disk exhaustion still blocks
the required validation and delivery.

## Current dispatcher retry on 2026-10-24

Inspected the saved report, module and node record and started with the required
`deliver2.py Q70 lem-sfb-torus-fixed-euler-unit --no-push`. Repeated it once.
Both attempts exited 1 after 10.0 seconds with exactly:

```
COMPILE FAILED on the server, nothing pushed:
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

There was no Lean diagnostic to repair. The saved Lean module and node record
remain unchanged; no push was attempted. Only this sandbox report was updated.
The required server validation is still blocked by server disk exhaustion.

## Saved-packet retry verification on 2026-10-24

This dispatcher retry began by inspecting the saved report and running the
prescribed `deliver2.py Q70 lem-sfb-torus-fixed-euler-unit --no-push`.
A second identical dry run confirmed the failure. Both exited 1 after 10.0 s:

```
COMPILE FAILED on the server, nothing pushed:
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

Neither emitted a Lean diagnostic. The saved module and node remain unchanged;
only this sandbox report was updated. No push or launcher-tool modification was
attempted. Server disk exhaustion prevents the required dry-run validation.

## Saved-packet dry-run confirmation, 2026-10-24

This retry inspected the saved report and began with the required dry run.
Both runs of `deliver2.py Q70 lem-sfb-torus-fixed-euler-unit --no-push`
exited 1 after 10.0 seconds with the same server diagnostic:

```
COMPILE FAILED on the server, nothing pushed:
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

No Lean diagnostic was emitted. The saved module already uses module mode.
The packet was retained unchanged except for this report entry. No push was
attempted and no shared repository or launcher file was modified. Server disk
exhaustion prevents the required validation and delivery.

## Current saved-packet retry, 2026-10-24

Inspected the saved report and module, then ran the prescribed
`deliver2.py Q70 lem-sfb-torus-fixed-euler-unit --no-push` twice. Both
exited 1 after 10.0 seconds with the same server failure:

```
COMPILE FAILED on the server, nothing pushed:
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

No Lean diagnostic was emitted. The module and node are retained unchanged;
only this sandbox report was updated. No push was attempted. Required server
validation remains blocked by server disk exhaustion.

## Dispatcher dry-run retry, 2026-10-24

Read the retained report and ran the prescribed
`deliver2.py Q70 lem-sfb-torus-fixed-euler-unit --no-push` twice.
Both exited 1 after 10.0 seconds with the same server diagnostic:

```
COMPILE FAILED on the server, nothing pushed:
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

No Lean diagnostic was emitted, so no packet source repair was indicated.
The saved module and node remain unchanged. No push was attempted; only this
sandbox report was updated. Server disk exhaustion blocks required validation.
