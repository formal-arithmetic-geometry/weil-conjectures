## Worker report

The module `Sheaf.AlgebraicGeometry.ExcellentSurfaceDesingularization` states
`AlgebraicGeometry.exists_projective_regular_resolution_of_excellent_surface`, with `sorry`
as its entire proof. It introduces no definition and does not change the natural statement,
dependencies, or proof plan of the node. The declaration docstring records all seven proof
steps, including normalization, complete local resolution, normalized refinement, descent,
globalization, projectivity, and preservation of the regular locus.

Clause-by-clause correspondence:

- The arbitrary scheme Y is `(Y : Scheme.{u})`, with explicitly bound universe u.
- Integral is `[IsIntegral Y]`; Noetherian is `[IsNoetherian Y]`, the standard scheme
  condition (all affine coordinate rings Noetherian, together with quasi-compactness).
- Excellent is `hExcellent : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U)`, using the recorded
  ring predicate on all affine opens. No finite-type, field, characteristic, separatedness,
  or affine hypothesis is imposed on Y.
- Dimension exactly two is `hDim : topologicalKrullDim Y = 2`. This is the usual scheme
  Krull dimension, the supremum of lengths of chains of irreducible closed subsets, agreeing
  with ring Krull dimension on affine schemes. It is not the dimension of global sections.
- Admitting an ample invertible sheaf is `hAmple : ∃ (L : Y.Modules)
  (hL : L.IsInvertible), @Scheme.Modules.IsAmple Y L hL`. The invertibility witness is
  supplied to precisely the recorded absolute ampleness definition.
- Existence of V, its integrality, and r are the successive existential binders
  `∃ (V : Scheme.{u}) (_ : IsIntegral V) (r : V ⟶ Y)`. The anonymous integral witness is
  available to subsequent typeclass inference, including formation of its function field.
- Regularity is `IsRegularScheme V`, including local Noetherianity as required by the
  recorded definition, rather than just the upstream stalkwise regularity class.
- Projectivity with the specified convention is `IsHProjective r`, whose field asserts
  a closed immersion into projective space with a finite coordinate type and equality of
  its projection composite with r. This is the existing finite-projective-space convention
  of `def-kun-projective`. Since V is nonempty, an empty coordinate type cannot witness
  this assertion; a nonempty finite coordinate type has cardinality m+1 for some m.
- Birationality is `∃ hη : r (genericPoint V) = genericPoint Y,
  IsIso (r.functionFieldMap hη)`. The equality explicitly ensures that the induced generic
  stalk map has source k(Y); its target is k(V). The map is the actual map induced by r,
  not an arbitrary isomorphism between the two fields. The generic-point equality expresses
  the dominance needed to speak of this induced map and adds no extra restriction to
  birationality.
- The entire regular locus is represented by `∃ U : Y.Opens,
  (∀ y : Y, y ∈ U ↔ IsRegularLocalRing (Y.presheaf.stalk y))`. Its exact membership
  equivalence prevents substituting any smaller open. `IsIso (r ∣_ U)` then states that
  the canonical morphism r⁻¹(U) → U is an isomorphism. Openness is included as an existential
  conclusion because excellence guarantees it; it is not an added hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` (including its
  irreducibility instance); recorded by `def-pc-integral-scheme`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; its scheme specialization is
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, built from `IsQuasiExcellent` and
  `IsUniversallyCatenary`; recorded by `def-exc-excellent-ring`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`; its topological version is
  `topologicalKrullDim` in `Mathlib.Topology.KrullDimension`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.FunctionField`: the docstring of
  `Scheme.functionFieldOfComponents` explicitly directs the arbitrary integral-scheme
  clause to `Scheme.functionField` in `Mathlib.AlgebraicGeometry.FunctionField`. The
  recorded dependency module is imported. `Hom.functionFieldMap` is reused from
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`; its full signature applies
  to arbitrary integral schemes, with no curve hypothesis.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple` and its
  `IsInvertible` input, read using `scompile.py --source` because the older checkout lacks
  this module.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, also read
  using `scompile.py --source` and checked against its existing `def-kun-projective` record.
- The already stated proof inputs `isHProjective_of_isProjectiveBundle` and
  `regular_normal_and_normal_decomposition` are imported non-publicly from
  `Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective` and
  `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`. The six remaining surface proof
  inputs have no Lean records or Mathlib matches in the current DAG; there is no module
  to import yet. They are retained in the node and named individually in the proof plan.

Edge cases checked: integral schemes are nonempty, so the empty scheme is correctly
excluded by the given hypothesis, not by a new assumption. Already regular Y is permitted:
the identity is a resolution and the regular open is all of Y. The empty singular set is
explicitly handled by the zero-length tower in the proof plan. No assumption that the
singular set is nonempty is introduced. The function-field isomorphism is tied to r and
cannot be satisfied merely by abstractly isomorphic fields. All points, including the
generic point and codimension-one points, occur in the regular-locus equivalence. There
is no characteristic restriction or relation between independent universes: only the
scheme universe u is used. No statement fault or disputed statement was found.

Source reading: `literature/stacks-project/resolve.tex`, theorem `theorem-resolve`
(Tag 0BGP), including its full proof of (4) ⇒ (3), agrees with the node's normalized
blowup route. The node's Tag 087S refinement is the existing projective-bundle conversion
theorem, whose declaration and proof-plan docstring were read in full.

Searches for an existing statement:

- `msearch.py ... leanfinder "excellent integral Noetherian scheme of dimension two
  admitting an ample line bundle has a projective regular birational resolution
  isomorphic over its regular locus"`: 8 hits, concerning relative normalization,
  projective spectra, and smoothness. None states the resolution theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsProjective,
  AlgebraicGeometry.Scheme.functionField, AlgebraicGeometry.IsRegular"`: 0 hits;
  unknown identifier `AlgebraicGeometry.IsProjective` in the Mathlib search service.
  The projectivity notion was subsequently located in the upstream project and reused.
- `msearch.py ... grep "desingular|resolution|IsHProjective|functionFieldMap"
  AlgebraicGeometry`: 0 hits.
- `rg` over upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for desingularization, excellent surfaces and this node:
  no exact statement. Project results concerned fan desingularization, Popescu smoothing,
  and log-regular-pair resolution, whose extra log hypotheses make them different.
- The specifically requested `grep -rn "lem-per-excellent-surface-desingularization"`
  in the upstream source returned no result. A full-name collision search in Mathlib,
  upstream, the project and upstream-name index also returned no result.
- Targeted searches found and reused the existing `IsHProjective`, `functionFieldMap`,
  `IsRegularScheme`, absolute ampleness, and `morphismRestrict` interfaces. No helper
  definition or new node was needed.

Validation: the prescribed `scompile.py NQ lem-per-excellent-surface-desingularization`
compiled both its sandbox check and the final module cleanly (3.3 seconds each).

## Second reading by NQ

This is the author's self-check; the dispatcher explicitly forbids starting other agents,
and the maintainer performs the independent review. With the node and final file open,
I rechecked the integral and Noetherian binders, all-affine excellence, exact dimension
two, and the existential ample invertible module against every hypothesis. I checked
the integral regular source, finite-projective-space factorization, actual induced
function-field map, and isomorphism over exactly all regular points against every
conclusion. I read the generic-stalk map and finite-coordinate projectivity definitions:
neither adds curve or base-field assumptions. No missing hypothesis or clause, copied
definition, node correction, or mismatch was found; no change was necessary.
