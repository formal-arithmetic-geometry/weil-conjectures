## Worker report

The delivery states `AlgebraicGeometry.excellent_normalized_blowup_tower` in
`Sheaf.AlgebraicGeometry.ExcellentNormalizedBlowupTower`. Its sole proof is `sorry`.
No definition is copied or introduced, and no mathematical statement is corrected.
The earlier sandbox module was retained and repaired: the `letI` in the signature was
removed by supplying its integrality proof explicitly to the generic-point and
function-field-map APIs; all currently stated proof dependencies are imported, and the
proof docstring now follows all eight DAG steps. The node changes only in `lean` and `stmt_deps`. The latter cites the landed definition
nodes `def-trf-normalized-blowup` for `IdealSheafData.normalizedBlowup` and
`IdealSheafData.normalizedBlowupMap`, and `def-weil-pbc-reduced-normalization` for
`Scheme.fromReducedNormalization`, which occurs directly in the finiteness conclusion.
The theorem node `lem-trf-normalized-blowup-calculus` is not a statement dependency.

Hypotheses and objects, in node order:

- An arbitrary integral scheme is `(X : Scheme.{u}) [IsIntegral X]`, with explicitly bound
  universe `u`. No field, finite-type-over-a-field, separatedness or regularity condition
  is imposed.
- Finite dimension at least one is `(d : ℕ) (hd : 1 ≤ d)` and
  `hDim : topologicalKrullDim X = d`, using the natural-number coercion to `WithBot ℕ∞`.
  Scheme dimension is topological Krull dimension, agreeing with `ringKrullDim` on affines.
- The finite affine Noetherian cover is `[IsNoetherian X]`. Mathlib's class means locally
  Noetherian and compact; `isNoetherian_iff_of_finite_iSup_eq_top` identifies it with exactly
  the finite-affine-cover formulation in the node, without requiring a finite discrete
  topology or a separated scheme.
- Excellence on every affine open is
  `hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U)`.
- A supplied finite tower is given by `n : ℕ`, `level : Fin (n + 1) → Scheme.{u}`,
  the ideal family `center`, and adjacent arrows `arrow`.
- `hzero : level 0 = X.normalization` specifies the initial function-field normalization.
  Equality here just fixes the chosen presentation: any isomorphic representative can
  be replaced by the canonical initial object and its adjoining arrow transported.
- `hpoint` gives for each center a point `x`, closedness of its singleton, and equality
  with `Scheme.IdealSheafData.vanishingIdeal` of its closure. Since the singleton is
  closed, the closure is that singleton. This is precisely the reduced induced point
  structure, not an arbitrary primary or thickened center.
- `hblowup` supplies an isomorphism from each next level to the center's canonical
  `normalizedBlowup`, whose hom followed by `normalizedBlowupMap` equals the supplied
  arrow. These existing definitions are componentwise normalization of the ordinary
  blowup and its structural map. In this tower every ordinary blowup is integral:
  initially X is integral, d is positive, the closed center misses its generic point,
  and the ordinary integral-blowup argument iterates. Thus componentwise normalization
  is the same normalization in its function field. This use makes no rational-base
  hypothesis: the definitions in NormalizedBlowupCalculus are unrestricted, and its
  theorem specialized to finite type over ℚ is not used to assert this result.
- `π`, `hπzero`, and `hπstep` supply the composites to X, including the initial
  normalization map, with their exact recursive equations.
- `r` and `hr` name the last composite, as required for the subsequent clauses.
  They add no restriction to the supplied tower since its finite composites always
  exist and satisfy these equations.

Conclusions, in node order:

- `∃ hIntegral : ∀ i : Fin (n + 1), IsIntegral (level i)` gives integrality of EVERY level.
  The witness is used explicitly at the endpoint to type its generic point and canonical
  function-field map. No integrality of a level is assumed in the theorem's hypotheses.
- `(∀ i, IsNoetherian (level i))`, `(∀ i, topologicalKrullDim (level i) = d)`, and
  `(∀ i, ∀ U : (level i).affineOpens, IsExcellent Γ(level i, U))` give exactly the stated
  Noetherianity, unchanged dimension and excellence.
- `(∀ i, ∀ x : level i, IsDomain ((level i).presheaf.stalk x) ∧
  IsIntegrallyClosed ((level i).presheaf.stalk x))` gives normality in the prescribed
  local-ring formulation.
- `IsFinite X.fromNormalization` and
  `∀ i : Fin n, IsFinite ((center i).blowup.fromReducedNormalization)` account for ALL
  normalization morphisms used: the initial one and each ordinary blowup's normalization.
- `IsProjectiveBundle r` uses exactly the recorded finite-type quasi-coherent-module
  projective-bundle convention; it does not substitute finite-projective-space projectivity.
- The existential `hη` says r sends the endpoint's generic point to X's generic point;
  `IsIso (@Scheme.Hom.functionFieldMap ... r hη)` says the induced canonical stalk map
  `k(X) → k(X_n)` is an isomorphism. This uses the actual morphism, not an unrelated field
  equivalence or a choice of algebra structure.
- For EVERY `U : X.Opens`, normality of all stalks of `U.toScheme` and disjointness of
  the images of the centers' supports from U imply `IsIso (pullback.snd r U.ι)`.
  `π i.castSucc x ∉ U` is the exact image-complement condition, and the second projection
  is the specified morphism `X_n ×_X U → U`.
- The final universally quantified U-clause explicitly states that initial normalization
  is an isomorphism over every normal open, including length zero.
- No level is asserted regular, and no tower or regular endpoint is existentially built.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; its scheme formulation is
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`, with the
  finite-affine-cover equivalence cited above.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` (with `IsQuasiExcellent` and
  `IsUniversallyCatenary` read in full).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`; for the scheme's dimension,
  `topologicalKrullDim` in `Mathlib.Topology.KrullDimension`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization` and `.fromNormalization`.
- `Sheaf.AlgebraicGeometry.FunctionField`: its arbitrary-integral-scheme clause explicitly
  reuses `AlgebraicGeometry.Scheme.functionField` in `Mathlib.AlgebraicGeometry.FunctionField`.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `AlgebraicGeometry.Scheme.Hom.functionFieldMap`; its current full signature and docstring
  were obtained with `scompile.py --source`, since that module is absent locally.
- `WeilConjectures.Blowup.Gluing`: `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and
  `.blowupMap`; `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `.vanishingIdeal`.
- `Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus`:
  `AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup` and `.normalizedBlowupMap`;
  `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization` and
  `.fromReducedNormalization`. These reuse the recorded ordinary blowup construction.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, paired with
  `IsDomain` at the stalks as prescribed by def-weil-pbc-normal-ring.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `AlgebraicGeometry.IsProjectiveBundle`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and `pullback.snd`.

Proof-dependency imports include finite-type localization of excellence, componentwise
normalization affine charts, excellent normalization preparation, normal dense-open integral
sections, closed dominant dimension, excellent affine covers, finite projective-bundle maps,
projective-bundle properness, and the ordinary-blowup complement theorem, in the modules
listed in the Lean header. The two proof-only nodes
`lem-per-integral-blowup-projective-geometry` and `lem-per-projective-bundle-composition`
have no Lean record or Mathlib match on the current base, so no module can yet be imported
for them. They are not prerequisites of the statement; their future imports belong to
maintainer synchronization under stages/2-statements.md §3(7).

Edge cases checked before the repair:

- n = 0: `Fin 0` gives empty center and arrow families; `Fin (0 + 1)` retains its one
  initial level and `Fin.last 0` is zero. The composite is the initial normalization map,
  and the last clause expressly supplies its normal-open isomorphism.
- U empty: its stalk condition and center avoidance are vacuous; the restriction is a map
  between empty schemes, as required. U = X: center avoidance forces no centers, and for
  n = 0 the normality hypothesis makes normalization an isomorphism.
- Dimension one is included, where blowing up a reduced closed point on the normal curve
  is allowed; no surface hypothesis is added. Dimension zero is excluded by the node's
  explicit d ≥ 1, so a blowup at the sole generic point cannot spoil integrality.
- Integral schemes are nonempty. The empty X is excluded by the original node, whereas
  empty opens are retained. Non-affine and non-separated X are allowed.
- No characteristic or rational-field restriction appears, despite importing the canonical
  construction from a module whose main calculus theorem has a rational-base specialization.
- The explicitly bound single scheme universe covers all objects in a supplied finite
  tower; there is no independent small test universe that could make a condition vacuous.

Searches (in addition to the node's existing search log):

- `msearch.py leanfinder`: “An excellent integral Noetherian scheme and every finite tower
  of normalized blowups at closed points has finite normalization projective birational
  composite and unchanged dimension”. Eight results are relative-normalization facts
  (`Scheme.Hom.normalization`, `instIsIntegralNormalization`, integral normalization maps,
  dominance and quasi-compactness); none states this tower theorem.
- `msearch.py loogle`: `"normalization"`. Twelve results concern Aesop normalization rules,
  not scheme towers; no match.
- `msearch.py grep`: `normalizedBlowup|normalized_blowup|blowup_tower` in
  `AlgebraicGeometry`. Zero Mathlib hits.
- `rg` in upstream WeilConjectures, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item ID and `excellent_normalized_blowup_tower`: no existing theorem; the project
  excellent-surface-desingularization module mentions this node only in its proof docstring.
- Broader normalized/blowup/tower searches found the existing NormalizedBlowupCalculus
  definitions and the completion-descent statement. The former is reused; the latter
  descends a completed local tower and does not assert this tower's geometry.

Sources opened: Stacks resolve.tex, definition-normalized-blowup and
lemma-Nagata-normalized-blowup (Tag 0BFT), and the recorded dependency modules listed above.
No `STATEMENT-DISPUTED` issue or missing statement notion was found. No new nodes and no
dependency-module repairs are needed.

Validation: `scompile.py N1 lem-per-excellent-normalized-blowup-tower` compiled both its
sandbox presentation and its final module path cleanly (3.6 s each). Every variable and
universe is explicitly bound; no local notation, private definition, local instance,
`let` statement binder, extra axiom, or proof other than the single `sorry` remains.

## Returned delivery repair

The independent review of immutable head `592cdcdeabd3` returned one H2 finding.
Replaced `lem-trf-normalized-blowup-calculus` in `stmt_deps` with its existing definition
owner `def-trf-normalized-blowup`, whose `lean.declarations` records both canonical
normalized-blowup definitions, and added `def-weil-pbc-reduced-normalization`, whose
`lean.declarations` records `Scheme.fromReducedNormalization`. Read both definition
nodes and their source declarations: these are real noncomputable definitions, not
choices from the calculus theorem. No calculus assertion is used in this signature.

Compared the saved node against the current shared base: before this repair only `lean`
and `stmt_deps` differed. All other node fields remain identical to that base. The Lean
module is byte-identical to the saved returned packet; its SHA256 is
`8a8dda672e2a31483f77ba4448171bf8c54fb34101061dbd0ac313c9ab5a4a90`.
The mathematical statement, signature, proof docstring and sole `sorry` are unchanged.
No new nodes, dependency modules or statement correction are introduced. The three
review advisories were informational and did not request changes to this module.

Repair validation: `scompile.py` compiled the unchanged module cleanly both as a sandbox
module and at its final library path (3.6 s each). The initial `deliver2.py --no-push`
completed with `OK` after its shared-fetch wait. The local self-check confirmed the exact
`lean.statement`, the unchanged module hash and that the only node differences from the
current base are `lean` plus the two required definition-node additions to `stmt_deps`.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
