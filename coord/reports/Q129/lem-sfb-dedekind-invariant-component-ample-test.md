## Worker report

The module `Sheaf.AlgebraicGeometry.DedekindInvariantComponentAmpleTest` states
`AlgebraicGeometry.isAmple_of_dedekind_invariant_component_tests`, with `sorry` as its only
proof. It detects absolute ampleness by exactly the two allowed classes of flat tests.
There are no new definitions, dependency replacements, or statement corrections. The node
copy changes only `lean`.

### Clause-by-clause reading

- The base ring is `D : Type u` with `CommRing D`, `IsDomain D`, `IsNoetherianRing D`,
  `IsIntegrallyClosed D`, and `hdim : ringKrullDim D ≤ 1`. These are precisely the node's
  Noetherian integrally closed domain of dimension at most one. The base is literally
  `Spec (.of D)` throughout. The symbol K in the prose abbreviates `FractionRing D` and
  occurs nowhere in a hypothesis or conclusion, so it requires no additional parameter.
- `H X : Over (Spec (.of D))` supply both schemes and their structure morphisms. `GrpObj H`
  supplies multiplication, inverse and unit, with all group diagrams in the slice. It is
  the same recorded general Mathlib class, now instantiated over this affine base.
- `Smooth H.hom`, `IsSeparated H.hom`, `LocallyOfFiniteType H.hom`, and
  `QuasiCompact H.hom` render smooth, separated and finite type for H. The last two
  together are the dependency node's definition of finite type. `IsSeparated` is defined
  by the closedness of the diagonal, as required. `GeometricallyConnected H.hom` means
  every field-valued base change is connected, equivalently geometrically connected fibres.
- The same four hypotheses on `X.hom` render smoothness, separatedness and finite type
  for X. There is no connectedness, nonemptiness, or surjectivity assumption on X.
- `ModObj H X` is the existing internal action structure. Its `smul` is the morphism
  H ×_S X → X; `one_smul` and `mul_smul` are exactly unit and associativity. The tensor
  product in `Over S` is the recorded scheme fibre product, not a product of point sets.
- `L : X.left.Modules` with `L.IsInvertible` is the given invertible structure-sheaf module.
- The universal testing condition is split into `hfield` and `htrait`. Universal
  quantification over a disjunction of allowed ring classes is equivalent to the
  conjunction of these two universal conditions; this avoids introducing any artificial
  choice of field structure on an already fixed commutative ring.
- In `hfield`, `R : Type u`, `Field R`, and `IsSepClosed R` give every separably closed field
  test. `t : Spec (.of R) ⟶ Spec (.of D)` with `Flat t` is every allowed flat base map.
- In `htrait`, `CommRing R`, `IsDomain R`, `IsDiscreteValuationRing R`, and
  `IsStrictlyHenselianLocalRing R` give every strictly henselian DVR test. The existing
  strict-henselian class extends `HenselianLocalRing` and asserts that its residue field
  is separably closed. Mathlib HenselianLocalRing is the simple-residue-root lifting
  condition; its monic formulation is equivalent, as also expressed by the node's proof
  dependency `IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`. Again `t`
  is arbitrary with `Flat t`, not assumed finite type, faithfully flat, or surjective.
- In each test, `Y : Over (Spec (.of R))` and
  `j : Y ⟶ (Over.pullback t).obj X` are an arbitrary subscheme over T of X_T.
  `IsOpenImmersion j.left` and `IsClosed (Set.range j.left)` express exactly an open
  immersion with closed image, hence a clopen subscheme with its induced structure.
  They impose no separate closed thickening or extra ideal structure.
- `ConnectedSpace Y.left` supplies both nonemptiness and connectedness, in accordance
  with `def-weil-connected-scheme`. `Surjective Y.hom` is surjectivity to T.
- For a field test `GeometricallyConnected Y.hom` is exactly geometric connectedness
  of the generic fibre, since the fraction field of a field is that field canonically.
  For a trait test it is
  `GeometricallyConnected (pullback.snd Y.hom
  (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))`:
  the structure morphism of the fraction-field base change. No special-fibre
  connectedness is inserted into either test.
- The invariant condition in each test is the existential `b : H_T ⊗ Y ⟶ Y` and the
  equation `(𝟙 H_T ⊗ₘ j) ≫ Functor.LaxMonoidal.μ (Over.pullback t) H X ≫
  (Over.pullback t).map (γ[H,X]) = b ≫ j`. The middle map is the canonical product
  comparison of the monoidal base-change functor; thus the left side is precisely
  the restricted base-changed action H_T ×_T Y → X_T. The equation states its
  factorization through Y, with no assumed or independently chosen action on Y.
- `j.left ≫ pullback.fst X.hom t` is the canonical map Y → X_T → X. Therefore
  `(tensorPullback (j.left ≫ pullback.fst X.hom t)).obj L` is precisely L_Y.
  `@IsAmple` is supplied its existing, mathematically forced invertibility proof
  `((invertible_pullback_tensor ...).1 L).2`. This is no extra hypothesis on the tests.
  It requires the invertible-pullback-tensor module to be public because the proof
  appears in the exported signature. It is already a proof dependency of the item.
- The conclusion `IsAmple X.left L` is the exact recorded absolute ampleness predicate,
  including quasi-compactness and affine nonvanishing loci of positive tensor powers.
  There is no weakening to generic, fibrewise, relative-only, or local ampleness.

### Dependency declarations used

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-connected-scheme`: `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`.
- `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-pc-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed`.
- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-ample-invertible-module`: `WeilConjectures.AlgebraicGeometry.Ample`, `AlgebraicGeometry.Scheme.Modules.IsAmple`.

For connectedness of geometric fibres the associated declaration is
`AlgebraicGeometry.GeometricallyConnected` from
`Mathlib.AlgebraicGeometry.Geometrically.Connected`, as explicitly recorded in that
multi-notion dependency's note. The generic-fibre construction uses `FractionRing`,
`algebraMap`, `Spec.map` and `pullback.snd`. Relative separatedness is
`Mathlib.AlgebraicGeometry.Morphisms.Separated.IsSeparated` (declaration namespace
`AlgebraicGeometry`). The action uses `CategoryTheory.ModObj` from
`Mathlib.CategoryTheory.Monoidal.Mod`, via its cartesian specialization. The canonical
base-change product comparison comes from `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`.
Strict henselianity uses the existing `IsStrictlyHenselianLocalRing` from
`WeilConjectures.Mathlib.RingTheory.Henselian`.

All statement-dependency records, full signatures and docstrings were read in the live
source clone, including the tensor pullback adjunction and the definitions of ample and
invertible modules. Every recorded proof-dependency module, including Mathlib matches,
is imported; those needed only for the proof use plain `import`. The four proof nodes
without a recorded declaration or Mathlib match (smooth-normal ascent, finite-coproduct
ampleness with points, strict-local sections, and algebraic-space relative-ampleness
fpqc descent) have no module to import yet. They are proof prerequisites, not missing
notions needed to type this statement. The declaration docstring carries all ten proof
steps and their existing DAG inputs.

### Sources and edge cases

Read BLR §6.4 Proposition 2, printed pp.153–154, in the primary online scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf
(PDF pages 159–160, zero based). The local/strict-local/component/surjective/generic-fibre
reductions are the source of this auxiliary statement. The generic-only component case
is explicitly restarted over a field, as BLR instructs when the open image loses strict
henselianity. Read the current blueprint unit and proof under `literature/blueprint/latest/`;
this is an auxiliary lemma, not that unit's own assertion.

Checked before writing and reread after elaboration:

- X empty: allowed; there is no `Nonempty X` or `ConnectedSpace X`. Test pieces must be
  nonempty, so no such pieces exist on the empty scheme. Absolute ampleness is valid
  because the empty scheme is compact and its pointwise condition is vacuous.
- D a field, dimension zero: allowed by `≤ 1`, with no nonfield or exact-dimension
  hypothesis. Its separable closure is an allowed flat field test.
- H trivial: allowed by `GrpObj`; the action need not be faithful or transitive.
- X disconnected: allowed; connectedness appears only for the test subschemes Y.
- Y empty: correctly excluded by `ConnectedSpace`, as stated by the node.
- Components missing the closed trait fibre: not incorrectly required to be trait
  tests, since surjectivity excludes them there. The separate flat field tests cover
  them after extension of the generic fraction field. No assumption of special-fibre
  surjectivity is made on X itself.
- Arbitrary characteristic: no characteristic-zero, perfection, or algebraic-closure
  assumption is introduced. Separably closed fields are not replaced by algebraically
  closed fields.
- Test size: `R : Type u` matches the universe of `Scheme.{u}`, rather than an unrelated
  potentially smaller universe. Every scheme and morphism variable, and universe u,
  is explicitly bound; both auto-implicit options are false.

### Searches

All msearch calls used group Q129 and this item identifier on 2026-10-24.

- LeanFinder query: "An invertible sheaf is ample if its restrictions to invariant
  connected components after separably closed field and strictly henselian DVR flat
  base change are ample". Eight hits on affine-local properties and general reductions;
  none is this theorem.
- LeanSearch query: "ampleness of invertible sheaves after flat base change to strictly
  henselian discrete valuation rings". Eight hits concerning flat base change and
  HenselianLocalRing; none states this ampleness test.
- Loogle query: `AlgebraicGeometry.Scheme.Modules.IsAmple, CategoryTheory.GrpObj,
  CategoryTheory.MulAction`. No match; the Mathlib search index does not know the
  project's IsAmple. Loogle `CategoryTheory.ModObj` returns the existing action class,
  its action map and standard instances; it is reused rather than redefined.
- msearch grep `IsAmple|invariant.*[Cc]omponent|[Aa]ction` in `AlgebraicGeometry`
  returned unrelated local-fraction entries. The targeted grep
  `invariant_component|component_ample|isAmple` in the same directory returned zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `invariant_component|component_ample|isAmple_of_dedekind_invariant_component_tests`
  returned no existing statement. Broader searches found unrelated component,
  group-action and ample-family results, which were inspected where relevant.
- The exact item identifier in `lean/WeilConjectures` and the exact proposed declaration
  name in `dag/lean_names_upstream.json` yielded no match. Existing group-scheme, internal
  action, geometric-connectedness, invertible pullback, and strict-henselian declarations
  were opened directly and reused.

### Validation

Per-file compile uses only the prescribed scompile.py wrapper. The first compile found
that the invertible-pullback-tensor module must be public for its proof term to occur in
the signature; that import was repaired. The next server compile identified two whitespace
warnings for the scoped action notation, repaired to `γ[H,X]`. No theorem is proved and
there are no data definitions or diagnostic commands in the delivery.

## Second reading by Q129

No second reading by a worker: this dispatch requires direct delivery, and the maintainer's
independent review reads the delivery. The clause mapping above records the worker's own
final rereading, not an independent review.
