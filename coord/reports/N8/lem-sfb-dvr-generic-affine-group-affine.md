## Worker report

The module `Sheaf.AlgebraicGeometry.DvrGenericAffineGroupAffine` states
`AlgebraicGeometry.isAffine_of_affine_genericFiber_of_dvr`, with its sole proof
`sorry`. It adds no definitions. Only the item's `lean` field changes.

Source checked directly: Prasad--Yu, *On quasi-reductive group schemes*,
Section 3, Proposition 3.1, printed page 5 / PDF page index 4,
https://math.stanford.edu/~conrad/papers/qrg.pdf . The proposition is precisely
that a flat finite-type group with affine generic fibre is affine if and only
if it is separated; the node states its sufficient direction. No statement
correction or disputed assertion is needed.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| R a DVR | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` |
| K its fraction field | `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]`; the algebra map is the localization map at all nonzero elements, not an arbitrary field extension |
| S = Spec R | `Spec (CommRingCat.of R)` |
| G an S-scheme | `G : Over (Spec (CommRingCat.of R))`, whose underlying scheme is `G.left` and structure map is `G.hom` |
| Multiplication, unit and inverse satisfying all group diagrams | `[GrpObj G]`: `MonObj.mul`, `MonObj.one`, associativity and two unit laws, and `GrpObj.inv` with both inverse laws; the cartesian product in `Over S` is the fibre product over S |
| Flat | `[Flat G.hom]` |
| Separated | `[IsSeparated G.hom]`, not properness |
| Of finite type | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the recorded dependency's conjunction |
| Generic fibre is G ×_S Spec K | `pullback G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))` |
| Generic fibre affine | `hgeneric : IsAffine (...)` |
| G affine | `IsAffine G.left` |
| Affine means isomorphic to some ring spectrum | Mathlib `IsAffine X` asserts that the canonical `X.toSpecΓ` is an isomorphism; `Scheme.isoSpec` supplies the spectrum isomorphism, equivalently the essential-image condition |
| No smoothness, connectedness, excellence, henselianity, perfect residue field | None of these predicates occurs in the signature; `GrpObj`, rather than `CommGrpObj`, also retains noncommutative groups |

All variables are explicit, with both auto-implicit options disabled. A single
arbitrary universe u contains R, K and the schemes; there is no quantification
over test schemes in a smaller independent universe. Fraction fields have the
same size as R, and any given collection of these objects may be placed in a
common universe. No characteristic restriction is imposed.

Recorded statement dependencies read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`; its class explicitly
  requires an integral domain and a local PID whose maximal ideal is nonzero.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme` (available through the public imports).
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; `Flat.iff_flat_stalkMap`
  identifies the affine-chart definition with the node's stalkwise one.
- `def-weil-proper-morphism`: its recorded component
  `AlgebraicGeometry.IsSeparated`, imported through the recorded module
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; the node requires separated,
  so its `IsProper` component is deliberately not a hypothesis.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact`, provided by
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its public imports.
- `def-pc-base-change`: recorded module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, whose docstring
  explicitly gives `pullback f T.hom` for scheme base change. Its
  `Scheme.Modules.moduleBaseChange` is for modules and is not substituted
  for scheme base change.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.

The inline group-scheme notion needs no new definition: Mathlib already gives
`CategoryTheory.GrpObj` in `Mathlib.CategoryTheory.Monoidal.Grp`. I read its
full signature and its inherited `MonObj` laws, and the project convention in
`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. That module's
field-specific ancillary terminology is not needed here. No private group
structure is introduced.

The natural-language proof docstring includes all six DAG steps and their
named inputs. Plain imports retain all already-stated proof dependencies:
affine and finite permanence (Mathlib Affine/Finite), smooth-flat (recorded
upstream SmoothFiber), qcqs over affine (Mathlib QuasiCompact/QuasiSeparated),
affine principal comparison (Sheaf AffinePrincipalAffinizationIsomorphism),
quasi-compact cancellation (Mathlib QuasiSeparated), open-immersion base
change (Mathlib OpenImmersion), finite-surjective affine target (upstream
FiniteSurjectiveAffineTarget), and fpqc affine descent (Sheaf FpqcAffineDescent).
No Lean statements are currently recorded for the proof-only nodes
`lem-sfb-trait-group-finite-smooth-cover`,
`lem-sfb-flat-trait-group-affinization`,
`lem-sfb-smooth-trait-principal-translate-cover`,
`lem-sfb-field-groupoid-open-image-closed`, or
`lem-sfb-immersion-principal-affineness`; their imports cannot yet be added.
They are not needed to type the present theorem. No import cycle is introduced.

Edge cases checked before writing: the trivial group is included; finite
constant groups with disconnected fibres are included; μ_p over a DVR in
residue characteristic p is included without requiring smoothness or reducedness;
noncommutative affine groups are included; mixed and equal characteristic,
imperfect residue fields, and nonhenselian/nonexcellent DVRs are retained.
An empty scheme cannot support an identity section over the nonempty spectrum
of a DVR, so the group-object hypothesis correctly rules it out. A field or
zero ring is not a DVR under the recorded definition. A proper positive-dimensional
abelian scheme has nonaffine generic fibre and fails exactly `hgeneric`.

Searches for an existing theorem:

- `msearch.py ... leanfinder "A separated flat finite type group scheme over a discrete valuation ring with affine generic fibre is affine"`:
  eight hits, including `IsSeparated.hasAffineProperty`, finite-discrete-space
  affineness, `IsIntegralHom.hasAffineProperty`, affine-space instances, and
  `ValuativeCommSq.domain`; none states this theorem.
- `msearch.py ... leansearch "A flat separated finite type group scheme over a discrete valuation ring with affine generic fibre is affine"`:
  eight hits on separated affine morphisms, `IsAffine` constructors and the
  finite-to-affine implication; no generic-fibre affineness criterion.
- `msearch.py ... loogle "AlgebraicGeometry.IsAffine, AlgebraicGeometry.Flat"`:
  three hits, `Scheme.Hom.flat_appTop`,
  `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`, and
  `isRegularEpi_of_flat_of_surjective_of_isAffine`; all already assume affineness.
- `msearch.py ... grep "Raynaud|generic.*affine|affine.*generic|isAffine.*[Gg]roup" AlgebraicGeometry`:
  four FunctionField hits about generic points of already affine schemes.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, including
  `Raynaud|generic.{0,40}affine|affine.{0,40}generic` and declaration candidates
  `dvr_generic_affine|affine_of_affine_generic|isAffine_of_generic`:
  no theorem match. Nearby results concern flattening and generic-point
  charts; the torus-closedness consumer names this theorem only in its proof.
- `grep -rn "lem-sfb-dvr-generic-affine-group-affine" lean/WeilConjectures`:
  no matches. The upstream declaration-name index contains no matching name.

Validation: `scompile.py N8 lem-sfb-dvr-generic-affine-group-affine` compiled
the delivered module in sandbox and library contexts on the server, both
clean (1.6 seconds each). No proof is supplied at stage 2.

## Second reading by N8

Dispatcher instructions forbid starting other agents. This is an explicitly
labelled second self-reading, not a claim of independent worker review; the
maintainer's independent review remains required. I reopened the original
node and the final module and checked the map direction and all binders.
The generic-fibre map is Spec K → Spec R induced by the fraction-field map
R → K; the pullback is thus G ×_S Spec K, not a residue fibre or an arbitrary
base change. The source is not assumed affine. Finite type includes
quasi-compactness, separatedness does not become properness, and GrpObj
does not impose commutativity. No extra smoothness/connectedness/base-ring
hypothesis occurs. Every conclusion clause is exactly `IsAffine G.left`.
The verbatim signature is extracted from the theorem keyword up to `:=`.
No mismatches found and no corrections were required.
