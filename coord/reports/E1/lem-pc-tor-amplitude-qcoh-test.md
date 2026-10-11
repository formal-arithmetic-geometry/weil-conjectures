## Worker report

The main module `Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest` states
`AlgebraicGeometry.torAmplitude_of_quasiCoherent_tests`, with proof `sorry`.
No theorem is proved. The companion definition contains no `sorry` and defines
vanishing of a derived tensor cohomology sheaf via a K-flat representative.

Clause-by-clause rendering of the unchanged item:

- Scheme X: `(X : Scheme.{uT})` uses Mathlib `AlgebraicGeometry.Scheme`.
- X quasi-separated: `[QuasiSeparatedSpace X]`. The dependency's recorded
  `AlgebraicGeometry.QuasiSeparated` describes morphisms; its Mathlib module proves
  that the terminal morphism is quasi-separated iff the scheme's underlying space
  is `QuasiSeparatedSpace`. The spatial formulation is precisely the scheme clause,
  not a restriction on a different morphism.
- E in D_QCoh(O_X): `(E : schemeDerivedCategory X)` and
  `(hE : schemeDerivedQCohProperty X E)` assert that every cohomology sheaf of E is
  quasi-coherent, exactly the full-subcategory condition. The `HasDerivedCategory`
  binder supplies the shared localization for Mathlib's existing Abelian instance;
  it imposes no extra geometric hypothesis.
- Integers a ≤ b: `(a b : ℤ) (hab : a ≤ b)`.
- Every quasi-coherent O_X-module F: the hypothesis quantifies over
  `SheafOfModules.{uT} (moduleRings X.toRingedSpace)` with `F.IsQuasicoherent`.
- Every i outside [a,b]: `∀ i : ℤ, i < a ∨ b < i → ...`; the endpoints are included.
- Vanishing of H^i(E ⊗ᴸ F): `schemeDerivedTensorCohomologyVanishes X E F i`.
- Conclusion: the same vanishing for **every** O_X-module G, with the same outside
  interval condition and no quasi-coherence premise on G. This is precisely the
  item's spelled-out Tor-amplitude conclusion.

The vanishing predicate uses an existential K-flat representative P with
`Nonempty (DerivedCategory.Q.obj P ≅ E)` and `IsZero` of degree-i cohomology of
`CochainComplex.mapBifunctor P F[0] (curriedTensor _)`. Thus the predicate cannot be
true by absence of representatives. Tags 06YS and 06YU justify that any such
representative computes E ⊗ᴸ F, and that representatives exist. Isomorphic derived
objects have isomorphic cohomology; allowing a different P for each F and i changes
no vanishing condition. In particular this is not an unconstrained tensor functor
or a hypothesized vanishing criterion. `F[0]` is Mathlib's
`HomologicalComplex.single _ (ComplexShape.up ℤ) 0`; `.homology i` is cohomology for
the cochain complex. The tensor comes from the shared
`SheafOfModules.monoidalCategory X.sheaf`, also used by the recorded K-flat predicate.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated` and the scheme `QuasiSeparatedSpace` criterion.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`; the first two implement
  the full-subcategory membership without changing the carrier category.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`, with R = X.sheaf;
  the existing tensor-zero preservation instances enable total tensor.
- Mathlib `CochainComplex.mapBifunctor`, `HomologicalComplex.single`,
  `HomologicalComplex.homology`, `CategoryTheory.Limits.IsZero` and
  `DerivedCategory.Q`, with the shared `moduleRings` from
  `Sheaf.Paper.DerivedHomMayerVietoris` (imported through DerivedCategory).

Edge cases checked before writing: X empty (all sheaves zero); E zero; F or G zero;
a=b (only one degree is permitted); arbitrary negative bounds and unbounded E;
X affine (the source reduces directly to Tag 08E9); non-quasi-coherent G remains
covered. No quasi-compactness, Noetherianity, boundedness or field hypothesis added.
All universes and variables are explicit; module sheaves and K-flat test complexes
use the scheme's universe. The localization morphism universe remains arbitrary.
No statement correction or disputed statement.

Sources were unavailable as local Stacks tex files, so the exact original tags
were read at https://stacks.math.columbia.edu/tag/08EA,
https://stacks.math.columbia.edu/tag/06YS and
https://stacks.math.columbia.edu/tag/06YU. The three-step natural-language proof in
the theorem docstring retains all the item's proof dependency names.

Searches (via msearch.py, plus direct rg and blueprint_refs.py):

- LeanFinder: "Tor amplitude of quasi-coherent derived complexes tested on
  quasi-coherent modules": 8 hits, all derived-category truncation/support
  declarations, no exact statement.
- Loogle: "TorAmplitude, DerivedCategory": 0 hits, unknown TorAmplitude.
- Mathlib grep: "derivedTensor|TorAmplitude|torAmplitude" in Algebra/Homology:
  0 hits.
- LeanSearch: "vanishing cohomology derived tensor sheaves of modules K-flat":
  unavailable, Internal Server Error; no inference drawn from the failed service.
- Loogle: "CochainComplex.mapBifunctor": 12 hits; reuse its actual total tensor
  rather than invent a complex. None defines derived tensor vanishing on O_X.
- Mathlib grep: "derivedTensor|tensor.*[Vv]anish|[Vv]anish.*[Tt]ensor": 11 hits
  on elementary tensor elements/flatness and a metric tensor, no exact predicate.
- rg on WeilConjectures for derivedTensor/TorAmplitude and the item id:
  no exact item; existing derivedTensor is for etale/proetale constant coefficients.
- rg on lean/Sheaf: `DerivedTensor.lean` likewise concerns proetale constant rings;
  `BalancedDerivedTensorModel.lean` concerns modules over rings, not O_X sheaves.
  `KFlat.lean` supplies the needed genuine sheaf K-flat predicate.
- DAG search for derived tensor and tensor cohomology: blueprint_refs gives 35
  results for derived tensor, all coefficient-site notions, and 0 for tensor
  cohomology. DAG rg finds uses of vanishing but no defining node for O_X-derived
  tensor vanishing. No declaration-name collision in Mathlib, WeilConjectures,
  lean/Sheaf, dag/lean_names_upstream.json or existing nodes.

Validation: the two modules compile together on the server with exit code 0 in
3.0 seconds, no warnings. Only the named main theorem contains `sorry`.

## New nodes

`def-pc-derived-tensor-cohomology-vanishes` defines the vanishing predicate
H^i(E ⊗ᴸ F)=0 for O_X-modules, through existence of a K-flat representative with
zero total-tensor cohomology. Sources are Stacks 06YS/06YU and its use in 08EA.
Its module reuses the recorded derived category, K-flatness, and Mathlib total
tensor and cohomology. The searches above are preserved in its mathlib_searches.
Neither the DAG nor the project nor Mathlib has this O_X predicate; the existing
constant-coefficient etale/proetale tensor definitions are different categories.
The item gains this definition as a statement dependency; its original statement
and every other field remain unchanged.

## Second reading by E1

I independently read the item, both delivered modules, all their definition-node
signatures, and the original Stacks tex. The source files are absent in the
read-only repository; I fetched upstream `perfect.tex` and `sites-cohomology.tex`
into this item's scratchpad. `perfect.tex`, label `lemma-tor-qc-qs` (08EA),
introduces exactly X quasi-separated, E in D_QCoh(O_X), and a <= b, with no
quasi-compactness or finiteness standing hypothesis. The item selects (2) => (1).
No statement correction is needed and there is no `statement_change` to audit.

Object/hypothesis/conclusion checklist (each verdict: exact):

1. Scheme X: `(X : Scheme.{uT})`. I read `Scheme` and `Scheme.Hom` in Mathlib's
   `AlgebraicGeometry/Scheme.lean`: locally ringed spaces with an affine open
   neighbourhood at every point, not varieties over a field.
2. X quasi-separated: `[QuasiSeparatedSpace X]`. The dependency defines
   quasi-compact diagonal and explicitly includes the scheme clause. Mathlib's
   `quasiSeparatedSpace_iff` identifies this spatial condition with
   `QuasiSeparated (terminal.from X)`; `quasiSeparated_iff_quasiSeparatedSpace`
   also applies to the map to Spec Z. No extra quasi-compactness is present.
3. E in D_QCoh(O_X): `(E : schemeDerivedCategory X)` together with
   `(hE : schemeDerivedQCohProperty X E)`. The dependency module's first definition
   is Mathlib `DerivedCategory` on the shared O_X-module category; its property
   is `forall n : Z, ((DerivedCategory.homologyFunctor _ n).obj E).IsQuasicoherent`.
   Membership in that property is exactly membership in its full subcategory.
   The localization universe binder uses Mathlib's existing Abelian instance;
   it supplies the category construction, not a geometric restriction.
4. Integers and ordering: `(a b : Z) (hab : a <= b)` (Lean uses Unicode symbols).
   They are arbitrary integers, including negative bounds and a=b.
5. Each quasi-coherent test F: `h` quantifies over
   `SheafOfModules.{uT} (moduleRings X.toRingedSpace)` and requires
   `F.IsQuasicoherent`. `moduleRings` is the structure sheaf forgotten from
   commutative rings to rings. This is O_X-modules on the open-set site.
6. Each degree outside the closed interval: `∀ i : ℤ, i < a ∨ b < i →`, after the binder for F. Degrees a and b
   are included in the permitted range.
7. Hypothesis vanishing: `schemeDerivedTensorCohomologyVanishes X E F i`.
   Its actual definition requires a K-flat P, an isomorphism `Q.obj P ≅ E`, and
   `IsZero` of degree-i cohomology of the total tensor of P and F[0]. See the
   independent definition audit below; this is the cohomology SHEAF, not its
   global sections or hypercohomology.
8. Conclusion: `forall G : SheafOfModules.{uT} (moduleRings X.toRingedSpace),
   forall i : Z, i < a ∨ b < i -> schemeDerivedTensorCohomologyVanishes X E G i`.
   G has no quasi-coherence premise. This is exactly the node's spelled-out Tor
   amplitude, with the same tensor and outside-interval condition as in `h`.

New definition audit: `def-pc-derived-tensor-cohomology-vanishes` is a definition
node in the item's chapter and unit. I checked its statement, sources, empty
proof/proof_deps, created record, blueprint ancestor/via, lean_audit, searches,
and Lean record against brief-stage2 section 5. It cites the scheme, derived
category, K-flat and total-tensor definition nodes, and the item cites it.
No companion dependency module is being delivered.

I read `CochainComplex.IsKFlat` in `Sheaf.Algebra.Homology.KFlat`: the actual
predicate is acyclicity of F tensor P for every acyclic F, with the sheaf tensor
on X.sheaf. I read `CochainComplex.mapBifunctor` and
`HomologicalComplex.mapBifunctor`: the former specializes the latter to up Z;
it forms the direct-sum total complex. The shared sheaf monoidal construction
is sheafification of the sectionwise tensor, not an arbitrary bifunctor.
`HomologicalComplex.single _ (ComplexShape.up Z) 0` places F in degree zero.
The existential derived isomorphism really binds P to E; it is not an extra
unconstrained map. Stacks 06YS supplies K-flat representatives; the paragraph
before `definition-derived-tor` (06YU), including the cofiltered-resolution and
quasi-isomorphism comparison argument, gives independence of representative.
Commutativity of O_X gives the symmetry needed to use the K-flat factor on the
left. Consequently a different representative for each (F,i) gives precisely
the same vanishing proposition, with no added witness hypothesis. No data or
proof is `sorry` inside this definition.

Independent searches, with different wording from the worker:

- LeanFinder via msearch: "A derived sheaf has bounded tensor cohomology if all
  quasicoherent test sheaves do": 8 generic cohomology, t-structure and sheaf
  Grothendieck-category hits; none states 08EA.
- Loogle via msearch: `CochainComplex.IsKFlat`: unknown identifier, zero hits.
- Mathlib grep via msearch: `amplitude|tensorCohomology|derived.*[Vv]anish`:
  only higher derived functor vanishing on projectives/injectives, not this item.
- LeanSearch via msearch: "sheaf derived tensor cohomology zero detected by
  quasicoherent modules": unavailable (Internal Server Error). No mathematical
  verdict is drawn from this service failure.
- Direct rg on WeilConjectures and lean/Sheaf for TorAmplitude/torAmplitude,
  derivedTensor and tensorCohomology, and definition-name searches: no exact
  criterion or O_X-derived tensor cohomology vanishing predicate.
- I opened upstream `CategoryTheory/DerivedCategory/TorAmplitude.lean` rather
  than dismissing its generic name. `DerivedCategory.torAmplitudeIn` tests all
  objects via a derived monoidal tensor under Grothendieck, monoidal closed,
  preadditive, braided and `Qh.HasDerivedMonoidalCategory` instances. It neither
  states detection by quasi-coherent objects nor defines single-degree tensor
  vanishing. It cannot replace this predicate without constructing additional
  derived-monoidal structures and a comparison; no such data is assumed here.
- I opened `Sheaf.Algebra.Homology.DerivedTensor`: its tensor is on the small
  pro-etale site with constant coefficients, not the structure sheaf on X's
  opens. Upstream etale/proetale tensors have the same different carrier.
- DAG rg and `blueprint_refs.py search 'tensor cohomology'`: zero blueprint
  matches; ring tensor cohomology and base-derived tensor cohomology model nodes
  describe rings/algebras and scalar-extension comparisons, not O_X-modules.
  The existing tensor-complex and K-flat nodes supply components already reused.

Edge cases: the empty scheme is allowed (there is no nonemptiness binder), as
are the zero E and zero test sheaves. No index-set quantification introduces an
empty-index exception; the total-complex sums are the standard integer-degree
sums. a=b and a=b=0 retain exactly one permitted degree; i=0 is included or
excluded according to the interval. Unbounded E is permitted. There is no field,
characteristic, Noetherianity, quasi-compactness or finiteness restriction.
Universes uT/wT and u/w are explicitly declared. Test sheaves and representatives
use the same module universe as E; no smaller independent test universe can
make the criterion vacuous. Each ordinary set-sized case is represented by
choosing uT large enough. All names and variables in both signatures are bound.

Mismatch and repair: the proof docstring omitted the explicit observation in
node proof step 1 that E restricted to U still has quasi-coherent cohomology.
I added that sentence before applying the affine equivalence. Both Lean
signatures, the definitions, and the node statements remain unchanged. The
remaining three proof steps and their named dependencies match the node.
The only local `sorry` is the named main theorem; nothing is proved. Module and
declaration docstrings name their source and blueprint id; imports, namespaces
and line lengths satisfy the conventions.

Validation: both delivered modules compiled together cleanly on the server
(exit code 0, 3.1 seconds) before the docstring repair. After the docstring repair, deliver2.py --no-push printed OK: both modules
compile cleanly and the complete delivery passes the stage-2 preflight.
