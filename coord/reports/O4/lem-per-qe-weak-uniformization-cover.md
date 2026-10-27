## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiExcellentWeakUniformizationCover` states
`AlgebraicGeometry.exists_regular_weakUniformization_cover`. Its only proof is `sorry`.
It introduces no definition and changes the item node only in `lean`.

I read the full item statement, all eight proof steps, the statements and Lean records of
all eight statement dependencies, and the recorded declarations in their source files.
I also read the current blueprint ancestor proof, in
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`.
The ancestor's current Step 3 uses Verdier duality; the item's own reviewed source is the
ILO weak uniformization argument, not a new assertion of that blueprint unit. I read ILO
Exposé VII pp.81–83 (Theorem 1.1 and its induction proof) and Exposé II pp.28–29
(ordinary alteration topology and Theorem 3.2.1, including its separate proof for parameter 1).
VII 1.1 supplies finite regular connected sources; regular Noetherian connected sources
are integral. II 3.2.1 supplies integral P and a Zariski refinement in the ordinary case.

The clause-by-clause correspondence is:

- The input is `Y : Scheme.{u}`. `[IsIntegral Y]` includes nonemptiness, reducedness,
  and irreducibility, exactly as in def-pc-integral-scheme. No additional separatedness
  or finite-dimensionality assumption is made.
- `[IsNoetherian Y]` is the Noetherian condition stated in the node: Mathlib
  `isNoetherian_iff_of_finite_affine_openCover` identifies it with a finite affine cover
  by spectra of Noetherian rings. This is not merely a Noetherian underlying space.
- `hqe : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ IsQuasiExcellent Γ(Y, U.1)`
  expresses existence of an affine open cover with quasi-excellent coordinate rings.
  Selecting all such opens gives the cover; conversely every cover supplies this
  pointwise condition. It does not require an arbitrary supplied chart to be excellent,
  or replace quasi-excellence by excellence.
- `n : ℕ` and `T : Fin n → Scheme.{u}` express finitely many source schemes. The
  existential `_hT : ∀ i, IsIntegral (T i)` gives nonempty integral sources and provides
  the actual instances used by each generic stalk map. `IsRegularScheme (T i)` and
  `IsNoetherian (T i)` impose regularity and global Noetherianness on every source.
- `f : ∀ i, T i ⟶ Y` gives the maps. `IsDominant (f i)` is dense image, and
  `LocallyOfFiniteType (f i) ∧ QuasiCompact (f i)` is finite type in the recorded
  dependency's exact convention.
- Each `hη : f i (genericPoint (T i)) = genericPoint Y` identifies the actual generic
  point images, and `((f i).functionFieldMap hη).hom.Finite` says that the canonical
  field extension is finite. The generic-point equality follows from dominance of
  a map between integral schemes; it is exposed to type the canonical stalk map,
  not imposed as an independent restriction. `Scheme.functionField` is the local
  ring at the generic point, not an independently selected field or algebra structure.
- `P : Scheme.{u}`, `_hP : IsIntegral P`, and `IsNoetherian P` give the integral
  Noetherian refinement, including its nonemptiness.
- `g : P ⟶ Y`, `IsProper g`, and `Surjective g` give the proper surjective map.
  Its generic-point equality and `(g.functionFieldMap hη).hom.Finite` express the
  same finite function-field-extension condition. Surjectivity implies dominance;
  no extra dominant hypothesis on g is necessary.
- `U : Fin n → P.Opens` gives the open subschemes `P_i = (U i).toScheme` and
  `(⨆ i : Fin n, U i) = ⊤` is precisely the covering condition. The inclusions
  `(U i).ι` are the canonical open immersions, not arbitrary embeddings.
- `lift : ∀ i, (U i).toScheme ⟶ T i` gives the refinement maps. The equations
  `lift i ≫ f i = (U i).ι ≫ g` say exactly that these are Y-morphisms. The same
  `Fin n` indexes both families, allowing repeated T_i as in the node's Step 8.
- There is no invertibility assumption, selected prime, prime-to-a-prime degree,
  separability assumption, or regularity conclusion for P.

Dependency declarations used:

- def-exc-excellent-ring: `Sheaf.RingTheory.ExcellentRing`, `IsQuasiExcellent`.
  Its full definition is Noetherian, G-ring, and open regular loci of finite-type algebras.
- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, with `AlgebraicGeometry.QuasiCompact`.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; used via the canonical inclusions of open subschemes.
- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`,
  as used by `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (separated, universally closed, locally finite type;
  universally closed implies quasi-compact).
- def-weil-regular-scheme: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme` (locally Noetherian and regular stalks).
- def-weil-surjective-morphism: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`. The same module supplies `IsDominant` as dense range.
- Function fields use Mathlib `Scheme.functionField` (generic stalk). The canonical map
  `Scheme.Hom.functionFieldMap` is imported from
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`; I read its full signature
  and definition, which apply to arbitrary integral schemes, despite the module's name.
  `RingHom.Finite` measures finiteness for this actual map.

The module also imports every already stated proof dependency: the upstream invertible
ideal module for def-nagata-effective-cartier-ideal; Mathlib DVRs;
`Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`;
`Sheaf.CategoryTheory.Sites.GrothendieckTopos`; upstream regularity; and
`Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization`. The finite-type composition and
base-change matches are already in the public finite-type import. The remaining proof
dependencies (ordinary topology, complete-local nodal reduction, log-pair strict resolution,
proper refinement, and local reduction) have no Lean record or match yet, so have no module
to import. They are not needed to type the statement and were not copied or restated here.
All eight steps of the node's proof, with their dependencies, are in the theorem docstring.

Edge cases checked before writing:

- An empty input is excluded by the node's integrality/nonemptiness, not by a new binder.
- With `n = 0`, the open union is bottom. It cannot cover integral nonempty P, so the
  conclusion correctly disallows an empty output family over nonempty Y without an
  added `0 < n` clause. Empty individual P_i are allowed by the statement.
- For an integral regular Noetherian Y one may take n=1, T_0=P=Y and identity maps;
  the canonical field maps have degree one and the sole open is top.
- For a field spectrum the same identity construction applies in every characteristic.
- Neither higher-dimensional singular inputs nor Noetherian schemes with unbounded
  global Krull dimension are excluded by the binders.
- Inseparable finite extensions are included: `RingHom.Finite` has no separability
  content. No algebra structure unrelated to f or g is quantified.
- All schemes have the same object universe u as Y; finite-type sources and the proper
  refinement can be represented in that universe. No independent smaller test universe
  or equality of unrelated site universes is imposed.

Searches made for an existing statement or notion:

- msearch LeanFinder: “A quasi excellent integral Noetherian scheme admits a finite
  regular alteration cover with a proper surjective generically finite refinement”.
  Eight hits: integrality, normalization, ordinary compact covers and dominance of
  normalization. None states weak uniformization or the required refinement theorem.
- msearch Loogle: `AlgebraicGeometry.Scheme.functionField, Module.Finite` returned
  zero hits. The existing generic stalk map was found by reading project sources.
- msearch LeanSearch: “A quasi excellent noetherian scheme has a covering by regular
  alterations with a proper surjective generically finite refinement”. Eight hits on
  locally Noetherian schemes, finite affine covers and finite-type zero-dimensional
  schemes; no weak uniformization theorem. One hit was the useful Noetherian-cover iff.
- msearch grep of Mathlib AlgebraicGeometry: `alteration|uniformi[sz]ation|quasi.?excellent`
  returned zero hits.
- rg of the item's id in `lean/WeilConjectures` and `lean/Sheaf` returned no hits.
  rg for `weakUniformization|weak_uniformization|IsGenericallyFinite|GenericallyFinite`
  found only other specialized alteration modules; none has the stated conclusion.
- rg for `functionFieldMap` located existing canonical maps in the upstream divisor
  pullback module and uses in finite-normal-cover and curve modules. Those were read;
  the upstream map is reused. `ProjectiveGenericallyFinite` concerns an already given
  projective map with zero-dimensional generic fibre, not existence of regular sources.
- rg for `exists_regular_weakUniformization_cover` in Mathlib, both project roots and
  `dag/lean_names_upstream.json` returned no clash.

Validation: scompile.py compiled the sandbox and the actual library module cleanly
(3.3 s and 3.8 s). The first attempt required changing affine-open membership `y ∈ U`
to explicit membership `y ∈ U.1`; the final statement has that correction. No diagnostic
commands, definitions with postponed data, or extra theorem proofs remain. No statement
correction, disputed statement, new node, or dependency repair was needed.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
