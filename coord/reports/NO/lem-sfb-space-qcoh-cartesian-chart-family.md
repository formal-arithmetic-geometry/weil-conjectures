## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.AlgebraicSpaceQCohCartesianChartEquivalence`,
with main declaration `AlgebraicGeometry.AlgebraicSpace.qcChartRestriction_isEquivalence`.
It asserts that the explicit canonical restriction functor is an equivalence. There
is one new definition node, described below. No statement correction or disputed
statement is needed. Nothing is proved at theorem level: the four theorem proofs
are `sorry`, with their source and complete natural-language proof plans.

The hypothesis and conclusion correspondence is:

- A scheme S: `{S : Scheme.{u}}`. An algebraic space over it: `(X : AlgebraicSpace S)`.
  The latter is exactly the recorded full subcategory of fppf sheaves with representable
  diagonal and an etale surjective atlas; no separatedness, finiteness, nonemptiness,
  field, Noetherian or characteristic restriction is added.
- The size convention is the explicit universe `u`, inherited from `AlgebraicSpace`,
  its small etale site (objects in `u+1`, arrows in `u`) and its section/ring universe `u`.
  The dependency's `QCoh` and module category are used verbatim. No equality of the
  object and arrow universes is imposed.
- A quasi-coherent module on X: `X.QCoh`, the recorded full subcategory for
  `SheafOfModules.IsQuasicoherent`. Its existing definition uses local presentations
  by arbitrary small coproducts, without finite presentation or finite generation.
- Every etale scheme chart V: `V : X.EtaleSite`. The module on its etale ringed site is
  `F.obj V : SheafOfModules.{u} (X.structureSheaf.over V)`. This uses the localized-site
  interpretation expressly specified by the item and `def-trf-algebraic-space`:
  `V_et = X_et/V`, with the same objects, rings and coverings under chart composition.
  It does not substitute Zariski modules `Scheme.Modules` for etale module sheaves.
- Quasi-coherence on every chart: `CartesianQCohChartFamily` is the full subcategory
  with predicate `∀ V, (F.obj V).IsQuasicoherent`, using exactly Mathlib's predicate.
  The auxiliary iterated-slice instances transport the existing chart instances along
  `W.iteratedSliceEquiv`; they introduce no hypothesis and have real construction data.
- A chart arrow f: `f : W ⟶ V`. Its transition is
  `F.transition f : (X.etalePullbackMap f).obj (F.obj V) ≅ F.obj W`.
  `etalePullbackMap` is the dependency's `SheafOfModules.overMap`, not an arbitrary
  map, tensor model or selected equivalence.
- Identity and cocycle laws: fields `identity` and `composition` in
  `CartesianModuleChartFamily`. They are equations on every section on every object
  of the localized site, hence equality of module maps. The identity source is
  identified by `(Over.mapId V).inv.app A`; the composite source is identified by
  `(Over.mapComp g f).inv.app A`. Their underlying scheme maps are identities and
  their arrow types carry exactly the canonical identity/composition reindexing.
  In categorical order the right side first restricts c_f and then applies c_g.
- A family map: `CartesianModuleChartFamily.Hom.app V` is an actual linear sheaf map.
  Its `comm f` is `(F.transition f).hom ≫ app W =
  (X.etalePullbackMap f).map (app V) ≫ (G.transition f).hom`, exactly h_W c_f^F =
  c_f^G f^*h_V. The category composes these maps componentwise.
- Canonical restriction: `moduleChartRestriction` has object V equal to
  `(X.etalePullback V).obj M` and map V equal to `(X.etalePullback V).map h`.
  Its transition is `moduleChartTransition`, defined as the actual component of
  `SheafOfModules.overFunctorMap` at M. This is the canonical identification of
  direct and repeated restriction and is sectionwise the identity. The named theorems
  `moduleChartRestriction_identity` and `_composition` supply precisely the
  normalization proof fields, not any data or arbitrary isomorphism.
- Quasi-coherent restriction: `chartRestriction_isQuasicoherent` supplies the proof
  that these specified chart modules are quasi-coherent, by transporting the same
  local presentations on identical slices (node proof step 1). This makes
  `qcChartRestriction` a genuine functor to the stated full subcategory.
- The equivalence assertion is `X.qcChartRestriction.IsEquivalence` for that exact
  functor. Its essential surjectivity gives a global quasi-coherent M and an
  isomorphism of families from its restrictions to each supplied F_V. An isomorphism
  in the family category includes all transition compatibilities through `Hom.comm`.
  Its full faithfulness gives existence and uniqueness of the global map for every
  compatible family of maps. Thus both of the statement's “in particular” clauses
  are included, with their actual maps; no bare equivalence between unspecified
  categories replaces the prescribed functor.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleTopology`, `structureSheaf`, `Modules`, `etalePullback`,
  `etalePullbackMap`; full signatures and construction bodies were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`,
  `etaleModuleOverHasWeakSheafify`, `etaleModuleOverWEqualsLocallyBijective`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`; this is used through `X.Modules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent`, `isQuasicoherent`, `QuasicoherentData`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `overFunctor`, `overMap`, `overFunctorMap` (their exact section formulas were read).
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  imported as the recorded proof dependency, while the sheaf axiom in the proof
  uses the existing Mathlib sheaf condition, as its dependency record specifies.
- `def-weil-size-convention` is explicitly recorded as a metatheoretic convention,
  with no module or declaration to import.

Sources read: the full 03LY and 03LZ statements/proofs in spaces-properties.tex,
Mathlib's module sheaf/morphism and local presentation definitions, and the current
blueprint's direct-image stability proof at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
The reconstruction proof in the docstring follows all seven node steps: evaluate at
terminal charts, verify semilinearity and functor laws, identify local presheaves,
glue sections, inherit local presentations, descend compatible maps, and check both
quasi-inverse identifications and uniqueness of maps.

Edge cases checked: X or a chart may be empty; zero modules and zero maps are allowed;
empty covering families are handled by the sheaf condition and explicitly mentioned
in the proof plan; no finite presentation or index nonemptiness is assumed. Identity
arrows and composable identity arrows use the same canonical comparisons. Arbitrary
site charts and module maps are retained. The definition uses the full site, without
an affine-only restriction or a choice of atlas. Isomorphisms rather than equalities
of reconstructed global modules are asserted, as appropriate.

Searches for reuse (all successful search calls; no exact declaration found):

- msearch LeanFinder: “Quasi coherent sheaves reconstructed from cartesian families
  on etale slice sites”: 8 hits, all `SheafOfModules.QuasicoherentData` fields,
  constructors, `IsQuasicoherent` or `isQuasicoherent`; these define local
  presentations, not cartesian families.
- msearch LeanSearch: “Compatible families of quasi coherent sheaves on slice sites
  and their restriction equivalence”: 8 hits, the same quasi-coherent definitions
  and presieve-compatible-family lemmas; no chart module category or equivalence.
- msearch Loogle: `"IsQuasicoherent", "Equivalence"`: 0 hits.
- msearch grep: `(cartesian|Cartesian).*(famil|Famil)|(famil|Famil).*(cartesian|Cartesian)`
  in `Algebra/Category/ModuleCat`: 0 hits.
- rg of Mathlib module sheaves and the project `lean/WeilConjectures`, `lean/Sheaf`,
  plus `dag/lean_names_upstream.json`: no chosen declaration name. Existing
  `CartesianChart*` modules concern cohomological base-change diagrams, and
  curve-moduli cartesian families concern geometric families, not module sheaves.
  The integral-closure and Fitting-ideal modules merely cite this item in proof
  docstrings. Searching this item id in `lean/WeilConjectures` found no declaration.
- DAG rg and `tools/blueprint_refs.py search 'cartesian families'`: the latter
  returns only `lem-pc-fpqc-descent`, whose families are on a fixed scheme covering.
  The DAG groupoid module-descent and QCoh groupoid-equivalence nodes concern a fixed
  presentation, not this all-chart definition. No existing definition node is duplicated.

All compiles use the prescribed `scompile.py`; all authored files are in the worker
sandbox. Initial whole-map heterogeneous equalities were replaced by equivalent
sectionwise equations to avoid elaboration costs; the resulting definition keeps
both canonical reindexings explicit. No timeout limit was raised.

## New nodes

`def-sfb-space-cartesian-chart-family` defines the actual category of cartesian
module chart families, their compatible maps, its full quasi-coherent subcategory,
and chart evaluation. It owns
`Sheaf.AlgebraicGeometry.AlgebraicSpaceCartesianChartFamily`. Its source is Tags
03LY/03LZ with the localized-site interpretation already specified by the algebraic
space dependency. The search calls and their results are recorded above and in
`mathlib_searches`; none supplies this notion. The supplied iterated-slice
sheafification instances are constructions from the existing chart instances via
Mathlib's canonical iterated-slice equivalence, not new mathematical hypotheses or
postponed theorems. The item adds this definition node to `stmt_deps`; all original
node fields and its natural-language statement are preserved.

Validation status: the new definition module compiled cleanly (26.3 seconds in its
private overlay and 22.0 seconds in its separate sandbox compile). The latest item
module has not been validated: scompile.py exited 1 with
`resource exhausted (error code: 28, no space left on device)` while compiling it.
An immediate retry of the prescribed wrapper returned the same resource failure.
No compiler/tool script or live file was edited to work around the device failure.

Retry validation (2026-10-24): the required initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push` and a subsequent direct `scompile.py` call supplying both saved modules each exited 1. Both reported successful definition-module compilation and failed at `sandbox Sheaf.Stage2.Sandbox1` with `resource exhausted (error code: 28, no space left on device)`. No Lean diagnostic was produced for the item module. The saved source and node records were retained; no delivery was pushed. This is a compiler-server resource failure, not an exit-124 busy-server timeout.

Dispatcher retry 3 (2026-10-24): inspected this saved report and retained both modules.
The required initial `deliver2.py --no-push` again exited 1 with error code 28 at
`sandbox Sheaf.Stage2.Sandbox1`. A direct `scompile.py` retry supplying both modules
returned the same failure, after reporting successful definition-module compilation.
There was no new Lean diagnostic to repair. The packet remains intact and unpushed;
no launcher script, live source, or server artifact was modified.

Dispatcher retry 4 (2026-10-24): inspected the saved report and ran the required
initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`.
It exited 1 with `resource exhausted (error code: 28, no space left on device)`
at `sandbox Sheaf.Stage2.Sandbox1`. Retried `scompile.py` directly with both saved
modules; it exited 1 with the same resource failure at the same item module,
after successful definition-module compilation. No new Lean diagnostic was
produced. Retained the packet without changing the Lean or node records; no
delivery was pushed and no launcher script or live source was modified.

Dispatcher retry 5 (2026-10-24): inspected the retained report and ran the required
initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`.
It exited 1 with `resource exhausted (error code: 28, no space left on device)`
at `sandbox Sheaf.Stage2.Sandbox1`. A direct `scompile.py` retry supplying both
saved modules exited 1 with the same resource failure at the same item module,
after reporting successful definition-module compilation. No new Lean diagnostic
was produced. The saved Lean sources and node records are retained unchanged;
nothing was pushed. No launcher script, live source, or server artifact was edited.

Dispatcher retry 6 (2026-10-24): inspected the saved report and ran the required
initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`.
It exited 1 with `resource exhausted (error code: 28, no space left on device)`
at `sandbox Sheaf.Stage2.Sandbox1`. A direct `scompile.py` retry supplying both
saved modules also exited 1 with exactly the same resource failure, after successful
definition-module compilation. No Lean diagnostic was produced for the item module.
The retained Lean sources and node records were not changed, and nothing was pushed.
No launcher script, live source, or server artifact was modified.

Dispatcher retry 7 (2026-10-24): inspected the saved report and retained the packet.
The required initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`
exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules exited 1 with the same
resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. No Lean source, node record,
launcher script, live file or server artifact was changed; nothing was pushed.

Dispatcher retry 8 (2026-10-24): inspected the retained report and ran the required
initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`.
It exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules also exited 1 with the
same resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. The Lean sources and node
records remain unchanged; nothing was pushed. No launcher script, live file or
server artifact was modified.

Dispatcher retry 9 (2026-10-24): inspected the saved report and retained the packet.
The required initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`
exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules exited 1 with the same
resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. The Lean sources and node
records remain unchanged; nothing was pushed. No launcher script, live file or
server artifact was modified.

Dispatcher retry 10 (2026-10-24): inspected the saved report and retained the packet.
The required initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`
exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules exited 1 with the same
resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. The Lean sources and node
records remain unchanged; nothing was pushed. No launcher script, live file or
server artifact was modified.

Dispatcher retry 11 (2026-10-24): inspected the saved report and retained the packet.
The required initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`
exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules exited 1 with the same
resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. The Lean sources and node
records remain unchanged; nothing was pushed. No launcher script, live file or
server artifact was modified.

Dispatcher retry 12 (2026-10-24): inspected the saved report and retained the packet.
The required initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`
exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules exited 1 with the same
resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. The Lean sources and node
records remain unchanged; nothing was pushed. No launcher script, live file or
server artifact was modified.

Dispatcher retry 13 (2026-10-24): inspected the retained report and ran the required
initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`.
It exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules exited 1 with the same
resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. The saved Lean sources and
node records remain unchanged; nothing was pushed. No launcher script, live file
or server artifact was modified.

Dispatcher retry 14 (2026-10-24): inspected the retained report and ran the required
initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`.
It exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules exited 1 with the same
resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. The saved Lean sources and
node records remain unchanged; nothing was pushed. No launcher script, live file
or server artifact was modified.

Dispatcher retry 15 (2026-10-24): inspected the retained report and ran the required
initial `deliver2.py NO lem-sfb-space-qcoh-cartesian-chart-family --no-push`.
It exited 1 at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry supplying both saved modules exited 1 with the same
resource failure, after reporting successful definition-module compilation.
No Lean diagnostic was produced for the item module. The saved Lean sources and
node records remain unchanged; nothing was pushed. No launcher script, live file
or server artifact was modified.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
