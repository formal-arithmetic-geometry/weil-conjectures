## Worker report

The delivery states `AlgebraicGeometry.log_tower_effective_center_descent` in
`Sheaf.AlgebraicGeometry.LogTowerEffectiveCenterDescent`. Its only postponed proof is
that theorem, with the node's seven-step proof in its docstring. The same module defines
`LogTowerCenterDescentRealization`, packaging precisely the descent conclusion. The new
node `def-trf-log-tower-center-descent-datum` supplies the missing ordered Čech datum in
`Sheaf.AlgebraicGeometry.LogTowerCenterDescentDatum`; it does not assume effectivity or
choose a descended object. All definitions contain actual data, with no sorry.

Source read: ILO VIII 3.3.7--3.3.10, printed pp.107--108 (PDF pp.113--114), and the
initial 'By descent' assertion in the proof of 3.3.15, printed p.109 (PDF p.115).
The current blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/
sk-i-curve-zero/lem-trf-local-term-locality.md` was also read. This is the historical
log-resolution subargument recorded in the node's existing blueprint ancestry; the
current blueprint unit and its contracting-correspondence route are unchanged.
No statement correction, disputed statement, or dependency repair is needed.

Hypotheses, individually:

* `(X U : FineSaturatedLogScheme.{u})` supplies the two fs log schemes and their local
  Noetherianity, log sheaves, structure maps, and fs-chart conditions.
* `uMap : EtaleLogHom U X` is the specified log morphism, including its actual maps
  on relative étale log sections. `hstrict : uMap.IsStrict`,
  `hetale : Etale uMap.base`, and `hsurjective : Surjective uMap.base` are exactly
  strictness, étaleness, and surjectivity; no quasi-compactness, chart choice, or
  torsion-free hypothesis is imposed.
* `S : LogBlowupTowerOver U` is the finite ordered tower with its specified initial
  identification. Its `tower.center` retains the actual ideals and `tower.isBlowup`
  supplies nonempty coherence and the universal saturated-blowup property at each step.
* `D : LogTowerCenterDescentDatum uMap S` is theta in its equivalent represented
  functor-of-points presentation. For maps `a,b : T → U` with `a.comp uMap = b.comp
  uMap`, `LogTowerPoint S i T a` is the fiber of the represented level over `a`.
  `D.transport` is the bijection from the first such fiber to the second, at the same
  stage `i`. Naturality in every log test map makes these bijections an actual
  isomorphism over the double overlap. `D.arrows` preserves every ordered arrow;
  `D.centers` equates the actual pulled-back ideals. `D.diagonal` and `D.cocycle`
  are respectively the diagonal identity and theta23 theta12 = theta13.
* All universes are explicit. Schemes and log-section monoids have the same bounds
  as the recorded `FineSaturatedLogScheme.{u}` framework; the small étale objects
  live in `Type (u+1)`, with morphisms and sections in the inherited bounds. Testing
  on all locally Noetherian fs `T` includes the representing pullbacks for a strict
  étale cover; no independent smaller test universe is introduced.

Why the datum is the same object, not an additional assumption: a pair `a,b` with
`ua=ub` is precisely a test point of `R=U×_X U`. A point of the first recursive
pullback at level i is precisely a point of `U_i` over a; the analogous statement
holds for b. Thus theta acts by `transport`. Conversely, evaluate a natural transport
on the universal point of the first pullback to recover its log morphism to the
second. The inverse bijections recover the inverse morphism. These representing
pullbacks are locally Noetherian fs, since the overlap projections are strict étale.
The tower-arrow equations and equality of ideal pullbacks recover, respectively,
ordered-tower commutation and equality of centers as actual subsheaves. Applying this
on the universal double and triple overlaps recovers exactly the original diagonal
and cocycle equations. At level zero the fibers are singletons, so the base map is
necessarily the identity over R. There is no chosen arbitrary comparison or extra
representability hypothesis.

Conclusions, individually, in `LogTowerCenterDescentRealization`:

* `B : LogBlowupTowerOver X` gives a finite saturated log blowup tower over X.
  `length : B.tower.length = S.tower.length` states the unchanged length, including
  all repeated levels. The `Fin.cast`s only transport this equality, retaining every
  original index and its order.
* Each `B.tower.level` is already a locally Noetherian fs log scheme. Each
  `B.tower.center` is a nonempty coherent ideal and each arrow is its universal
  saturated blowup by `B.tower.isBlowup`; these clauses are not replaced by arbitrary
  objects or arbitrary maps.
* `map j` is the comparison `U_j → X_j`, and `initial` identifies its base level
  with the specified `uMap`. `cartesian` expresses its log Cartesian property and
  `schemeCartesian` its ordinary scheme Cartesian property. These identify the
  supplied local tower with the full uncontracted pullback of B.
* `strict`, `etale`, and `surjective` give the three required properties of every
  level map. `recursive` gives the Cartesian square for each specified blowup
  arrow. `centers` equates its entire pulled-back log ideal with the specified J.
* `induces` says that theta-related local test points have equal images in the
  descended level. The Cartesian property makes the corresponding point over the
  second base map unique, so this says the pullback isomorphism induces exactly D.
* `overlap` uses the actual scheme `pullback (map j).base (map j).base`, namely
  `U_j×_{X_j}U_j`. Its map r to R is characterized by both projection equations;
  the additional `IsPullback` identifies it with the first overlap pullback
  `U_j×_U R`, or equivalently `R×_X X_j`. This is the stated level-overlap
  identification, compatible with the original projections.
* `sections` is exactly I_i(V) = {m : restriction of m to V×_{X_i}U_i belongs to
  J_i}. Its restriction map is the actual `EtaleLogHom.sectionMap` on the two
  canonical scheme pullback projections, and it quantifies over every small
  étale V and every log section m. The transposed product `U_i×_{X_i}V` is the
  same scheme fiber product, with the named projections in the opposite order.
* `B.tower.isBlowup` includes `IsNonemptyCoherentIdeal`, hence `IsIdeal`: these
  are ideal subsheaves, including étale restriction, multiplication stability,
  and sheaf-local membership. `centers` is equality of the entire restricted
  ideal with J_i. `uniqueIdeal` quantifies over every other ideal subsheaf K
  with that restriction and concludes K = I_i.
* The very same nonempty finite local generators work for the restriction because
  `centers` identifies the entire ideal families, not just their isomorphism
  classes. In particular its equality under `idealStalk` identifies both sides
  of the generator equality in the definition of `IsNonemptyCoherentIdeal`, for
  every original chart, monoid, finite nonempty E, and geometric point. This
  requested clause is included by actual equality and needs no extra generators
  or global-section descent assumption.
* `proper` says that if every J_i is proper, every I_i is proper. In the recorded
  tower convention, this says precisely that B is contracted. Whole-center
  stages are otherwise allowed, and proper principal centers are never deleted.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`,
  `FineSaturatedLogScheme`, `EtaleLogHom`, `IdealFamily`, `IsIdeal`,
  `IsNonemptyCoherentIdeal`, `pullbackIdeal`, `IsSaturatedLogBlowup`,
  `SaturatedLogBlowupTower`. Full signatures and docstrings were read.
* `Sheaf.AlgebraicGeometry.LogFanChartBlowup` (and its public
  `FSStrictLogMorphism` import): `EtaleLogHom.IsStrict`, `IsIdentity`,
  `Square`, `IsFSPullback`, `AreInverses`; the fan-chart theorem was also read.
* `Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure`: `LogBlowupTowerOver`,
  `LogBlowupComparison`, `LogBlowupTowerIso`. The latter two describe contracted
  comparisons and same-base ordered isomorphisms; they do not themselves supply
  the missing uncontracted Čech datum, so neither is copied or misused here.
* `Sheaf.AlgebraicGeometry.StrictLogBlowupProcedure`: the existing
  `LogBlowupTowerOver.toBase`, with its actual recursive arrow composition.
* `Sheaf.AlgebraicGeometry.LogMorphismOperations`: the existing
  `EtaleLogHom.comp`, constructing section maps via canonical étale pullbacks.
  These last two notions are cited through their existing definition nodes in
  the new definition node; no replacement composite or base map is introduced.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, and the universal property; `Mathlib.CategoryTheory.Sites.Sheaf`:
  `CategoryTheory.Sheaf`, inherited through the log-sheaf and ideal interfaces.
  `def-weil-size-convention` is metatheoretic and has no declaration/module.
* Proof imports: `Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction`
  (`coherentLogIdeal_chart_construction`) and
  `Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent`
  (`isLocallyNoetherian_of_etale_cover`). The current synchronization proof node
  has no Lean record, so it cannot yet contribute a proof import; its use remains
  explicitly named in the proof docstring.

Edge cases checked before and after writing: n=0 has `Fin 0` for centers and arrows,
with one unchanged initial level; the empty base permits positive-length towers of
whole-center identity stages; proper centers on that base force length zero.
The identity cover and a two-copy split cover give the usual identity and cocycle
transport. Whole centers are retained; a proper principal center whose blowup is
an isomorphism is also retained. Disconnected and non-quasi-compact inputs are not
excluded. No field-characteristic or torsion-free assumptions enter this result.

Searches made (raw results also recorded in the new node): LeanFinder, query
'Effective descent of a finite ordered saturated logarithmic blowup tower preserving
its coherent ideal centers along a strict etale cover', returned ordinary scheme
morphism descent/étale-algebra statements only (8 hits). A second LeanFinder query
'An ordered center preserving Cech descent datum on the functor of points of a
logarithmic blowup tower' returned ordinary affine-transition and gluing interfaces
(8 hits), none the log-tower datum. LeanSearch, query 'Cech descent datum for an ordered
logarithmic blowup tower with nonempty coherent monoid ideals', returned abstract
pseudofunctor descent and scheme gluing (8 hits). Those general interfaces do not
supply the represented centered-log-tower notion. Loogle 'IsSaturatedLogBlowup,
LogBlowupTowerIso' returned no hits (the first identifier is not a Mathlib identifier).
The prescribed Mathlib grep 'LogBlowup|SaturatedLog|log.*[Dd]escent' in
AlgebraicGeometry returned zero hits. Project rg searches found the existing tower,
procedure, and log-map operations used here, with no center-descent datum. The
item-id grep in WeilConjectures returned no match. The DAG search located the
present theorem and its synchronization and functorial-descent neighbors, which do
not define the datum. `blueprint_refs.py search 'logarithmic blowup tower'` returned
zero matching nodes. No existing Lean theorem says the item's statement.

Validation: both delivered modules compiled individually, in dependency order, via
`scompile.py Q52 lem-trf-log-tower-effective-center-descent <both files>`, against the
live published library. No errors or warnings. The only sorry is the required
statement proof. A first compile caught a nonexistent Mathlib Surjective module
name; that import was removed because the actual UnderlyingMap module is already
publicly available. No library, tool, target, or source checkout was modified.

## New nodes

`def-trf-log-tower-center-descent-datum` defines `LogTowerPoint` and
`LogTowerCenterDescentDatum` in its own module. It is the ordered natural bijection
of represented fibers, with explicit diagonal, triple-overlap cocycle, arrow, and
actual-ideal equations. Its source is ILO VIII 3.3.7--3.3.10 and the descent assertion
of 3.3.15, pp.107--109. The three required search kinds, project/DAG searches and
blueprint search are recorded in `mathlib_searches` as returned. Existing tower and
log-morphism definitions are reused. The node is directly added to the item's
statement dependencies; all original dependencies and all original mathematical
statement/proof fields are preserved. Its ancestry and chapter/unit are inherited
from the item. It is definition-only, with no postponed proof and no choice of data.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
