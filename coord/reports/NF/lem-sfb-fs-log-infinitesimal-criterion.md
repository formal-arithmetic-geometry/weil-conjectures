## Worker report

This stage-2 packet states `AlgebraicGeometry.EtaleLogHom.infinitesimal_criterion` in
`Sheaf.AlgebraicGeometry.FSLogInfinitesimalCriterion`, with one `sorry` and no proved
results. Both equivalences are conjuncts of the one theorem. The item's statement,
proof, proof dependencies, and existing statement dependencies are unchanged. Its
statement dependencies gain the new definition node described below.

The retained retry diagnosis confused stages: the live node's `reviewed` record is
NI's stage-1 split review, while its `lean` and `reviewed_lean` records are absent.
NI's report says explicitly that its attachment count is zero. Thus there is no
reviewed stage-2 result being restated and no re-split in this delivery.

I read the item, its twelve proof steps, all nine statement dependency records, and
their recorded Lean interfaces. I read ILO X Proposition 1.2 and proof, printed
pp.136--139. I also obtained the scanned Kato primary source from the item's URL
and read printed pp.200--202 (PDF pages 11--13) visually: 3.1 defines the exact
closed immersion by the isomorphism from the associated pullback log structure;
3.2 uses its square-zero ideal; 3.3 adds underlying local finite presentation and
uses etale-local existence versus one unique global lift. Theorem 3.5 and Remark
3.6 supply the chart characterization, with the smooth-comparison variant for log
smoothness. This agrees with the node. The PDF and page images are scratch files
in the sandbox and are not part of the delivery.

Hypothesis and clause correspondence:

- The locally Noetherian fs endpoints are the explicit binders
  `{X Y : FineSaturatedLogScheme.{u}}`. This reuses the recorded structure with its
  scheme, locally Noetherian proof, etale monoid log sheaf and fs charts. The
  morphism is `(f : EtaleLogHom X Y)`, including its structural compatibility.
- The chart notions are exactly `f.IsLogSmooth` and `f.IsLogEtale` from
  `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`. No infinitesimal definition replaces
  either chart definition, and the entire cokernel remains in the etale version.
- The underlying scheme map is `f.base`. Each right side has exactly
  `LocallyOfFinitePresentation f.base`; it is not assumed as an external binder.
- The general log morphism `f.toLogMap` retains the actual scheme map and all the
  section maps of `f`, through the existing `EtaleLogHom.toLogMap`.
- Arbitrary fine test schemes are quantified as `(T₀ T : Scheme.{u})` and
  `(L₀ : EtaleLogStructure T₀) (L : EtaleLogStructure T)` with
  `L₀.IsFine → L.IsFine → ...`. The existing `IsFine` requires etale-local
  finitely generated integral charts. These binders impose neither local
  Noetherianness nor saturation. In particular the bundled `FineLogScheme`, whose
  definition imposes local Noetherianness, is deliberately not used for tests.
- A test immersion is `(i : EtaleLogMap L₀ L)` with
  `IsFirstOrderThickening i.base` and `i.IsStrict`. The first predicate is the
  recorded upstream closed immersion with `i.base.ker ^ 2 = ⊥`; it includes the
  zero ideal and is not restricted to affine or Noetherian thickenings.
- The strictness predicate is a test of the actual associated inverse-image log
  structure. At each geometric point it uses a homomorphism `φ` from the target
  log stalk to the source log stalk, with its values fixed by every relative
  pointed etale section diagram of `i`. This fixes `φ` uniquely; there is no
  arbitrary map in the statement. `N.IsStalkChart t φ` then says that the product
  map with the source ring units is surjective and its kernel is exactly
  `divisorialChartCongruence` for `β = N.stalkAlpha t ∘ φ`. Those are precisely
  the relations `(me,u) ~ (m,β(e)u)` in the node. The associated presheaf quotient
  is the existing actual congruence quotient; inverse image and sheafification
  have these stalks, and geometric stalks detect an isomorphism. Thus this is the
  canonical pullback-log isomorphism condition, not the assertion that the two
  original log sheaves or their sections are isomorphic. In particular a strict
  square-zero immersion may quotient its units by `1 + I`.
- The maps `a` and `b` are general `EtaleLogMap` values. The hypothesis
  `a.CompositesEq f i b` fixes equality of both the scheme maps and the log maps.
  It uses a common composite with the existing `CompEq` twice. Every composite
  exists canonically, so this common-composite presentation adds no condition.
- Etale-local existence is
  `f.toLogMap.HasEtaleLocalInfinitesimalLifts`. For each point `t : T` it provides
  `V : T.Etale` with `t ∈ Set.range V.hom`. Taking these neighbourhoods gives a
  jointly surjective family; conversely any such family supplies the pointwise
  witness. There is no finiteness, nonemptiness or independent size restriction
  on this family.
- The local log structure `L'` and map `v` satisfy `v.base = V.hom` and the
  existing `v.IsStrictEtale`. This identifies the prescribed pulled-back log
  structure, with its actual structural map. It is automatically fine because
  it is a strict etale restriction of the fine structure `L`.
- The reduction scheme is literally `pullback i.base V.hom`, with the recorded
  `pullback.fst` and `pullback.snd`. Its log structure `L₀'` has a strict etale
  map `v₀` to `(T₀,L₀)` with base the first projection. The map `j` to `(V,L')`
  has base the second projection and satisfies `j.CompositesEq v v₀ i`.
  Since `v` is strict, that commuting equation determines precisely the
  induced reduction log map; it cannot be an arbitrary replacement for it.
- The local lift is `c : EtaleLogMap L' M`. Its equations are
  `c.CompositesEq f v b` and `j.CompositesEq c v₀ a`, rendering `fc = bv`
  and restriction to `a pr_T₀`, respectively.
- Unique global lifting is `f.toLogMap.HasUniqueInfinitesimalLifts`, with the
  same universally quantified test squares, followed by
  `∃! c : EtaleLogMap L M, c.CompEq f b ∧ i.CompEq c a`. Uniqueness is of the
  whole log morphism, including its scheme map and section maps; there is no
  locality qualification on this conclusion.
- The final conjunction contains both complete iff statements. No direction,
  finite-presentation conjunct, existence clause or uniqueness clause is omitted.

Dependency declarations reused:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `EtalePrelogStructure.stalk`, `germ`, `stalkAlpha`, `EtaleLogStructure`,
  `EtaleLogStructure.unitsIn`, `IsStalkChart`, `IsChart`,
  `FineSaturatedLogScheme`, `EtaleLogHom`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`:
  `FSLogChart`, its smooth/etale predicates, `EtaleLogHom.IsLogSmooth`,
  `EtaleLogHom.IsLogEtale`.
- `Sheaf.AlgebraicGeometry.LogIdealChartPresentation`:
  `EtaleLogMap`, `EtaleLogMap.CompEq`, `EtaleLogMap.IsStrictEtale`,
  `EtaleLogHom.toLogMap`.
- `Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum`:
  `EtaleLogStructure.IsFine` (already publicly imported by the preceding module).
- `WeilConjectures.AlgebraicGeometry.Thickening`:
  `AlgebraicGeometry.IsFirstOrderThickening`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
  `AlgebraicGeometry.Etale`, `Scheme.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `Scheme.smallEtaleTopology`, the existing monoid sheaf's site.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar` (inverse image) and
  `Mathlib.CategoryTheory.Sites.Sheafification`:
  `CategoryTheory.presheafToSheaf`, `toSheafify` (sheafification).
  The strictness condition uses their stalkwise quotient description, so it
  does not need to choose a globally associated log structure or assume extra
  sheafification instances in the theorem.

The modules of the already-stated proof dependencies are imported privately in the
item module. The five newly split sfb calculus/lattice/logification inputs have no
Lean declaration on the base; their imports will be supplied after they are stated.
Their content is not axiomatized privately here. Every one of the twelve proof
steps and its non-elementary inputs appears in the theorem docstring.

Edge cases checked before writing:

- Empty schemes: the pointwise local-cover condition permits the empty cover.
  The global version still asserts uniqueness of the morphism from the empty
  log scheme. The chart definitions themselves permit empty sources.
- Identity tests and the zero square-zero ideal: the equations force the original
  lift; no nonzero-ideal, positive-codimension or proper-immersion hypothesis is
  present. Strictness uses the unit pushout even for a noninjective unit map.
- Trivial logs reduce the conditions to ordinary smooth/etale lifting. The affine
  line has local existence but fails uniqueness; it is not made log etale.
- The rank-one chart `0 → ℕ` has a free cokernel and may be log smooth without
  being log etale. Multiplication by `m` on a Kummer chart requires invertibility
  of `m`; in residue characteristic dividing `m` the lifting obstruction remains.
  These checks use the imported chart definitions without changing their group
  conditions.
- Nonsaturated integral chart monoids, for example the submonoid of nonnegative
  integers generated by 2 and 3, are allowed by `IsFine` on tests. Non-Noetherian
  rings with square-zero ideals are also allowed by the `Scheme` binders.
- All schemes, monoid coefficients and geometric fields share the explicit
  universe `u` of the recorded log framework. No independent smaller test
  universe or finite bound on covering indices makes the lifting condition vacuous.

Searches actually run with `msearch.py` (logged in `searches.jsonl`):

- LeanFinder: "A morphism of fine saturated logarithmic schemes is log smooth or
  log etale if and only if it is locally of finite presentation and has the
  infinitesimal lifting property for strict square zero thickenings of fine log
  schemes". Eight ordinary smooth/etale hits; no logarithmic criterion.
- Loogle: "AlgebraicGeometry.EtaleLogHom, AlgebraicGeometry.FineLogScheme".
  No hits; the service does not know the project's `EtaleLogHom` identifier.
- LeanSearch: "Pullback logarithmic structures and strict morphisms of log schemes;
  fine log schemes without Noetherian hypothesis". Eight ordinary pullback or
  module-pullback hits, no logarithmic strictness or lifting predicates.
- LeanFinder: "Strict logarithmic maps and infinitesimal lifting conditions for
  arbitrary fine logarithmic schemes". Eight ordinary scheme-morphism hits.
- Mathlib grep: `LogScheme|LogStructure|log.?smooth|log.?etale` in
  `AlgebraicGeometry`, zero hits. Full-Mathlib grep for
  `LogMap|LogStructure|InfinitesimalLifts` found number-field logarithmic maps,
  unrelated to logarithmic structures on schemes.
- `rg` of the upstream `WeilConjectures` sources for the item tag and log
  structures found no declaration. Searches of `lean/Sheaf` found the general
  log maps, general fine predicate and strict-etale predicate reused above.
  The fs-only `EtaleLogHom.IsStrict` in `LogFanChartBlowup` is restricted to
  locally Noetherian fs endpoints and cannot type the arbitrary fine tests.
- DAG searches found `def-per-strict-log-morphism`, whose Lean record is that
  same fs-only predicate; it supplies no general strict test immersion or
  logarithmic lifting condition. Blueprint searches for "strict log",
  "infinitesimal log" and "log infinitesimal lifting" each returned zero.

Both delivered files were compiled separately, in dependency order, by
`scompile.py` against the live server library and the private sibling overlay.
They compile without errors or non-sorry warnings. No live file, launcher script,
git state or compiled library was edited directly. No statement fault or dispute
was found. No dependency interface repair is needed.

## New nodes

`def-sfb-log-infinitesimal-lifting-properties` records general strict log maps,
equality of two log composites, and the two lifting predicates for arbitrary fine
strict square-zero test squares. Its module is
`Sheaf.AlgebraicGeometry.LogInfinitesimalLifting`, with four actual Prop-valued
definitions and no `sorry`. Its source is Kato 1.3--1.4 and 3.1--3.3, the primary
source referenced by ILO X 1.2. It reuses `EtaleLogMap`, `IsFine`, `IsStalkChart`,
strict-etale pullback and the actual scheme fibre product. The source, DAG,
blueprint and Mathlib searches above rule out an existing definition of these
general lifting predicates. Existing fs strictness and locally Noetherian fine
log schemes do not cover these arbitrary tests. The new node's statement cites
all its definition dependencies, and the item cites this new node. Its inherited
blueprint ancestor is null, exactly as `blueprint_refs.py ancestor` reports for
the item; its `via` records the item followed by the item's existing provenance.

## Second reading by NF

No second worker was started: the dispatcher brief prohibits delegation and
requires direct delivery. The maintainer's independent review reads this packet.
