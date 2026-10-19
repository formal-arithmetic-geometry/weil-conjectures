## Worker report

The item is stated by `AlgebraicGeometry.exists_polarizedFineLog_of_etaleDescent` in
`Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent`. Its only postponed proof is this
named theorem, whose docstring carries all eight proof steps of the DAG node. No other
theorem, axiom, chosen existence object or postponed definition is introduced. The node's
natural-language statement, source, proof, proof_deps and status are unchanged.

Clause-by-clause reading:

- The base `(S,M)` is `S : FineLogScheme.{u}`: `S.scheme`, `S.logStructure`, `S.fine`
  and `S.locallyNoetherian` are the underlying scheme, the actual étale monoid log sheaf,
  étale-local finitely generated integral charts, and the locally Noetherian convention
  inherited from `def-trf-fs-log-blowup` / ILO VI 1.1. There is no saturation hypothesis.
- The covering is `I : Type v`, `U`, `uMap`, with `D.isEtale` and
  `D.jointlySurjective`. This is precisely the arbitrary jointly surjective family in
  the node, not a finite cover or a single surjective morphism.
- The `U_i` have the pulled-back base log structures. Rather than choose second copies
  of these canonical log structures, `E.localMap i` is the map from `E.localLog i` to
  `S.logStructure` over `f i ≫ uMap i`. A map to a strict base change is exactly a map
  to the original log base with this prescribed scheme factorization. Thus the data
  specify log maps `X_i → U_i` and do not assume those maps strict or saturated.
- `X`, `f`, `E.localLog`, `E.fine` and `E.locallyNoetherian` give all the fine log
  schemes over the `U_i`, with no finite-type, properness or separatedness assumption.
- `D.theta`, `D.theta_over_left`, `D.theta_over_right`, `D.theta_identity` and
  `D.theta_cocycle` are the specified scheme isomorphisms over the double base overlap
  and their identity and triple-overlap conditions. The second overlap is written in
  its reversed-index form as in the recorded polarized scheme interface.
- `E.logTheta` supplies the log part of those same isomorphisms. On the relation
  `R_ij = polarizedOverlap ... i j`, let `p_i` and `q_j = theta_ij ≫ p_j` be its two
  maps to the local schemes. Its sections are tested on `a:T → R_ij`, with `p=a≫p_i`
  and `q=a≫q_j` étale; `hp` and `hq` retain exactly these equalities. Both relation
  projections are étale because they are base changes of the base-cover maps (and one
  is composed with an isomorphism). Consequently these tests are precisely the small
  étale site of the relation, by cancellation of étaleness, and include its identity
  object. `logTheta` is a monoid equivalence on each test, `naturality` commutes with
  every restriction, and `alpha` commutes with the actual regular functions on `T`.
  These are genuine isomorphisms of the canonical restricted log structures.
- `E.identity` tests `a=p≫polarizedOverlapDiagonal` and gives the identity equivalence,
  including repeated indices. `E.cocycle` compares all three transitions on a common
  étale test of the triple relation. The two base-projection equalities ensure that
  `a,b,c` really have the same three base coordinates; no equality is required for
  unrelated pairs. Thus it gives exactly the specified triple-overlap cocycle.
- `E.overBase` compares the two maps from the base log sheaf to each relation test,
  through `localMap i` and `localMap j`. This makes theta a log isomorphism over the
  strict base overlap, rather than an isomorphism forgetting the map from `M_S`.
- `L` and `hL` are the invertible modules on the underlying local schemes. `D.lambda`,
  `D.lambda_identity` and `D.lambda_cocycle` are the specified line-module comparisons,
  normalized by the recorded tensor-pullback composition and identity isomorphisms.
- `D.ample_local` says, for every affine open `V` of `U_i`, that the tensor restriction
  of `L_i` to `(f i ⁻¹ᵁ V).toScheme` is `Scheme.Modules.IsAmple`. This is exactly the
  affine-open formulation of relative ampleness in the node, including quasi-compactness
  in the recorded absolute predicate. No global ampleness condition is substituted.
- The conclusion `∃ d : PolarizedFineLogRealization E` gives `d.pair.Y`, `d.pair.g`,
  `d.logStructure`, `d.fine`, `d.locallyNoetherian`, `d.map`, `d.pair.M` and
  `d.pair.isInvertible`. The scheme/module charts are `d.pair.chart`; `d.realizes`
  forces them to induce exactly `D.theta` and `D.lambda`.
- `d.chartMap` and `d.strict` identify each local log structure with the restriction
  of the global one. The underlying chart is the inverse of `d.pair.chart i` followed
  by the canonical fibre-product projection, so it is exactly `X_i → X`. A strict
  étale map over a scheme chart is an isomorphism to its log base change.
  `d.overBase` forces the local maps to the log base to be the specified ones, and
  `d.transition` forces the induced log overlap maps to be exactly `E.logTheta`.
- The fs clause is `(∀ i, (E.localLog i).IsFineSaturated) →
  d.logStructure.IsFineSaturated`, with no fs assumption on the base or on the theorem.
- Unique compatible isomorphism is `∃ e : PolarizedFineLogRealizationIso d d',
  ∀ e', e'=e` for every other realization. `e.pairIso` includes a single global scheme
  isomorphism over `S`, a single global line-module isomorphism, and their labelled
  chart compatibilities. `e.logMap` is a log map over this scheme isomorphism;
  `e.strict` makes it invertible, and `e.overBase` and `e.chart` impose compatibility
  with the log base and every local log chart. No unlabelled uniqueness is asserted.
- The final assertion is the independent conjunction
  `FineLogMorphismsAreStrictEtaleLocal.{u,w} S`. Its quantifiers range over all fine
  `T,Z`, log structure maps `t,z` to `S`, every `A : Type w`, and every strict étale
  jointly surjective cover `q` of `T`. `g` gives the local log maps and
  `(g a).CompositesEq z (q a) t` says that each is over `S`.
- Agreement on `T_a ×_T T_b` is stated by all fine-log cones `r:R → T_a`,
  `s:R → T_b` with equal composites to `T`, requiring equal composites to `Z`.
  This is exactly overlap agreement: the canonical strict fibre product is itself a
  fine, locally Noetherian log scheme in universe `u`, so its projection cone is one
  test; conversely every such cone factors uniquely through it. No cone or action
  is arbitrary or unconstrained: `CompositesEq` includes the scheme equation and
  all relative-section equations. This formulation avoids introducing a second
  canonical log pullback construction solely to state this clause.
- Finally `∃! h : T.Hom Z, h.CompEq z t ∧ ∀ a, (q a).CompEq h (g a)` is exactly
  existence and uniqueness of the log `S`-morphism restricting to all given maps.
  This final assertion is outside the quantifiers of the polarization datum, so
  its availability does not depend on furnishing any polarized descent datum.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtalePrelogStructure`,
  `EtaleLogStructure`, `EtaleLogStructure.IsChart`, `IsFineSaturated`, and the original
  relative-test presentation of `EtaleLogHom`. The new definition module
  `Sheaf.AlgebraicGeometry.FineLogSchemeMorphisms` imports that original module and
  supplies `EtaleLogStructure.HomAlong`, `.CompEq` and `.IsStrictEtale` without the
  old fs-only bundled domain restriction.
- `Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum`:
  `EtaleLogStructure.IsFine`, the exact finitely generated/integral chart predicate.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.Etale`, `Scheme.ofArrows_mem_smallEtaleTopology_iff`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` and their universal property, as used by the recorded
  polarized overlap and chart constructions.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`; `WeilConjectures.AlgebraicGeometry.Ample`:
  `Scheme.Modules.IsAmple`, used through the actual recorded scheme descent datum.
- `Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent`:
  `PolarizedSchemeEtaleDescentDatum`, `PolarizedDescentPair`,
  `IsPolarizedDescentRealization`, `PolarizedDescentPairIso`, `polarizedOverlap`,
  `polarizedOverlapX`, `polarizedOverlapUi`, `polarizedOverlapUj`,
  `polarizedOverlapDiagonal`, `polarizedChartMap`. Their signatures and docstrings
  were read in full. The new `def-trf-polarized-scheme-etale-descent-datum` node owns these already
  landed definitions with `existing: true`; the theorem node is absent from stmt_deps.
  No theorem witness or `.choose` from polarized effective descent is used here.
- Proof imports follow the current DAG: `FineLogEtaleDescent`
  (`fineLogStructure_etale_descent`), `EtaleLocalNoetherianDescent`
  (`isLocallyNoetherian_of_etale_cover`), `FpqcFinerThanEtale`
  (`Scheme.fpqcCover_of_smallEtaleCover`), `Mathlib.AlgebraicGeometry.Sites.Fpqc`
  (`Scheme.instSubcanonicalFpqcTopology`) and `Sites.MorphismProperty`
  (jointly surjective precoverage base change). The polarized scheme theorem is
  available in its public interface module already imported for its definitions.

Edge cases checked against the statement and definitions: empty cover index is allowed
and forces an empty base by joint surjectivity; empty schemes and empty local members
are retained. The source-cover locality clause also permits an empty cover of an empty
source. Repeated indices retain nontrivial off-diagonal overlaps while the diagonal
condition is only on the actual diagonal. Fine integral nonsaturated monoids are allowed;
for example the additive submonoid generated by 2 and 3 is not silently made saturated.
Trivial log structures and identity charts give ordinary polarized scheme descent.
Strictness is required on the source covering and realization charts, not on the
arbitrary morphisms `X_i → U_i` or `T → Z`. There is no extra nonempty-index, properness,
characteristic, finite-type or global-chart assumption. Index universes `v,w` are free;
all test schemes, monoid coefficients and geometric points use the original site
universe `u`, preserving the dependency's object/morphism universe convention.

Searches made with the prescribed wrapper: LeanFinder, "effective etale descent fine
log schemes compatible polarization" (8 unrelated étale morphism/site hits); Loogle,
"EtaleLogStructure, PolarizedSchemeEtaleDescentDatum" (no identifier/match);
LeanSearch, "Fine logarithmic schemes with morphisms descend effectively under strict
etale covers with compatible ample invertible sheaves" (8 scheme-morphism descent hits);
grep, "LogStructure|FineLogScheme|Polarized.*Descent", Mathlib/AlgebraicGeometry
(no hit). Direct rg searches of the source library and lean/Sheaf found the existing fs
structures, fine-log sheaf descent and polarized scheme descent, all reused, but no
combined theorem or general fine-log scheme bundle. The item-id source search had no
hit. `blueprint_refs.py search 'fine log'` found no blueprint node; DAG searches found
`def-trf-fine-log-etale-descent-datum` and the fs node, reused here. Further searches for
the new bundle are recorded verbatim in its mathlib_searches (LeanSearch, LeanFinder,
Mathlib grep, and source/side/DAG grep). No exact duplicate was found.

Source checks: read ILO VI 1.1 (PDF p.75, printed p.69) for fine/fs and the locally
Noetherian convention; VIII 3.3.4(ii) and 3.3.8 (PDF pp.113--114, printed pp.107--108)
for strict charts and the descent sentence; Stacks spaces-descent.tex 0D3C and 04W8,
and spaces.tex 02WW, for the polarization route. No statement correction and no
STATEMENT-DISPUTED finding.

Repair validation: both retained modules compiled separately in dependency order through
scompile.py, including sandbox and library module-name checks, with no errors or warnings
(3.2 s for FineLogSchemeMorphisms and 3.6 s for PolarizedFineLogEtaleDescent). All variables
and universes are explicitly bound and `autoImplicit` is disabled. Only the item's theorem
has a `sorry`; all definition data are fully written. Delivery preflight results follow below.

## New nodes

`def-trf-fine-log-scheme-morphisms` packages a fine (not necessarily saturated), locally
Noetherian log scheme and its morphisms using the existing `IsFine` predicate and the
general `HomAlong` interface owned in the same module. It defines composite and two-composite equality
by the existing relative-test prescription, and the ordinary étale section/restriction
helpers. Source: ILO VI 1.1 and VIII 3.3.4(ii), 3.3.8. The exact bundle was absent in the
DAG, Mathlib, source and side library; LeanSearch and LeanFinder returned scheme and
étale notions only, and Mathlib grep found no log bundle. The original fs bundle cannot
represent the nonsaturated objects in this statement. This module uses the recorded
fine-chart predicate and original log structures; its three general-map helpers extend
the fs-only map interface without copying any previously usable definition.

`def-trf-polarized-scheme-etale-descent-datum` records the existing definition interface
in `Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent` with `existing: true` and no
new Lean file. It owns the polarized covering datum, overlap/projection/diagonal maps,
normalized tensor comparisons, candidate pairs, realization predicate and compatible
pair isomorphisms. Sources are the descent-datum and effective-datum definitions in
Stacks spaces-descent.tex, Tag 0D3C, spaces.tex Tag 02WW and Descent Tag 023Q.
The definitions are already present exactly as required, so no copy is made. Fresh
LeanSearch returned ordinary Scheme.GlueData and etale-site declarations; LeanFinder
returned ordinary scheme gluing/affine-limit declarations; Mathlib grep returned no
matches. Source rg returned no hits, side-library rg found the existing module, and
DAG rg found only the theorem's record (no definition owner). The blueprint search
returned no polarized node. All search outputs are recorded verbatim in the node.

## Returned delivery repairs

F1 (H13/H4): removed the sandbox copy of `def-trf-fs-log-blowup`, leaving Q49's
landed reviewed `FineSaturatedLogBlowup` record untouched. Removed
`GeneralLogMorphisms.lean`. Moved precisely `EtaleLogStructure.HomAlong`,
`EtaleLogStructure.HomAlong.CompEq` and `EtaleLogStructure.HomAlong.IsStrictEtale`
into `FineLogSchemeMorphisms.lean`, registered all three in the existing new
`def-trf-fine-log-scheme-morphisms` record, and assigned their blueprint docstrings
to that owning node. Their signatures and data are unchanged. This module now
imports the original `FineSaturatedLogBlowup` directly. No original fs declaration
or importer is rebound or orphaned.

F2 (H2): replaced the added `lem-trf-polarized-scheme-etale-descent` statement
dependency by `def-trf-polarized-scheme-etale-descent-datum`. The latter is an
`existing: true` definition node on the unchanged landed module, listing its full
definition interface but excluding the existence theorem. This changes neither
the Lean statement nor any mathematical hypothesis. The theorem stays in the
item's unchanged proof plan; the public import supplies both its definition
interface and its use as a later proof dependency.

## Second reading by Q80

Author's self-check against the open node, both retained files and the reused module; no second worker was
started, as the dispatch brief prohibits delegation. The maintainer supplies the
independent review. Checked each of the correspondences above, with particular attention
to log base compatibility in `overBase`, normalization of `identity`/`cocycle`, agreement
on the actual triple relation, the single global line isomorphism in `pairIso`, and
fine rather than fs input. During this reading the final morphism assertion was moved
outside the polarization-data quantifiers, ensuring the last clause is unconditional
for every fine base. On the repair reading, checked the exact three moved declarations against the
new fine-log node, including arbitrary nonsaturated endpoints, composable-test
equations and bijectivity on isomorphic tests. The original fs record remains
untouched. Read all definitions of the unchanged polarized scheme module again:
cover/scheme cocycle, line identity/cocycle and affine-local ampleness are in the
datum; candidate pairs retain both scheme and line charts; realization pins both
transitions; pair isomorphisms retain one global module isomorphism. The new
definition owner lists those definitions, while the item imports the same names
and no descent witness is chosen. No mathematical signature, natural-language
statement, proof plan or target changed.
