## Worker report

The item is stated by `AlgebraicGeometry.functorial_log_blowup_etale_descent` in
`Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent`. Its only proof is `sorry`.
The additional definition module `Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure`
provides the missing procedure, contracted comparison, and natural ordered tower-isomorphism
interfaces. All definition data is explicit; there are no postponed helper theorems.
The item's natural statement is unchanged, and its stmt_deps gains the new definition node.

The source was read directly in the ILO PDF (PDF pages 114--116, printed 108--110),
especially VIII 3.3.8 (only whole-monoid centers are deleted), 3.3.9 (saturated towers),
3.3.10 (recursive pullback), 3.3.11 (fs Cartesian compatibility), and the descent and
finite-disjoint-union argument in the proof of 3.3.15. No log regularity, smoothness of
strata, characteristic restriction, or prescribed length bound is imposed.

Clause-by-clause correspondence:

- Quasi-compact locally Noetherian fs log schemes: `FineSaturatedLogScheme` already
  contains `locallyNoetherian` and `fineSaturated`; `IsLogBlowupInput` adds precisely
  `CompactSpace X.scheme` and geometric characteristic group torsion-freeness.
  The latter is the explicit condition `0 < n → g ^ n = 1 → g = 1` for all geometric
  points and all elements of `Algebra.GrothendieckGroup (X.logStructure.characteristic t)`.
- Members admitting a global fan chart: `IsChartedLogBlowupInput X` is admissibility
  and `∃ F, Nonempty (LogFanChart X F)`. The rule is indexed by this property of X,
  with no fan or chosen chart among its arguments, so chart independence is literal.
- A rule assigning finite ordered saturated log blowup towers: the argument
  `T : StrictEtaleLogBlowupProcedure IsChartedLogBlowupInput` has `tower X hX` of
  type `LogBlowupTowerOver X`. This contains the existing `SaturatedLogBlowupTower`
  and its initial identification. The natural Fin indexing orders every stage.
- Nonempty coherent log ideal centers: each existing `tower.isBlowup i` is
  `IsSaturatedLogBlowup (tower.arrow i) (tower.center i)`, whose first conjunct is
  `IsNonemptyCoherentIdeal`. No arbitrary replacement centers are introduced.
- Canonical contracted pullback for every strict étale morphism: `T.comparison hX hY
  f hs he` is a `LogBlowupComparison f ...`; `hs : f.IsStrict` and `he : Etale f.base`
  are precisely the hypotheses. `count`, `retained`, `before`, `after`, `deleted`,
  `first`, and `last` retain the original order with no lost endpoints. `map` and `step`
  display all repeated levels of the recursive uncontracted pullback, with `cartesian`
  in the existing fs universal-property sense and `base : HEq (map 0) f`.
- Recursive blowup of pulled ideals: `centers` requires the retained actual ideal
  to be `EtaleLogHom.pullbackIdeal` of the corresponding original ideal; `keptStep`
  identifies its blowup arrow. Cartesian squares identify the pulled-back blowups.
  `deletedStep` makes every removed arrow a transported log identity. `whole` is an
  equivalence: exactly the pulled ideals `fun _ ↦ Set.univ` are removed. Thus every
  repeated-level arrow is a saturated blowup of its pulled center, including unit
  centers; no arbitrary morphism stands in for the canonical construction.
- Preservation of centers and order: the ordered embeddings and exact `centers`
  clauses above, not merely equality of final spaces or of blowup morphisms.
- Identity and composition: `identityIndex`, `identityMap`, `compositionIndex`, and
  `compositionMap` impose these laws on the count maps and actual log morphisms.
  Log identity and composition use the dependency's section-normalized `IsIdentity`
  and `CompEq`. They quantify over any representatives of the actual identity or
  composite, so no unspecified choice of a log-composition operation is assumed.
- Finite disjoint unions and component inclusions: T is assigned on EVERY charted
  admissible log scheme. A finite union of charted admissible inputs is again such
  an input (componentwise fan chart, quasi-compactness, local Noetherianity and stalks).
  Its component inclusions are strict étale and are included in `comparison` and all
  its laws. There is one finite ordered union tower, not independently ordered towers
  on its components. The new interface does not assume a common bound for all inputs.
- Extension to all indicated inputs: `∃ E : StrictEtaleLogBlowupProcedure
  IsLogBlowupInput` supplies the global finite towers and all the same compatibility
  laws. `Nonempty (LogBlowupProcedureAgreement T E (fun _ h ↦ h.1))` identifies its
  restriction with T, preserving order, actual centers, and every comparison map.
- Unique up to canonical isomorphisms of contracted towers with centers: for every
  other extension E' with an agreement on the charted domain, the conclusion gives
  `Nonempty (Unique (LogBlowupProcedureAgreement E E' (fun _ h ↦ h)))`.
  `LogBlowupTowerIso` has ordered level/stage equivalences, forward/backward log maps,
  actual inverse identities, the identity on the base, commuting arrows, and exact
  pulled-center equality. `LogBlowupProcedureAgreement` adds `indexNaturality` and
  `mapNaturality` for every strict étale comparison. Identity comparisons force each
  procedure tower to be contracted, so no normalization hypothesis is added here.
- Contracted pullback on each chart neighborhood: the second conjunct explicitly
  supplies `Nonempty (LogBlowupComparison f (E.tower X hX) (T.tower Y hY))` for each
  charted admissible Y and strict étale `f : EtaleLogHom Y X`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogStructure.characteristic`, `EtaleLogStructure.IdealFamily`,
  `EtaleLogStructure.IsNonemptyCoherentIdeal`, `EtaleLogHom`, `EtaleLogHom.CompEq`,
  `EtaleLogHom.pullbackIdeal`, `IsSaturatedLogBlowup`, `SaturatedLogBlowupTower`.
- `Sheaf.AlgebraicGeometry.LogFanChartBlowup`: `LogFanChart`, `EtaleLogHom.IsStrict`,
  `EtaleLogHom.IsFSPullback`, `EtaleLogHom.Square`, `EtaleLogHom.IsIdentity`,
  `EtaleLogHom.AreInverses`, and the local/finite-cover theorem `log_fan_chart_blowup`.
  Its full signature and docstrings were read, including the current source returned
  by `scompile.py --source Sheaf.AlgebraicGeometry.LogFanChartBlowup`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; its affine-open
  definition and documented equivalence to the affine-cover definition were read.
  This hypothesis is already a field of the dependency's fs log scheme.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` for the underlying morphisms.
- The added module imports the recorded chart module, which in turn imports the
  recorded fs-log-blowup module and Mathlib Noetherian. The item imports the added
  module. Available proof modules `FiniteCoproductLfpQcqs`,
  `CoherentLogIdealChartConstruction`, `SetSheafCoverDescent`, and upstream `EtaleOver`
  are imported for the docstring's proof plan. Other Mathlib proof inputs are already
  available transitively. The upstream derived-category size-convention declaration
  is unrelated to the statement's objects and is not imported merely to impose a
  derived-category instance or a second universe convention.

Edge cases checked before and after writing:

- A length-zero tower has one level and no centers. All stage-indexed clauses then
  quantify over `Fin 0`; count endpoints and the base map remain meaningful.
- The empty scheme is allowed. Its whole monoid ideal is the only ideal, so identity
  compatibility forces the prescribed contracted tower to have length zero. No
  `Nonempty` assumption on the input scheme or covering family is imposed.
- Proper principal ideals remain, even if their blowups are isomorphisms: `whole`
  checks equality to the whole monoid sheaf, never `IsIso` or local principality.
- Consecutive whole pulled centers repeat the same count index, and every such step
  is a log identity. There is no requirement of strictly increasing counts.
- Disconnected schemes and finite unions use the full domain of T; no chosen chart
  or nonempty-component assumption is present.
- Equality of centers concerns ideals in the actual log sheaf; arbitrary isomorphisms
  of ideals, ordinary scheme blowups, and mere equality of terminal modifications
  would lose data and were not used.
- The only universe is explicitly bound `u`, as in all three dependency interfaces.
  Geometric test fields have the same fixed universe as their schemes, as in the
  existing definitions; no new site-universe equality is imposed.

Searches (all prescribed tools, no exact existing statement or definition found):

- msearch LeanFinder, query “Etale descent of a functorial finite tower of saturated
  logarithmic blowups with coherent ideal centers”: 8 ordinary étale algebra/scheme
  hits (`IsEtale` permanence instances, `Scheme.Etale`, `Algebra.Etale.comp`,
  `RingHom.Etale.ofLocalizationSpan`, `RingHom.Etale.stableUnderComposition`); no match.
- msearch LeanSearch, query “A finite tower of logarithmic blowups has canonical
  contracted pullback along strict etale maps, deleting precisely whole monoid ideals”:
  8 ordinary étale hits, including `Scheme.Etale`, `Scheme.instHasPullbacksEtale`,
  `StandardEtalePair.instFormallyEtaleRing`; no log procedure or descent statement.
- msearch Loogle, `"SaturatedLogBlowupTower"`: 0 hits.
- msearch grep, `LogBlowup|logBlowup|LogScheme` in Mathlib AlgebraicGeometry: 0 hits.
- rg of the item id in upstream WeilConjectures: no match; in lean/Sheaf only the
  monoidal-resolution consumer's proof docstring mentioned this missing statement.
- rg for log towers and contraction in both source trees located the existing log
  tower, fan comparison/contraction, and ordinary resolution comparisons. Their
  signatures were read. Fan comparison is fan-indexed and equal-length; ordinary
  comparison uses ordinary ideal sheaves and ordinary blowups. Neither is this notion.
- rg for every new declaration name in Mathlib, upstream WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json found no match.
- DAG search for contracted log towers and log procedures found the item, its consumer,
  ordinary resolution, and fan blowups, but no independent log procedure definition.
  `blueprint_refs.py search 'contracted log tower'` and `search 'log blowup'`: 0 matches.
- The new definition's separate LeanSearch and LeanFinder searches are recorded with
  complete returned declaration-name lists and queries in its `mathlib_searches`.
  They returned only ordinary étale algebra definitions and no match.

Compilation used only the prescribed `scompile.py` wrapper. Both delivered files
compiled cleanly together, separately in dependency order, with no errors or warnings.
The first attempt diagnosed an upstream legacy non-module import: current
`LogFanChartBlowup` is not a `module` file. Both new files therefore use ordinary import
syntax, which the stage-2 format supports; no upstream or live file was edited.

No STATEMENT-DISPUTED flag, statement correction, or unusable dependency record.

## New nodes

`def-trf-strict-etale-log-blowup-procedure` defines the admissible and globally charted
input classes, a tower over an input using the existing saturated tower, contracted
recursive pullback with actual log centers, functorial identity/composition laws,
ordered isomorphisms with centers and natural agreement on a subdomain. These are the
notions explicitly used in the item's hypothesis and uniqueness conclusion; their
source is ILO VIII 3.3.8--3.3.15. The new node cites the existing fs log and fan-chart
interfaces, records all three search kinds plus DAG/blueprint searches, and contains
no theorem or hollow data. The existing fan and ordinary procedure definitions have
different objects and cannot be reused for this purpose.

## Second reading by Q153

Worker reread of the finished node and both files; the dispatcher supplies the
independent maintainer review after delivery. No additional agent was started.

Checked each item clause against the mapping above, especially what “contracted” and
“with centers” mean. The repeated-level presentation gives a recursive fs pullback,
not an arbitrary tower map. `whole` removes only whole centers, while `centers` and
`keptStep` preserve every proper center even if its blowup is an isomorphism. Identity
and composite comparisons are normalized on log section maps through the dependency
predicates, not just on underlying scheme morphisms. Natural agreement contains both
index and map compatibility. The uniqueness target is unique natural ordered log
isomorphism with centers, rather than equality of chosen models or of procedure data.
The input predicate includes all charted finite disjoint unions, so a single union
ordering is available as required in the proof. No chart datum remains in the input,
so chart independence is not an extra untyped assumption. All original node fields
except lean and the authorized addition to stmt_deps are preserved.

The module-system incompatibility found by the first compile was fixed in the two
new files by using legacy imports compatible with the existing chart module. The
successful two-file compilation then validated the exact finished signatures. No
mathematical mismatch was found in this reread.
