## Worker report

The delivery states `AlgebraicGeometry.characteristicZero_log_resolution_independence`
in `Sheaf.AlgebraicGeometry.CharacteristicZeroLogResolutionIndependence`. Its proof is
`sorry`; the docstring contains the entire reviewed eleven-step natural-language proof,
with every dependency named. The item's statement, proof, source, proof dependencies,
status and reviewed split are unchanged. Only `lean` and added statement dependencies
are delivered. Q129's reviewed stage-1 split is preserved; the old stage-1 superseded
ending is not applicable to this queued stage-2 assignment.

Three definition modules and one existing-definition attachment supply missing notions,
using actual previously published
blowups, monoid ideals, sharpening, log structures and comparison maps. There are no
new axioms, unspecified constructions chosen from existence theorems, or proof work.
Definitions contain their data in full. Published provider modules are reused unchanged;
no dependency module repair is delivered.

Clause-by-clause correspondence:

| Node clause or hypothesis | Lean rendering |
| --- | --- |
| Existence of one normalized desingularization algorithm | First conjunct `Nonempty (RegularFunctorialNormalizedResolution.{u})`. |
| All reduced Noetherian quasi-excellent schemes over Q | `QERationalResolutionInput.scheme`, `.reduced`, `.noetherian`, `.quasiExcellent`, `.structureMap`; the base is `Spec (.of (ULift.{u} ℚ))`. No finite-type, dimension, integrality or separation restriction. |
| Finite ordinary blowup followed by normalization; actual defining ideals | `NormalizedResolutionOver.length`, `.tower`, using existing `Monoscheme.NormalizedTower` and `IsNormalizedBlowup`. The latter is the prescribed componentwise normalization of the ordinary blowup, with affine finite-generation condition and isomorphism over the base. |
| Regular last scheme | `NormalizedResolutionOver.regularLast`, via existing `NormalizedTower.IsDesingularization` and `IsRegularScheme`. |
| Regular morphisms, flat with geometrically regular fibers | `IsRegularResolutionMap f := ∀ y, RingHom.IsRegular (f.stalkMap y).hom`; the existing ring predicate is flatness and geometric regularity of every fiber. This is the local characterization of the scheme condition, without finite presentation. |
| Source is contracted target pullback with extended ordered ideals | `.comparison`, `RegularNormalizedPullback.centers`, `.commutes`, `.cartesian`, and existing `NormalizedContraction`, with the specified base equations. |
| Delete unit-center isomorphisms; identity and composition | `NormalizedContraction.deleted`, `.deletedMap`, `.keptMap`, `.keptCenter`; the rule's `identityIndex`, `identityMap`, `compositionIndex`, `compositionMap` retain maps as well as indices. |
| Fix any such algorithm | The second conjunct quantifies over **every** `F : RegularFunctorialNormalizedResolution`; it asserts existence of an induced datum and independence for **every** such datum `D`. The final independence is not a hypothesis on the datum. |
| Restriction to rational toric realizations and descent of invariant centers | `D.realizes` and `ToricResolutionIdentification`: all toric models of each monoscheme input, bijective ordered indices, canonical monomial realization arrows, and the actual `Monoscheme.ringIdeal` centers. Thus the descended centers are monomial-generated; arbitrary ideals with the same supports cannot substitute. No new toric realization is defined. |
| Sharpen to a smooth-functorial fan resolution | `D.monoschemeRule`, `D.fanRule`, and the existing `Monoscheme.RuleSharpens` in `D.sharpens`. This comparison includes the actual tower identification and naturality of both indices and maps. Fine torsion-free fans with finite covers are the existing `FineFan.ResolutionInput`. |
| Finite saturated fan blowups, nonempty coherent centers, smooth last fan | The existing `FineFan.Resolution.tower`, its blowup properties and `.smooth`; `D.properFanCenters` excludes the whole sheaf. Its existing rule includes every smooth morphism and identity/composition laws. Open localizations, isomorphisms and component inclusions have smooth rank-zero stalk maps. |
| Induced finite saturated log tower on every Noetherian fs log regular scheme | `D.logRule` has domain `IsNoetherianLogRegularInput X := IsNoetherian X.scheme ∧ X.IsLogRegular`. The bundled `FineSaturatedLogScheme` already includes fs and local Noetherianity. There is no excellence or separation condition on this domain. |
| Characteristic group completions are torsion free | `D.torsionFree` gives the existing `IsLogBlowupInput` condition on every domain member, as a property, not an additional theorem hypothesis. |
| Local pullback of the fan rule, contraction, and strict etale gluing | `D.onCharts` uses every global fan chart and a `LogFanTower` of the actual fan resolution. `LogBlowupComparison` over a log map satisfying `IsIdentity` identifies its contraction with the global procedure. The procedure supplies all strict etale pullback comparisons and identity/composition laws. This global rule, characterized on every chart, is precisely the descended rule, not an unrelated tower supplied as a hypothesis. |
| No whole-log-structure center | `D.properLogCenters`; existing comparisons delete exactly whole-monoid centers. |
| Underlying tower centers are alpha(I) O and have nonempty zero locus | `D.underlying`, `UnderlyingNormalizedLogResolution.generated`, `IsRingIdealOfLogCenter` test equality of the actual ring ideals on every geometric strict-local stalk. `.nonempty` records nonempty zero loci. `.toResolution` keeps the exact log tower's scheme levels, arrows and generated centers. |
| V and W Noetherian separated fs log regular | `V W : FineSaturatedLogScheme`, `hV hW : IsNoetherianLogRegularInput`, and the two `scheme.IsSeparated` hypotheses. |
| Any underlying scheme isomorphism, without log compatibility | `φ : W.scheme ≅ V.scheme`. No log map over φ is assumed. |
| Every generic point of every log stratum has characteristic zero | `HasCharacteristicZeroLogStrata V` and `... W`: every natural-number rank, every point in its constant-rank locus, genericity in its connected component, then `CharZero (scheme.residueField x.1)`. The rank is the existing rational rank of the geometric characteristic group, not a Zariski stalk rank. |
| Equality identifying every stage and defining ideal in original order | `.IsIsoOver` requires equality of the two lengths, then the existing `NormalizedTower.CenterIso` at that common length, and its base map is φ. `CenterIso.commutes` and `.centers` preserve all arrows and actual ideals. There is no contraction, reordering or radical replacement in this conclusion. |
| Finite disjoint unions, including empty schemes | Every rational, fan and log input is in the corresponding rule's domain, including disconnected and empty inputs. Comparisons apply to every component inclusion. The comparison conclusion is made on the complete towers, never on independently contracted components. No nonemptiness assumption appears. |
| No quasi-excellence of V or W | Only the separate rational algorithm input has `.quasiExcellent`. Neither `hV`, `hW`, either characteristic hypothesis nor φ adds excellence. |

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule`: the existing
  `AlgebraicGeometry.QERationalResolutionInput` (reused after the latest return).
  Its quasi-excellence field is `GabberModification.QuasiExcellent scheme`,
  definitionally the same affine-local predicate as in the removed duplicate.

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`; it reuses
  `WeilConjectures.RingTheory.GRing`'s `RingHom.IsRegular` and geometric-regularity predicate.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization`,
  `Scheme.fromNormalization` on integral schemes. Disconnected normalization is handled by
  the already recorded `Monoscheme.IsNormalizedBlowup` construction, not by imposing integrality.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: `Fine`, `Hom`, `realization`,
  `realizationToBase`, `ringIdeal`, `IsRealizationMap`, `NormalizedTower`,
  `NormalizedContraction`, `NormalizedTower.IsDesingularization`.
- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `ResolutionInput`, `Resolution`,
  `SmoothFunctorialDesingularization`, `Tower`, `wholeIdeal` in namespace `FineFan`.
  `FunctorialFanDesingularization.exists_smoothFunctorialDesingularization` is retained
  as a public statement dependency with its exact signature and proof docstring.
- `Sheaf.TraceFormula.SharpeningFanBijection`: monoscheme `ResolutionInput`, `Resolution`,
  `SmoothFunctorialDesingularization`, `RuleSharpens`, and the unchanged theorem
  `AlgebraicGeometry.sharpening_fan_bijection`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogStructure.characteristicRank`, `IsLogRegular`, `EtaleLogHom`, `idealStalk`,
  `stalkAlpha`, `IsSaturatedLogBlowup`, `SaturatedLogBlowupTower`.
- `Sheaf.AlgebraicGeometry.LogFanChartBlowup`: `LogFanChart`, `pullbackIdeal`,
  `LogFanTower`, and `log_fan_chart_blowup` with its full signature/docstring.
- `Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure`: `IsLogBlowupInput`,
  `LogBlowupTowerOver`, `LogBlowupComparison`, `StrictEtaleLogBlowupProcedure`.
- `Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent`:
  `functorial_log_blowup_etale_descent`, unchanged, including uniqueness and all comparisons.
- `Sheaf.AlgebraicGeometry.NormalizedTowerDescentData`:
  `Monoscheme.NormalizedTower.toFirst`, `CenterIso`; there is no duplicate centered isomorphism.
- `Mathlib.Topology.Sober.IsGenericPoint`, `TopologicalSpace.connectedComponent`, and
  `Mathlib.AlgebraicGeometry.ResidueField.Scheme.residueField` supply the stratum hypothesis.

All stated proof dependencies are imported, with plain imports where used only
by the proof, including the unchanged toric-realization provider. Unstated
proof-dependency nodes have no module to import yet; their full reviewed uses
are retained in the theorem's eleven-step docstring.

Edge cases checked before writing and again against the final definitions:

1. Empty schemes/fans and length-zero towers have one initial level and no centers.
   Every rule's domain includes them. Nonempty center zero loci force length zero on
   an empty scheme. The stratum hypothesis is vacuous on empty rank loci as intended.
2. Finite disconnected inputs use a single rule value with one global ordering; no
   disjoint-component contraction is present in the final synchronized `CenterIso`.
3. Unit centers are deleted only when the normalized stage is an isomorphism. A
   nonnormal input can have a nontrivial unit-center normalization, so the existing
   `NormalizedContraction` is reused without weakening its isomorphism condition.
4. Proper principal ideals are retained even when their blowups are identities.
   The definition never deletes all isomorphisms indiscriminately.
5. Rank zero and mixed characteristic: with trivial log structure the rank-zero locus
   is the whole scheme. Only the generic points of its connected components must have
   characteristic zero; special points may have positive residue characteristic.
6. Strata are not generally closed in the scheme. Genericity is measured in the
   rank locus's subspace topology, avoiding an unintended global-closure condition.
7. The isomorphism may interchange connected components and may carry incompatible
   log structures. Only its underlying scheme map is specified.
8. Non-qe log schemes remain in the conclusion. The resolution algorithm itself is
   only evaluated on its specified qe rational inputs, as in ILO Remark 3.4.16(i).
9. Universes: every universe and variable is explicit; geometric fields have the
   scheme universe, as in the existing log framework; `ULift` retains Q in that universe.
10. Every new definition has real data. No arbitrary canonical map is chosen, and the
    independence conclusion is not hidden inside an input structure.

Searches: prescribed `msearch.py` LeanFinder query “Characteristic zero functorial
resolution of singularities normalized blowup towers independence of log structure” gave
8 normalization-map hits, not the theorem. Loogle on expected normalized-tower and
fan-rule names gave no match; Mathlib grep for desingularization/log_resolution/quasi-
excellence in AlgebraicGeometry gave zero hits. Searches in `WeilConjectures` and `Sheaf`
found the reused normalized/fan/log framework, ordinary finite-type smooth rules and
centered descent data, but no regular-qe normalized rule, induced-rule datum or log-stratum
condition. The exact item identifier is absent from `WeilConjectures`. Additional
LeanSearch/LeanFinder searches for the three missing notions returned ordinary
normalizations, category-theoretic resolutions or unrelated logarithms/Archimedean
strata. Loogle on `logCharacteristicRankLocus` and Mathlib grep on all new principal
names returned zero hits. `blueprint_refs.py search` returned zero matches for “regular
normalized resolution rule”, “induced normalized log resolution” and “log stratum”.
The raw search records and answer digests are included in each new node's
`mathlib_searches`; project/DAG grep and the reused notions are recorded too.

No mathematical statement correction or STATEMENT-DISPUTED finding. The only interface
faults found are the module issues described below. The four delivered modules are checked separately in dependency order via `scompile.py`;
final compile and dry-run results are recorded in the repair section below.

## New nodes

`def-per-regular-normalized-resolution-rule` owns
`Sheaf.AlgebraicGeometry.RegularNormalizedResolutionRule`. It reuses the qe rational input from
`Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule` and defines regular scheme maps through the existing regular local-ring-map predicate,
normalized resolutions, regular pullback and coherent contracted comparisons. Source:
ILO VIII 2.2.3--2.2.8, 2.3.2--2.3.5, 2.3.10--2.3.12. Existing ordinary finite-type
smooth rules and smooth-only `NormalizedPullback` do not supply this interface.
It reuses the existing normalized tower, contraction and actual blowup construction.

`def-per-induced-normalized-log-resolution` owns
`Sheaf.AlgebraicGeometry.InducedNormalizedLogResolution`. It characterizes the induced
monoscheme/fan/log rule by realization of the given algorithm, the existing sharpening
comparison and all fan chart pullbacks. It retains actual generated ring ideals and
constructs the underlying normalized resolution from the log tower's levels and arrows.
It also defines equality over a scheme isomorphism using the existing `CenterIso`.
Source: ILO VIII 3.2.19--3.2.21, 3.3.13--3.3.15, 3.4.3--3.4.9, 3.4.15.
The searches found existing components, all reused, but no datum tying them to an
arbitrary regular-functorial rational algorithm. This definition does not assert
existence or independence; those are exactly the delivered theorem's conclusions.

`def-per-characteristic-zero-log-strata` owns
`Sheaf.AlgebraicGeometry.CharacteristicZeroLogStrata`. It defines the ordinary rank
locus using every geometric characteristic rank and the characteristic-zero condition
at generic points of all connected strata. Source: ILO VIII 3.4.14--3.4.15.
It reuses the log characteristic rank, Mathlib generic points, connected components
and scheme residue fields. No existing node or declaration supplied this condition;
search results and the actual definitions used are recorded in the node.

`def-per-monoscheme-resolution-sharpening-data` records existing definitions in
`Sheaf.TraceFormula.SharpeningFanBijection` with `existing: true`: monoscheme inputs,
resolutions, contracted pullback comparisons, smooth-functorial rules, canonical
sharpened maps and towers, and `Monoscheme.RuleSharpens`. No module is added for it.
Source: ILO VIII 3.1.11 and 3.1.22--3.1.27, printed pp.100--102, reread directly
from the PDF. Its statement defines the data before the theorem asserts the rule
bijection. The existing `Fine.toFan` continues to belong to
`def-trf-monoscheme-toric-realization`; the map, tower and input `toFan` definitions
are attached here. Every signature and body is reused unchanged.

For this ownership node, LeanSearch on “smooth functorial monoscheme resolution rule
sharpening comparison to fan resolution with ordered centers” returned eight ordinary
smooth-scheme-map declarations. LeanFinder on “smooth functorial monoscheme
desingularization and sharpening of blowup towers” returned smooth scheme maps and
normalizations. Mathlib grep `RuleSharpens|ResolutionComparison|sharpSpaceMap|Monoscheme`
in AlgebraicGeometry returned zero hits. Project grep found the exact existing
sharpening definitions and no upstream copies; DAG grep found their previous theorem
attachment but no definition owner. `blueprint_refs.py search 'monoscheme resolution'`
returned zero matches. The new node records these actual search results.

## Repair of returned delivery

1. H2, sharpening ownership: the item and
   `def-per-induced-normalized-log-resolution` now cite the new definition node
   `def-per-monoscheme-resolution-sharpening-data`. The latter's textual citation
   changes to the definition owner too. `lem-trf-sharpening-fan-bijection` is removed
   from statement dependencies and remains in the item's unchanged proof dependencies.
   Its module has an explicit plain proof import; the public import in the induced
   definition module exposes the exact definitions used by its statement.
2. FineMonoidUnitSplitting: drop the stale sharpening provider repair entirely.
   `scompile.py --source Sheaf.TraceFormula.SharpeningFanBijection` and the local live
   source both show module mode and `public import Sheaf.GroupTheory.FineMonoidUnitSplitting`.
   Reusing that provider restores the import that the returned packet dropped.
3. H2, toric realization: remove `lem-trf-toric-realization-finite-type` from the
   item's statement dependencies and drop its node/module repair. It remains in
   the unchanged proof dependencies and as a plain proof import. The live provider,
   including `Sheaf.RingTheory.AffineMonoidAlgebraNormalization`, is reused unchanged.
4. Advisory, no-op republishes: drop the node and module copies for
   `lem-trf-functorial-fan-desingularization`,
   `def-trf-strict-etale-log-blowup-procedure` and
   `lem-trf-functorial-log-blowup-etale-descent`. Their current live sources supply
   these interfaces. No provider file or dependency node is delivered. The extra direct statement
   dependency on the strict etale procedure, added solely for its no-op repair,
   is dropped; the induced-datum definition still cites that procedure.
5. Advisory, duplicate imports: deduplicate the three identical GRing imports in
   `RegularNormalizedResolutionRule` and the repeated ResidueField imports in
   `CharacteristicZeroLogStrata`.

The interrupted-tool check found the initial dry run completed successfully at
`b533d3edf3d` with nothing pushed. That was the saved packet, before these repairs.
The repaired packet preserves the accepted mathematical statement, eleven-step proof,
proof dependencies, reviewed split and all four statement-module signatures. It
changes only dependency ownership, removes provider republishes and duplicate imports,
and adds the existing-definition record requested by the return. The final delivery
wrapper rebases it onto current live main without direct Git commands.

The first repaired compile passed all three definition modules but rejected the
main theorem's module-mode import of the published legacy artifact for
`FunctorialFanDesingularization`, despite its current source having module mode.
The theorem-only consumer now uses an ordinary Lean import header, retaining all
proof imports, so it can consume both published provider formats without any
provider repair or republish. Its declaration, docstring, universe and signature
are unchanged. The three definition modules retain module mode and public exports.

Validation: the final four-file `scompile.py` call returned exit 0. Each module
compiled separately, including its library-name check, with no errors or warnings:
`RegularNormalizedResolutionRule`, `CharacteristicZeroLogStrata`,
`InducedNormalizedLogResolution`, `CharacteristicZeroLogResolutionIndependence`.
Final self-check: the item differs from current live data only in `lean` and the
four new definition-node dependencies. Its mathematical statement and all proof
fields are unchanged. Exactly four Lean modules remain; no live provider module
or existing dependency-node file remains in the packet. Every changed Lean line
is within 100 columns, and the theorem signature still matches its Lean record.

The repaired dry run passed at `31233b4736f` (nothing pushed), including the new
existing-definition probe. The final proof-import audit then found the existing
`def-trf-fine-fan-blowup` provider was visible transitively but lacked its required
direct proof import. That plain import is restored before the final dry run and push.

## Repair of duplicate input declaration (returned head f62ddd5c6f9c)

The single returned fault is repaired by deleting the complete local
`AlgebraicGeometry.QERationalResolutionInput` declaration and importing
`Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule` publicly. The existing declaration
is now the input type used by both `RegularFunctorialNormalizedResolution` and
`ToricResolutionIdentification`; no alias or renamed copy is introduced. Its owning
node `def-per-qe-ordinary-resolution-rule` is cited by the normalized-rule and
induced-datum definition nodes. The normalized-rule node no longer lists the
input among its own `lean.declarations`.

Read the entire current provider through both the local read clone and
`scompile.py --source`. The five fields agree: the scheme universe `u`, map to
`Spec (.of (ULift.{u} ℚ))`, reducedness, Noetherianity and quasi-excellence. The
existing `GabberModification.QuasiExcellent` unfolds to exactly
`∀ U : scheme.affineOpens, IsQuasiExcellent Γ(scheme, U.1)`, so the mathematical
domain is unchanged, including empty and disconnected inputs and schemes that
are not of finite type or separated. No transport, extra assumption or postponed
theorem is needed. The new provider's dependency graph has no path back to this
item or either consumer definition node. Its other declarations are imported and
not copied. The theorem statement, proof plan and all retained signatures stay
unchanged. The previous delivery finished with `DELIVERED` at f62ddd5c6f9; no
interrupted delivery remains to resume or repeat.

Validation for this repair: the four-file `scompile.py` call passed with exit 0,
no errors and no non-sorry warnings. It compiled the existing input provider and
then every delivered file separately under its sandbox and library module names.
The removed input declaration is absent from the normalized-rule module and its
ownership list; the canonical name resolves through its public provider import.

## Repair of distinct log input predicates (returned head c90dc6bd8d39)

The returned collision is real, but the two declarations have different statements.
The existing `AlgebraicGeometry.IsLogRegularResolutionInput` in
`Sheaf.AlgebraicGeometry.StrictLogBlowupProcedure` is
`IsNoetherian X.scheme ∧ X.scheme.IsSeparated ∧ X.IsLogRegular`.
The predicate required by this delivery is
`IsNoetherian X.scheme ∧ X.IsLogRegular`: it defines the construction domain
before separatedness is imposed for the independence conclusion. Substituting
the existing predicate would silently exclude inputs allowed by the node and by
ILO VIII Theorem 3.3.15. Both the current source and `scompile.py --source` confirm
the separation conjunct in the existing declaration. Its owning node
`def-per-strict-log-blowup-procedure` explicitly specifies that separated domain.

Following the return's explicit exception “rename only when the two declarations
say different things”, rename the broader predicate to
`AlgebraicGeometry.IsNoetherianLogRegularInput`, and update all its uses and Lean
records. Its body, universe and mathematical domain are unchanged. The new
name's declaration docstring explains the distinction. The item still requires
separation separately in its conclusion; the induced procedure still has the
broader domain. No definition of the existing separated predicate is copied,
replaced or changed. `rg` of the current project, upstream source and DAG found
no prior `IsNoetherianLogRegularInput` declaration. Source reread: ILO VIII
Theorem 3.3.15, pp.109--110, constructs the induced log rule on monoidally
torsion-free fine log schemes without a separation restriction.

All earlier repairs are retained. The preceding delivery completed successfully
at c90dc6bd8d3, so there is no interrupted delivery mutation to resume. The wrapper
will rebase this packet onto current main. This repair changes only the broad
predicate's name, its references, its declaration documentation and its records;
it does not change any natural-language statement or proof field.

Validation for this repair: `scompile.py` returned exit 0 for all four delivered
modules and a separate, undelivered compatibility probe. That probe imports both
`InducedNormalizedLogResolution` and `StrictLogBlowupProcedure`, checks both names,
and verifies each displayed predicate body by definitional equality. Thus both
notions coexist and remain distinct: the broader input has exactly Noetherianity
and log regularity, and the existing input additionally has separation. No
compiler warnings or errors remain. All delivered Lean lines meet the 100-column
limit; recorded signatures match the files; the item's natural-language statement
and all proof fields remain identical to current main.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
