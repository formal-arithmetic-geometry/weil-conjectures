## Worker report

The module Sheaf.AlgebraicGeometry.LogMonoidalAssociatedPoints states
AlgebraicGeometry.logMonoidal_associatedPoints, with its single proof `sorry`.
Four real helper definitions unpack notions explicitly introduced by this node:
FineSaturatedLogScheme.fanPoints, FineSaturatedLogScheme.monoidalIdeal,
FineSaturatedLogScheme.monoidalQuotient, SaturatedLogBlowupTower.toBase.
There are no additional postponed theorems or repaired dependency modules.
One new definition node records the existing rank-locus declaration; the characteristic-space
helpers are owned by Q95’s landed def-per-log-fan-chart-tower.
See “New nodes” below. No declaration is moved or duplicated.

Source read: ILO, Travaux de Gabber, Exposé VIII printed pp.112–113,
3.4.11 and Lemma 3.4.13, extracted from PDF pages 118–119. The statement uses
only the saturated case specified in the DAG. The fan is the generic-point set
of the log strata, and its Zariski characteristic sheaf is the one in 3.4.11.

Hypotheses and clauses, with the node and source open:

- The fs log scheme is `X : FineSaturatedLogScheme.{u}`; that structure includes
  `IsLocallyNoetherian X.scheme`. `[IsNoetherian X.scheme]` adds precisely
  quasi-compactness and makes X Noetherian. Mathlib's class is locally Noetherian
  plus CompactSpace, equivalent to the node's finite affine Noetherian cover.
- Log regularity is `hX : X.IsLogRegular`, the recorded geometric-stalk stratum
  regularity and dimension formula. No excellence, field, characteristic,
  separatedness or Zariski-origin hypothesis is added to (i)–(iii).
- `fanPoints` uses the EXISTING
  `SimultaneousCohenRigidification.rankLocus X.logStructure n` and requires the
  rank-locus subtype point to be `IsGenericPoint` of its `connectedComponent`.
  Genericity is in the rank-locus subspace, not the ambient scheme. Quantifying
  `n : ℕ∞` introduces no extra rank case for fs monoids, whose ranks are finite.
- For (i), `I : X.logStructure.IdealFamily` and
  `hI : X.logStructure.IsNonemptyCoherentIdeal I` express exactly the nonempty
  coherent log ideal. `monoidalIdeal` is the first witness of
  `coherentLogIdeal_chart_construction X I hI`. That witness is specified by
  all its geometric-stalk ideals, each the span of structural images of I.
  Such a quasi-coherent ideal is unique: strict-local faithful flatness detects
  equality of affine ideals. This is the permitted selection of an object
  determined up to equality, with no arbitrary blowup selected. The theorem is
  already a recorded DAG theorem, not an extra helper theorem introduced here.
- `monoidalQuotient` is `cokernel (X.monoidalIdeal I hI).toModulesι`, literally
  O_X/J in the module category. `Scheme.Modules.associatedPoints` uses maximal
  ideals equal to nonzero-element annihilators on ordinary module stalks.
  In a local nonzero ring the annihilator being its proper maximal ideal forces
  the element to be nonzero; this is exactly the node's annihilation criterion.
- The first conjunct is the subset of `X.fanPoints`. Its second conjunct is the
  parenthesized implication from the nonempty support of J (the vanishing locus
  V(J), not the support of J as a module) to nonempty associated points.
- For (ii), all Y, b and I are quantified, with exactly `IsSaturatedLogBlowup b I`.
  The conclusion `Y.fanPoints ⊆ b.base ⁻¹' X.fanPoints` states fan preservation.
  It does not assume log regularity or Noetherianity of Y separately.
- For (iii), every `SaturatedLogBlowupTower T` with `h : T.level 0 = X` and every
  center index `i : Fin T.length` is quantified. `toBase` recursively composes
  precisely the arrows of T, starting with the identity. Composing it with
  `eqToHom (congrArg FineSaturatedLogScheme.scheme h)` expresses the actual map
  to X. The image of the associated points of the center quotient is contained
  in `X.fanPoints`. Coherence comes from `(T.isBlowup i).1`, not an extra assumption.
- Étale locality is explicit: for every strict étale f into X, fan points pull
  back as sets, the pulled-back log ideal is coherent, and its quotient associated
  points are exactly the inverse image of the original associated points.
- For a Zariski log structure only, `X.fanPoints.Finite` is asserted. The witness
  `F : FineFan.Fan` has a sheafed-space map e to X's existing sharpSpace whose base
  is an embedding with image exactly fanPoints, and whose characteristic stalk maps
  are bijective. This precisely identifies the topology as the induced topology
  and the monoid sheaf as the restriction of the characteristic sheaf, rather than
  merely choosing an unrelated fan on the same cardinality of points. A stalkwise
  bijective map of sheaves on an embedding identifies the source sheaf with its
  inverse-image restriction.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup:
  EtaleLogStructure, FineSaturatedLogScheme, FineSaturatedLogScheme.IsLogRegular,
  EtaleLogStructure.characteristicRank, EtaleLogStructure.IsNonemptyCoherentIdeal,
  IsSaturatedLogBlowup, SaturatedLogBlowupTower (including their full definitions).
- Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian and IsNoetherian.
- Sheaf.AlgebraicGeometry.FineFanBlowup: FineFan.Fan, FineFan.stalkMap,
  FineFan.Chart and its monoid-spectrum local-model definition.
- Sheaf.AlgebraicGeometry.RelativeAssassin: Scheme.Modules.associatedPoints;
  WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes:
  RingTheory.annihilatorAssociatedPrimes (underlying annihilator definition).
- Sheaf.AlgebraicGeometry.SimultaneousCohenRigidificationLift:
  SimultaneousCohenRigidification.rankLocus (existing rank locus, reused verbatim),
  now recorded by def-per-log-characteristic-rank-locus. No theorem conclusion
  of lem-per-simultaneous-cohen-rigidification-lift is used.
- Sheaf.AlgebraicGeometry.LogFanChartBlowup: EtaleLogStructure.IsZariski,
  EtaleLogStructure.sharpSpace, now recorded by
  def-per-log-fan-chart-tower. No theorem conclusion of
  lem-trf-log-fan-chart-blowup is used.
- Sheaf.AlgebraicGeometry.FSStrictLogMorphism: EtaleLogHom.IsStrict,
  cited through def-per-strict-log-morphism, with its actual induced
  CharacteristicRelation graph, not an arbitrary characteristic isomorphism.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: AlgebraicGeometry.Etale,
  cited through def-weil-etale-morphism (same affine-local ring-map class).
- Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction:
  coherentLogIdeal_chart_construction, whose full ideal-stalk characterization is
  used to choose the uniquely specified algebraization.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module:
  Scheme.IdealSheafData.toModulesι; Mathlib's categorical cokernel forms the quotient.
  The definition dependency def-sbc-closed-immersion-ideal-sheaf records the
  kernel ideal sheaf, including its toModules presentation in lean.note;
  toModulesι is exactly its kernel inclusion. This module is now a direct public import.

Every available recorded proof-dependency module is imported with plain import
unless it is already public for the statement; the module docstring reproduces the
node's ten-step proof with its dependency ids. Unstated proof prerequisites are
lem-per-log-rank-strata-local-model, lem-sfb-scheme-etale-assassin-invariance,
lem-per-completed-monomial-transverse-parameter, lem-sfb-affine-associated-points-primes.
The Mathlib proof leaves are imported from their recorded mathlib_match modules:
Mathlib.RingTheory.AdicCompletion.LocalRing (the local-completion instance and
maximalIdeal_eq_map), Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
(biUnion_associatedPrimes_eq_zero_divisors), Mathlib.LinearAlgebra.FreeModule.PID
(Submodule.basisOfPid). No independent theorem is invented or deferred by this delivery.

Edge cases checked mathematically before writing: the empty scheme has empty fan
and no associated points; nonempty V(J) is then impossible. A unit center gives
J=O_X and zero quotient, so containment and conditional nonemptiness hold. A tower
of length zero has no center indices and its level-zero map is identity. A trivial
log structure gives the generic points of the connected components of a regular
scheme. Arbitrary characteristic is admitted. An empty strict étale source makes
the inverse-image assertions empty. Non-Zariski log structures are covered by (i)–(iii)
and locality; the final actual-fan assertion is explicitly conditional on Zariski
origin, as the source's Remark 3.4.12 requires.

Searches made:

- msearch.py leanfinder: “Associated points of monoidal ideal quotients on a log
  regular scheme belong to the Kato fan preserved by saturated log blowups”.
  Eight ideal-sheaf/subscheme/affine hits, none states this log-geometric theorem.
- msearch.py loogle: “associatedPrimes, IsLocallyNoetherian”. The service reports
  unknown identifier IsLocallyNoetherian (unqualified); the qualified local
  declaration was read directly. No match.
- msearch.py grep: `log.?strat|log.?regular|monoidal.*ideal`. Six hits in monoid
  algebra ideals, polynomial ideals and cartesian-closed sites; none matches.
- rg in lean/WeilConjectures and lean/Sheaf for the item id: no declaration.
  Searches for logFan/fanPoints/canonicalFan, characteristic ranks, rankLocus,
  monoidalIdeal and monoidalQuotient found the existing rankLocus, associatedPoints,
  sharpSpace and ideal-inclusion APIs listed above; no duplicate main statement.
- rg in Mathlib and dag/lean_names_upstream.json for the new full helper names:
  no hits for newly introduced names. The return identified missing definition-node
  ownership of three already existing helpers. The new existing:true rank-locus record
  below and Q95’s landed def-per-log-fan-chart-tower supply the definition owners.

The previous ending was a stage-1 unchanged-item rejection. Current queue row says
stage 2 and the current reviewed item has no lean field. This delivery adds the
stage-2 record and preserves the reviewed mathematical statement, proof and split.
The only other field changed is stmt_deps. The repaired dependency list contains
the new rank-locus definition and landed def-per-log-fan-chart-tower instead of
the two former theorem-owner nodes,
keeps lem-trf-coherent-log-ideal-chart-construction as expressly accepted, and adds
the strict-log, etale-morphism and kernel-ideal-sheaf definitions.

Validation: scompile.py compiled the revised file as both sandbox and actual module,
2.1 seconds each, with no errors or warnings. Module mode, public statement imports,
explicit universes and binders, and no file-local notation or instances are used.


## Repair of return on 99d25b02dfbb

H12/H4: removed the proposed def-per-zariski-log-characteristic-space node from
this packet and replaced its entry in the item's stmt_deps by the already landed
Q95 definition def-per-log-fan-chart-tower. Read the full landed definition node:
its lean.declarations owns logOpenEtale, EtaleLogStructure.zariskiPresheaf,
sharpSpace, sharpSection and IsZariski, as well as the fan-chart/tower definitions.
Thus every characteristic-space helper used by the item has that existing owner.
Q95's node and provider module are not copied or modified.

The accepted def-per-log-characteristic-rank-locus node is retained byte for byte.
The Lean file is unchanged from returned head 99d25b02dfbb, including all three
public imports accepted in that return. Its theorem signature still matches the
record verbatim. The already accepted strict-log, etale-morphism and kernel
ideal-sheaf dependencies are retained. The genuine theorem statement dependency
lem-trf-coherent-log-ideal-chart-construction is retained: it uniquely pins the
constructed monoidalIdeal by geometric-stalk ideals, as both returns accept.
There is still one sorry, the whole named theorem proof, and no new Lean module.

Compared with the current main node, only lean and stmt_deps differ; its
natural-language statement, proof, proof_deps and all other fields are preserved.
The delivery wrapper rebases this packet on the current server main. This repair
changes the returned packet by dropping the duplicate node, replacing its
statement dependency, and updating this report and lean.note. No declaration is
moved or duplicated and no mathematical statement or definition changes.

## New nodes

`def-per-log-characteristic-rank-locus` defines the set of ordinary points whose
geometric characteristic groups have a specified rational rank, with the subspace
topology. Source: ILO VI 1.2,1.5, VIII 3.4.11 and VIII 5.5.2. It records
AlgebraicGeometry.SimultaneousCohenRigidification.rankLocus in the existing
Sheaf.AlgebraicGeometry.SimultaneousCohenRigidificationLift module. Read its full
signature and body: all algebraically closed fields and all lifts over x are
quantified. Empty schemes, empty rank loci, rank zero and infinity are allowed;
fs characteristic groups have finite ranks. Searches: LeanSearch on “rank locus
of characteristic monoid of an etale logarithmic structure” gives etaleLocus and
module rankAtStalk results; LeanFinder on “constant rank locus of characteristic
group completion logarithmic monoid sheaf” gives module-rank/structure-sheaf
results. Mathlib grep has zero rankLocus/sharpSpace/IsZariski hits. Project rg
finds the exact existing rankLocus; parsed DAG definition records and blueprint
search find no definition owner. The new node stores the raw search outputs.
The matching theorem node only listed the helper; it did not own this standalone
definition as a definition node. No duplicate declaration is written.


Repair validation: scompile.py passed for the unchanged module (sandbox 5.3 s,
library 3.8 s), with no errors or unexpected warnings.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
