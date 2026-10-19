## Worker report

The delivery states `AlgebraicGeometry.exists_semistable_to_stable_valuation_comparison`
in `Sheaf.TraceFormula.ValuationSemistableDominatesStable`. Its sole theorem proof is
`sorry`; the three supporting definition modules contain actual structures and canonical
pullback maps, with no postponed data or helper theorem. The item statement and proof are
unchanged. Its statement dependencies gain the landed `def-trf-multipointed-curve` and
three definition nodes described below.

I read Temkin's paper at
[Stable modification of relative curves](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf):
§1.2, Corollary 4.4.3(i) on printed p. 31, and the final paragraph of Proposition 4.5.1
on printed p. 33. The local scratch PDF/text are for source inspection only. The
proposition is written for separably closed fraction fields; the item's existing six-step
proof explicitly extends the comparison to arbitrary fraction fields by a faithfully flat
valuation extension and descent. The Lean imposes no separable-closedness restriction.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* `K : Type u` and `[Field K]` give the arbitrary fraction field. `V : ValuationSubring K`
  gives the actual subring inclusion and the alternative `a ∈ V ∨ a⁻¹ ∈ V`. The canonical
  `IsFractionRing V K` instance is provided by Mathlib. The valuation condition at zero
  adds no condition, since every subring contains zero.
* `[Finite (PrimeSpectrum V)]` expresses that there are only finitely many prime ideals.
  They form a chain for a valuation ring. Thus this is exactly finite height in the
  item's explicit finite-chain sense, including height zero. It assumes neither
  discreteness nor Noetherianness.
* `Spec (.of V)` is `S`; the map `Spec.map (CommRingCat.ofHom V.subtype)` has source
  `Spec (.of K)` and is the actual generic-point morphism, with no arbitrary choice of
  generic lift or independent field map.
* `P`, `Pst`, and `P'` are `MultipointedCurve (Spec (.of V))`. The landed structure
  includes both scheme structure maps, their flatness, locally finite presentation,
  quasi-compactness and quasi-separatedness (full finite presentation), pure fibre
  dimensions 1 and 0, and the closed marking immersion. It imposes no separatedness or
  properness over the base and no nonemptiness condition on the marking.
* `hXη : Smooth (pullback.snd P.x ...)` and `hDη : Etale (pullback.snd P.d ...)` are exactly
  smoothness of the generic curve and etaleness of the generic marking over `K`.
* `f : MultipointedCurve.Hom Pst P` and `g : MultipointedCurve.Hom P' P` contain both maps
  over `S` and the commuting marking squares. `hf` states that `f` is a stable
  eta-modification; `hg` states that `g` is an eta-modification and `hsemistable` gives
  semistability of its source. The auxiliary predicates below expand every clause.
* The result gives `h : MultipointedCurve.Hom P' Pst`, hence both an `S`-curve map and an
  `S`-marking map, compatible with the closed immersions. The first two conjuncts are
  `h.curve ≫ f.curve = g.curve` and `h.marking ≫ f.marking = g.marking`, exactly `fh = g`.
* The last two conjuncts explicitly state the generic curve and marking maps of `h`
  as the base changes of `g` followed by the inverses of the base changes of `f`.
  These inverses use precisely `hf.1.generic_curve` and `hf.1.generic_marking`. They are
  canonical inverses of specified isomorphisms, not chosen arbitrary maps.
* Semistability is `MultipointedCurve.IsSemistable`: etale marking, a smooth open
  neighbourhood of each marking point, and a smooth neighbourhood or the existing
  `Orgogozo.IsOrdinaryDoublePoint` at every point of the chosen geometric fibre.
  The latter is a scalar-compatible ring isomorphism from the maximal-ideal-adic
  completion of the stalk to `Orgogozo.nodeRing Ω = Ω[[u,v]]/(uv)`. The variables are
  `Fin 2`, and the completion and power series are Mathlib's exact constructions.
  Testing the implication at nonsmooth points is expressed as the equivalent disjunction
  of smoothness and the node condition. No connectedness assumption is added.
* `Hom.IsEtaModification` records properness of each component, a schematically dense
  isomorphism open for each, and both generic-fibre isomorphisms. Schematic density is
  injectivity of `U.ι.app W` for every open `W`, exactly injectivity of the structure-sheaf
  map. Both corresponding source and target opens are recorded, as in Temkin's
  modification convention. The opens need not be quasi-compact; generic-flatness and
  the specified generic isomorphisms also ensure the source-density clause in the
  present situation. No topological-density substitute is used.
* `Hom.IsStableEtaModification` combines modification, semistability and the absence of
  exceptional components in every chosen geometric fibre. A component isomorphic over
  the algebraic closure to `P¹` is represented by a closed immersion of
  `ProjectiveSpace (ULift (Fin 2)) (Spec Ω)` whose range is an irreducible component,
  commuting with the projections to `Spec Ω`. This is the reduced component scheme,
  rather than its normalization or a topological copy of a projective line. Contraction
  is subsingleton image under the canonical base-changed curve map (the component is
  nonempty). The intersection with the union of marking and nonsmooth points has
  `Set.encard ≤ 2`, which includes finite sets of cardinal 0, 1, 2 and excludes infinite
  sets. No numerical `ncard` convention at infinite sets is used.

Dependency declarations read and used:

* `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`, including
  its full signature, docstring and all fields. Its pure-dimension interface is the
  landed `Scheme.IsPureDimension` from `Sheaf.AlgebraicGeometry.PureDimension`.
* `Sheaf.Paper.OrgogozoInductionData`: `AlgebraicGeometry.Orgogozo.geometricPoint`,
  `IsOrdinaryDoublePoint`, `nodeRing`, and `localScalar`, with their docstrings and full
  signatures. `IsSemistableGeometricCurve` is not used: it adds connectedness and
  reducedness as explicit conditions and is not the multipointed notion here.
* `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `AlgebraicGeometry.ProjectiveSpace`
  and its canonical structure map. Two homogeneous coordinates give the projective line.
* Mathlib dependency signatures/docstrings were read in `Topology.KrullDimension`
  (`topologicalKrullDim`), `AlgebraicGeometry.Properties` (`IsIntegral`),
  `AlgebraicGeometry.Scheme` (`Spec`, `Spec.map`), `Morphisms.FinitePresentation`
  (`LocallyOfFinitePresentation`), `Morphisms.Smooth` (`Smooth`),
  `Morphisms.ClosedImmersion` (`IsClosedImmersion`), `Morphisms.Etale` (`Etale`),
  `Morphisms.Flat` (`Flat`), and `Morphisms.Proper` (`IsProper`). Also read the
  `CategoryTheory.Limits.pullback`/`pullback.map` signatures, the `AdicCompletion`
  compatible-sequence definition, and the `MvPowerSeries` coefficient-family definition.
  `Field` is the dependency's Mathlib match and needs no replacement node.
* `Mathlib.RingTheory.Valuation.ValuationSubring`: `ValuationSubring`, `subtype`, and its
  `IsFractionRing` instance. `CategoryTheory.inv` supplies the canonical inverse.
* Proof imports: `Sheaf.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree`
  (`Scheme.Modules.injective_smul_sections_of_flat`) and
  `Mathlib.AlgebraicGeometry.Sites.Fpqc` (the recorded fpqc subcanonical-topology match).
  The properness/finite-presentation permanence matches are already imported by the
  definition modules. The six other proof nodes have no recorded modules yet; no
  import was invented for them and no downstream theorem was used to define these maps.

Edge cases checked against the definitions: empty marking (every marking condition is
vacuous and its canonical maps are retained), empty fibres, the valuation subring equal
to its field (height zero), nondiscrete valuation rings of finite height, arbitrary
characteristic including two, disconnected curves, nonproper and nonseparated curves,
identity modifications, and generic markings that are etale rather than assumed split.
A cusp is not silently counted as nodal, and a contracted rational component with zero,
one or two special points violates stability; one with at least three does not. The
base, curves and field share the scheme universe `u`, with no extra universe equality
on unrelated sites or coefficients and no small independent test-field universe.

Searches made:

* `msearch.py` LeanFinder, query “A semistable modification of a pointed curve over a
  finite height valuation ring dominates a stable modification”: eight Weierstrass
  minimal-equation/good-reduction results; none is the statement.
* `msearch.py` Loogle, `ValuationSubring`: found the exact valuation subring interface,
  which is used. Loogle `"AlgebraicGeometry.Scheme", "IsProper"` only found the proper
  underlying-map lemma.
* `msearch.py` LeanSearch, “A semistable multipointed curve has nodal geometric fibres
  and an etale marking in the relative smooth locus”: smooth/etale loci and scheme
  properties, no multipointed semistability predicate.
* `msearch.py` LeanFinder, “Proper eta modification of multipointed curves is an
  isomorphism over schematically dense opens and the generic fibre”: properness,
  local isomorphisms and rational-map interfaces; no pair modification.
* `msearch.py` LeanSearch, “Stable modification of a marked nodal curve has no contracted
  projective line component with at most two special points”: base-change permanence
  and elliptic-curve results, no exceptional-component predicate.
* All three new nodes also carry the actual JSON result records of the combined
  LeanSearch, LeanFinder and Mathlib grep searches for “Semistable multipointed curves
  with proper eta modifications and stable modifications excluding contracted projective
  lines with at most two marked or singular points”. The semantic hits concern proper
  morphisms, rational maps and Weierstrass curves; Mathlib grep gives zero hits.
* `rg` of the upstream source, side `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `MultipointedCurve`, `EtaModification`, `IsSemistable`, `IsStableEtaModification`,
  `curveBaseChange`, `markingInclusionBaseChange` and the proposed theorem name found
  the landed multipointed structure and Orgogozo point predicate, but no full statement
  or any of the three new predicates. The upstream item-id search gave no hits.
* DAG statement/title searches for multipointed, eta-modification, semistable, and stable
  modification found the landed multipointed definition and statement nodes repeating
  the conventions, but no definition nodes for the three predicates. The blueprint
  reference searches for multipointed, eta-modification, semistable and stable
  modification found no matching blueprint definition. I checked the full dependency
  closure of the Orgogozo definition (11,132 nodes): it does not reach this item, so
  reuse introduces no dependency cycle.

Validation: `scompile.py` compiled all four delivered files separately in dependency
order in the private overlay and in the library/sandbox checks: exit 0, no warnings or
errors. The only postponed proof is the named main theorem, whose docstring includes
all six DAG proof steps. No statement dispute or correction was necessary.

## New nodes

`def-trf-semistable-multipointed-curve` owns
`Sheaf.TraceFormula.SemistableMultipointedCurve`. It introduces the multipointed
semistability predicate exactly as in Temkin §1.2, reusing `MultipointedCurve`,
`Orgogozo.geometricPoint`, and `Orgogozo.IsOrdinaryDoublePoint`. Existing connected
nodal-fibre predicates would impose additional conditions. The searches above found
no existing declaration or definition node of this notion.

`def-trf-multipointed-eta-modification` owns
`Sheaf.TraceFormula.MultipointedEtaModification`. It gives the morphism-of-pairs
structure, canonical pullback curve/marking maps and marking inclusion, and the
proper generic-modification predicate of Temkin §1.2/§3.1. The predicate takes the
base-change arrow explicitly; its specialization at the actual generic inclusion is
used in the theorem. All maps are constructed with `pullback.map` and the supplied
over-base equations. This is not Orgogozo's modification of a reduced Noetherian base,
which does not encode a multipointed pair and does not have the hypotheses here.
Searches found no pair-modification interface.

`def-trf-stable-multipointed-eta-modification` owns
`Sheaf.TraceFormula.StableMultipointedEtaModification`. It adds precisely the
geometric no-exceptional-component condition of Temkin §1.2 to a semistable generic
modification. It uses the recorded projective-space construction and actual
base-changed pair maps. No isomorphism, canonical map or scheme structure is replaced
by a `Nonempty` choice. Searches found no stability definition for these pairs.

## Second reading by Q101

Independent maintainer second reading, 2026-10-18, of immutable delivery
`168ad5806792554938cb5f368b5d8cd697cf7563`. This reader did not author the delivery.
The original worker report above is retained verbatim. This section replaces its
placeholder second-reading section; no Lean or node correction is needed.

I read packet.md, check-brief2.md in full, the immutable item and all 17 statement
dependencies, all four delivered modules, their module and declaration docstrings,
and the three new definition-node records. For recorded declarations absent from
the extracted Lean files I read the read-only Q101 clone and pinned slopmaster2
sources. Source checked: Temkin, *Stable modification of relative curves*,
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, §1.2 (printed p. 2),
Corollary 4.4.3(i) (printed p. 31), Proposition 4.5.1 and Remark 4.5.2 (printed p. 33).
The arbitrary-field extension is an explicit additional descent argument in the
node, not an assertion that Proposition 4.5.1 itself has that generality.

Clause correspondence, all accepted:

* `K : Type u`, `Field K`, `V : ValuationSubring K`: an actual valuation subring of
  its fraction field. I read Mathlib's `mem_or_inv_mem'`, `subtype`, and
  `IsFractionRing` instance. `[Finite (PrimeSpectrum V)]` is exactly the finite
  chain convention stated by the node, because valuation-ring primes are ordered.
* `Spec (.of V)` and `Spec.map (CommRingCat.ofHom V.subtype)` are the specified base
  and actual generic inclusion. There is no separably closed, discrete, rank-one,
  Noetherian, or characteristic hypothesis.
* `P Pst P' : MultipointedCurve ...` use the existing structure: both flat,
  locally finitely presented, quasi-compact and quasi-separated structure maps,
  pure fibre dimensions 1/0, closed marking, and its commutative triangle.
  These are full finite presentation and impose no separatedness over the base.
* `hXη` and `hDη` are smoothness and etaleness over the generic field, using the
  second pullback projections, with no splitting assumption on the marking.
* `f`, `g` are the compatible curve/marking maps over the base. `hf` includes
  properness of both maps, dense isomorphism opens, generic isomorphisms,
  semistability, and stability. `hg` plus `hsemistable` states the corresponding
  semistable modification assumptions for `g`.
* The existential is a morphism of pairs. Its first two equations express
  `fh = g` on curve and marking. Its last two equations give the specified generic
  inverse composites; `hf.1.generic_curve` and `hf.1.generic_marking` are exactly
  the isomorphism witnesses needed by `inv`.

I expanded each new definition against its node. `IsSemistable` uses the relative
smooth locus at markings and smooth-or-node on each chosen geometric fibre.
`Orgogozo.geometricPoint`, `localScalar`, `nodeRing`, and
`IsOrdinaryDoublePoint` were read in `Sheaf.Paper.OrgogozoInductionData`:
the completion is at the maximal ideal and its ring equivalence respects scalars;
`MvPowerSeries (Fin 2)` supplies precisely two variables. The connectedness in
`Orgogozo.IsSemistableGeometricCurve` is deliberately not imported into this notion.
`Hom` and all three base-change maps have actual data, constructed by `pullback.map`
and the pair equations. `IsEtaModification` asks for injectivity of the open
immersion's section maps over every open on target and source, not just topological
density. This is Temkin's two dense opens convention. `IsStableEtaModification`
tests an actual closed immersion of a projective line as an irreducible component,
its map over the residue-field algebraic closure, its contraction, and the union
of marking and nonsmooth points. The upstream `ProjectiveSpace` indexes homogeneous
coordinates, so `ULift (Fin 2)` gives a line. `Set.encard ≤ 2` handles infinite sets
correctly. A projective line is nonempty, so subsingleton image is contraction to
one point, not an empty-image loophole.

The other dependency interfaces read were `topologicalKrullDim`, `IsIntegral`,
`LocallyOfFinitePresentation`, `Smooth`, `IsClosedImmersion`, `Etale`, `Field`,
`Flat`, `Spec`/`Spec.map`, `pullback`, `AdicCompletion`, and `MvPowerSeries`.
Their uses agree with the dependency records. The pure-dimension helper was read
in `Sheaf.AlgebraicGeometry.PureDimension`. No unusable statement prerequisite
or universe repair was found. The generic pair, residue-field closures, and
projective line all live in the ambient arbitrary scheme universe `u`; `ULift`
only lifts the finite coordinate index and adds no size assumption.

I checked all six proof-plan steps against the nine cited proof statements.
The common refinement and contracted-component statements give the stated inputs;
eta-normality and component factorization give the curve comparison; flat
structure-sheaf torsion-freeness gives marking factorization. Valuation extension,
properness permanence, and marked base change apply in Step 4. The equalizer
argument in Step 5 uses flatness over the original domain, not a false claim
that the tensor square is a valuation ring. Representable fpqc descent then gives
both maps and reflects the compatibility equations. Stated proof interfaces are
imported; the remaining unstated proof nodes need no invented import at stage 2.

Edge cases: empty marking, empty scheme/fibre where allowed, height zero `V = K`,
finite higher height and nondiscrete valuations, arbitrary characteristic,
disconnected and nonproper/nonseparated curves, identity modifications,
nonsplit etale generic markings, and exceptional components with 0/1/2, at least
3, or infinitely many special points. No case is silently discarded.

Independent searches: LeanFinder query “A proper modification of a nodal marked
relative curve factors through its stable modification” returned eight
normalization/rational-map interfaces, no exact statement. LeanSearch query “A
nodal curve with marked points in its smooth locus has a minimal stable
modification” returned smooth-locus and Weierstrass minimality results, no exact
statement. Loogle `ValuationSubring` returned the interface used here. Direct `rg`
searches for multipointed, semistable, stable modification and eta modification
in upstream algebraic geometry, Mathlib algebraic geometry and Q101's trace-formula
modules found no replacement for these three definitions or the main statement.
The existing multipointed curve and ordinary-double-point interfaces are reused.
The new records have self-contained statements, empty proof/proof_deps,
source/blueprint/created/search fields and none-state lean audits; helpers in the
modification module are listed in `lean.declarations`.

All four `lean.statement` strings occur verbatim as their declaration signatures.
All module and declaration docstrings carry source and blueprint identifiers;
the main docstring gives all six proof steps. All definitions have real bodies;
the only delivered theorem ends in `by sorry`. No local theorem proof, private
notion, file-local notation or instance, auto-implicit variable, or overlong line
was found (maximum line lengths: 90, 92, 92, 93).

Reproduction: invoked the prescribed `scompile.py Q101
lem-trf-valuation-semistable-dominates-stable` on the four immutable files, ordered
MultipointedEtaModification, SemistableMultipointedCurve,
StableMultipointedEtaModification, ValuationSemistableDominatesStable.
Exit 0; no diagnostics. Private-overlay compiles took 2.0/2.2/2.3 seconds;
per-file library compiles took 2.0/2.0/2.2/2.7 seconds, with successful preliminary
and sandbox checks. The installed wrapper currently runs the private overlay on
the server through `nt_srv_compile.py --wire-confirm`; I used that wrapper,
not direct ssh, a live Lean write, or a global build.

Route-pivot check: no direct statement/proof dependency of the item or new nodes
is on `origin/newtargets-dag:coord/route-pivot-dropped.txt`; no item repair note
exists there. No dropped machinery or pro-etale replacement is introduced.

Finding H11: the delivered second-reading section was only a placeholder. This
replacement supplies the actual independent reading. No mathematical changes,
statement corrections, or dependency-record changes are required. Verdict: FIX
for this report only.

Review-environment limitation: two read-only HEAD checks of the contextual Q101
clone returned 72c22d4f60d1cfa0be2f06bbed63404a59e326a6 and then
ab5ae9a1d614cde26c9f6ba66a9a6a59c5c99566. This reader issued no mutating Git
command and did not reset the clone. Delivery files were read from the immutable
snapshot; their reviewed commit is unchanged.

## Repair of returned delivery (2026-10-18)

The returned delivery reported duplicate declarations from `Sheaf.TraceFormula.MultipointedEtaModification` and its dependent modules. I removed those duplicate modules from the packet and reused the canonical declarations in `Sheaf.AlgebraicGeometry.MultipointedCurveModification`: `AlgebraicGeometry.MultipointedCurve.Hom`, `Hom.curveBaseChange`, `Hom.markingBaseChange`, `MultipointedCurve.markingBaseChange`, `Hom.IsEtaModification`, `MultipointedCurve.IsSemistable`, and `Hom.IsStable`. The three dependency node copies now have `lean.existing: true` and point to those exact declarations. The item theorem imports the canonical module and takes `hf : f.IsStable`; its generic fibre components are the final two conjuncts of the existing `IsEtaModification` predicate. The item statement remains the same mathematically; only its Lean interface now uses the canonical existing predicate. The theorem file compiles cleanly with `scompile.py`.
