## Worker report

The delivery states `lem-per-kummer-g-cover-fs-base-change` in
`Sheaf.AlgebraicGeometry.KummerGCoverFSBaseChange`. Its two theorems are
`AlgebraicGeometry.kummerGCover_fs_baseChange` and
`AlgebraicGeometry.veryTame_logQuotient_isKummerGCover`. All three delivered
modules compiled separately through the prescribed server scompile.py wrapper;
only the expected sorry warnings are permitted. Every theorem proof is `sorry`.
Definitions have actual predicate/structure data and contain no postponed proofs.
The item's mathematical statement, proof, and proof dependencies are unchanged.

The source was read directly from the local ILO PDF: VI 2.1--2.3 and 3.1--3.5,
printed pp.71--76, and X 1.8, printed pp.146--147. In particular VI 2.2 uses the
fs product in its diagonal, VI 2.3 gives BOTH invariant sheaf formulas, and X 1.8
explicitly allows any fs base change. The formalization does not replace that
product by the ordinary scheme product.

The correspondence between the statement and Lean is as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Locally Noetherian fs log schemes C,D,E and locally Noetherian C_E | `C D : FineSaturatedLogScheme.{u}`; every `B : FSLogBaseChange q` has `B.base` and `B.total` of this same bundled type, whose `locallyNoetherian` and `fineSaturated` fields are the existing properties. |
| A finite group G | `{G : Type v} [Group G] [Finite G]`; no choice of an enumeration or equality of u and v is required. |
| The order of G is invertible on D | `horder : ∀ d : D.scheme, IsUnit (Nat.card G : D.scheme.presheaf.stalk d)`, at every ordinary local ring, including mixed characteristic. |
| The group acts over D | `a : FSLogGroupAction G C`; `IsKummerGCover` includes `∀ g, (a.logMap g).CompEq q q`, so invariance includes log sections. |
| Log etaleness in the specified chart sense | `q.IsLogEtale`, reused from FSLogSmoothEtale inside `a.IsKummerGCover q`. |
| Injective characteristic maps and positive-multiple condition | `q.IsKummer`, reused from KummerLogMorphism; its actual stalk-image relation tests injectivity modulo units and positive powers in the image. |
| Finite surjectivity | `IsFinite q.base ∧ Surjective q.base` in the cover definition, and again for B.snd in the output cover. |
| Canonical diagonal from the disjoint union, component (1,g), is an isomorphism | `S`, `ι`, `l`, `r`: the scheme cofan is a colimit, all `ι g` are strict, `l.IsFSPullback q r q`, and `(ι g).CompEq l (EtaleLogHom.id C)` and `(ι g).CompEq r (a.logMap g)`. This is precisely the assertion that the indicated disjoint union, with its component log structures, itself represents the fs self-product. Uniqueness of representing objects identifies this with the canonical diagonal isomorphism; no extra hypothesis on a chosen product is imposed. |
| Every E to D with locally Noetherian fs product | Universal quantification over `B : FSLogBaseChange q`, whose `map`, `fst`, `snd`, and `cartesian` fields specify any such representative. The original statement already assumes this product is locally Noetherian; no arbitrary existence choice or ordinary product is used. |
| The induced action on C_E | `B.IsInducedAction a b`: the two full log equations prescribe precisely `(g,1_E)`. The `∃! b` in `HasKummerQuotientsAfterFSBaseChange` supplies and uniquely characterizes it, instead of accepting an arbitrary action as an extra hypothesis. |
| C_E to E is a Kummer etale G-cover | `b.IsKummerGCover B.snd`. This includes all the original cover conditions and the new fs diagonal. |
| The underlying scheme quotient is E | `b.IsQuotient B.snd` includes the orbit quotient topology, the scheme categorical quotient property and affine invariants; finite surjectivity is in the preceding cover clause. |
| Orbit geometric fibres | Explicit quantification over algebraically closed `Ω : Type u` and scheme maps `x z : Spec (.of Ω) ⟶ B.total.scheme`, with equality over E iff `x` and `z` differ by a member of G. The same field for ordinary points is also in the existing `IsQuotient` definition. |
| O_E = (q_* O_C_E)^G | Existing `IsQuotient.affine_invariants`: inverse images of affine opens are affine and the canonical ring pullback is injective with image exactly the fixed sections. These affine identities identify the structure sheaf, rather than supplying an unnormalized sheaf isomorphism. |
| M_E = (q_* M_C_E)^G | Existing `IsQuotient.log_injective` and `.log_invariants` on EVERY etale E-test object, using its canonical ordinary scheme pullback test object. These are invariant log sections of the fs product itself, not of an ordinary replacement for C_E. The structural map is the given log morphism. |
| Compatibility with composition of fs base changes | `FSBaseChangeCoherence.comparison` gives the uniquely characterized canonical comparison over every base map; `.equivariant` matches the induced actions; `.identity` and `.composition` give the identity and three-level composition equations. `.iterated` supplies the inverse log maps between successive and direct fs products, with both prescribed projections. All equations use `CompEq` on full log morphisms, hence prescribe compositions on log sections as well as regular functions. |
| Compatibility of BOTH quotient identifications | These identifications are the canonical ring and log pullbacks in `IsQuotient`. `IsComparison` includes `r.CompEq B.snd (B'.snd.comp h)`. Its section equations, and the underlying scheme-map equality for ring sections, state that pulling back through the total-space comparison agrees with the successive base pullbacks. Since those pullbacks have exactly the invariant images, their inverse identifications obey the same equation. `.composition` states the corresponding three-level equality, with `.identity` covering identity base change. |
| No flatness and no log triviality required | The first theorem and every fs base-change/coherence binder impose neither condition. Log regularity is also absent from the general cover theorem. |
| The very tame quotient application | `veryTame_logQuotient_isKummerGCover` takes the Noetherian source, admissible and generically free action, log regularity and very tameness from `exists_veryTame_logQuotient`; `hquotient : a.IsQuotient q` specifies its invariant scheme/log quotient. It concludes the cover condition and both base-change conclusions. This applies to each quotient supplied by the dependency theorem, not an independently chosen log structure. |
| Freeness on the log-triviality locus in the application | `hfree`: every geometric point `x` in `C.logStructure.trivialityLocus` has trivial stabilizer. This hypothesis occurs only in the application theorem. The standing invertibility assumption is retained as `horder` on D. |

Dependencies used, after reading the node statements and recorded source declarations:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogHom`, `EtaleLogHom.CompEq`, `EtaleLogStructure.trivialityLocus`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogEtale` and its
  chart definition, through KummerLogMorphism.
- `Sheaf.AlgebraicGeometry.KummerLogMorphism`: `EtaleLogHom.IsKummer`,
  `EtaleLogHom.StalkImage`, and `EtaleLogHom.HasStrictLocalKummerChart`.
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`,
  `.IsQuotient`, `.IsEquivariant`, `.IsGenericallyFree` and the invariant-section
  definitions used by the quotient.
- `Sheaf.AlgebraicGeometry.VeryTameFSLogAction`: `FSLogGroupAction.IsVeryTame`.
- `Sheaf.AlgebraicGeometry.LogFanChartBlowup`: `EtaleLogHom.IsFSPullback`,
  `.IsStrict`, `.AreInverses`, `.IsIdentity`. Their full log universal property
  and inverse equations are reused, without a new fs-product notion.
- `Sheaf.AlgebraicGeometry.LogMorphismOperations`: actual `EtaleLogHom.id` and
  `.comp`, with relative etale section-map construction.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `Cofan.mk`, `IsColimit`, the
  match of `def-galois-finite-coproduct`.
- `Sheaf.AlgebraicGeometry.VeryTameLogQuotient`:
  `exists_veryTame_logQuotient`, restored as described below.

Existing proof-plan modules are imported without `public`: StrictHenselizationNoetherian
(`Algebra.isNoetherianRing_iff_isStrictHenselization`), FinitePushforwardSetStalk
(`finite_pushforward_set_stalk_bijective`), EtalePoint (conservativity of lifted
small-etale points), IndEtaleStrictLocalInvariance, LogRegularDivisorialStructure,
Mathlib's Finite and UniversallyInjective stability declarations, and
`CommGroup.subgroupOrderIsoSubgroupMonoidHom` from FiniteAbelian.Duality. The fs finite
comparison, Kummer-etale stability, strict-local standard model, tame admissible
quotient and finite quotient strict-local invariants nodes do not yet have Lean
records; they remain explicitly named in the proof docstrings. They are proof
inputs, not unstated prerequisites needed to type this statement.

Edge cases checked before writing: empty schemes (all relevant coproducts may be
empty even though a group is nonempty); the trivial group; disconnected covers
(the coproduct and component arguments do not require connectedness); nontrivial
underlying inertia at a boundary (the diagonal is an fs diagonal, not a free
ordinary-scheme torsor); arbitrary nonflat and nonstrict base changes; nonregular
bases in the first theorem; identity and successive base changes; and independent
scheme/group universes. Geometric test fields share the scheme universe, so the
quantifier is not vacuous on schemes of a larger unrelated universe. Finite G is
expressed by `Finite`, not a possibly empty indexing set or a chosen enumeration.

Searches made: msearch LeanFinder, query "Kummer etale finite group cover fs log
fibre product stable base change invariant quotient", returned ordinary etale
base-change results only. msearch Loogle "IsPullback, IsIso, HasPullback" returned
unknown identifier IsPullback; a second query '"pullback"' returned Function
pullbacks only. msearch grep 'Kummer|FSLog|FineSaturatedLog' in Mathlib's
AlgebraicGeometry returned no hits. msearch LeanSearch on the log quotient wording
returned ordinary scheme etale topology and base-change declarations. `rg` in
both project roots located the reused definitions above; no logarithmic G-cover
or FSLogBaseChange declaration exists. Searching the exact item id in upstream
WeilConjectures found no declaration. DAG regex searches returned applications
and existing theorem nodes, but no cover definition node; `blueprint_refs.py
search 'Kummer etale G-cover'` returned zero blueprint nodes. The new node contains
additional verbatim msearch results for its own defining notion (LeanSearch,
LeanFinder and grep), together with project/DAG search output. Its search misses
are not treated as missing mathematical hypotheses.

No statement correction or STATEMENT-DISPUTED flag is needed.

## New nodes

`def-per-kummer-g-cover`, module `Sheaf.AlgebraicGeometry.KummerGCover`, defines
`FSLogGroupAction.IsKummerGCover`, the explicit fs base-change diagram
`FSLogBaseChange`, and its induced-action and comparison predicates. Its source
is ILO VI 2.1--2.3 and X 1.8. The diagonal is a universal-property reformulation
of the stated canonical isomorphism, using the existing fs pullback and the
ordinary coproduct with strict component inclusions; it is not a new definition
of fs products. The separate node is required because neither a DAG definition
nor Mathlib nor either project root supplies this group-cover notion. Its
mathlib_searches contain the exact tool output. It reuses all previously defined
notions and cites their owning nodes, including the actual log operations and
scheme coproduct interface. The item's stmt_deps cites this new node and the landed strictness and very-tameness owners.

## Dependency modules

`lem-per-very-tame-log-quotient` has a recorded Lean theorem but its record says
the module was deleted on 2026-10-20. The source file is absent in the read clone,
and the mandated `scompile.py --source Sheaf.AlgebraicGeometry.VeryTameLogQuotient`
returned `Module source unavailable: Sheaf.AlgebraicGeometry.VeryTameLogQuotient`.
Under §1(B), this delivery restores the module and its recorded theorem signature,
with the original statement and every other node field unchanged. The signature
retains each hypothesis, invariant quotient, orbit geometric fibres, log
regularity, log etaleness and Kummer condition, standard strict-local charts,
and unique factorization of every invariant log morphism. Its proof docstring
contains all original proof steps. Existing definitions are imported, not copied.
Its `lean.note` records the failed source lookup and the exact scope of the repair.

## Second reading by Q110

A fresh clause-by-clause rereading was performed within this worker session;
no additional agent was started, as the dispatcher expressly forbids that.
The maintainer's independent review remains the independent reading. The table
above was checked against the live node and all three delivered files, not just
the declaration names. In particular the fs diagonal, geometric rather than just
ordinary orbits, canonical log invariants on all etale tests, the standing group
order assumption in the final application, and composition of both quotient
identifications were checked. The new definition's coproduct uses strict log
inclusions and the actual component equations, rather than an arbitrary isomorphism.
The dependency theorem was compared with the entire original recorded signature.
No mismatch was found and no mathematical statement was changed.

Dry-run repair: the server preflight requires `import_flags` on a new definition
node, although the brief's new-node field list omits it. Added the empty list.
Also explicitly imported the restored dependency's recorded Mathlib proof leaves
for finite algebras, Noetherianity and faithful flatness. The preflight advisory
about the old route-pivot deletion is acknowledged: this assigned node's unchanged
statement explicitly includes the very-tame quotient application, and the current
worker brief authorizes restoring its unusable statement dependency under §1(B).
No route-pivot file or other node field was changed.


## Repair of returned head a9b5aab38889 (H2/H12)

The initial saved-packet dry run passed as f2e51533937. Its automated checks did
not resolve the independent review finding, so the ownership graph is repaired
before delivery. All three Lean files are retained byte-for-byte; no mathematical
statement, hypothesis, conclusion or definition body changes.

`def-per-kummer-g-cover` now cites the landed `def-per-fs-log-pullback` for
`EtaleLogHom.Square` and `.IsFSPullback`, and `def-per-log-morphism-identity` for
`.id`. It cites `def-per-strict-log-morphism` for `.IsStrict` and `.IsIdentity`,
whose provider is now `Sheaf.AlgebraicGeometry.FSStrictLogMorphism` (re-exported
by LogFanChartBlowup). The theorem-node citations
`lem-trf-log-fan-chart-blowup` and `lem-sfb-log-morphism-operations` are removed
from that definition's statement and statement dependencies. Their theorems are
not prerequisites for defining these notions. The item also directly cites the
landed `def-per-very-tame-fs-log-action`, resolving the advisory about IsVeryTame,
and the strictness owner used by its coherence predicate.

## New nodes (repair additions)

`def-per-log-morphism-composition` is an existing:true ownership record for
`AlgebraicGeometry.EtaleLogHom.comp` and its general helper `EtaleLogMap.comp` in
`Sheaf.AlgebraicGeometry.LogMorphismOperations`. Source: ILO VI 1.1 and X 1.8.
The relative diagram uses U = Y times_Z W and its uniquely prescribed map from V;
the section map is the actual composite through U. This matches the definition
body, including the scheme component, not just a compositional existence claim.

`def-per-inverse-log-morphisms` is an existing:true ownership record for
`AlgebraicGeometry.EtaleLogHom.AreInverses` in
`Sheaf.AlgebraicGeometry.LogFanChartBlowup`. Source: ILO VI 1.1 and VIII 3.3.9.
The two existential common composites in its statement match the two conjunctions
of `CompEq` and `IsIdentity` in the definition. Its statement dependencies cite
`def-per-strict-log-morphism` for the actual identity criterion. Neither new node
adds a Lean module or duplicates a definition. The cover definition cites both.

Fresh search results are preserved verbatim in each new node: LeanSearch and
LeanFinder returned only ordinary scheme inverse/composition results; Mathlib
grep returned zero log-operation hits. Project rg located exactly the definitions
above; a scan of every definition-node Lean record found no owner for comp or
AreInverses. Blueprint searches for composition/inverse log morphism both returned
zero nodes. The already-landed Q56 pullback and identity records are reused.

## Second reading by Q110 (repair)

Self-check, with node JSON and source definitions open; no second agent was started.
The retained cover still has log etale, Kummer, finite, surjective and invariance
conjuncts, the coproduct colimit, strict inclusions, fs universal property, and
both component equations. The base-change records still prescribe both projections
and full log comparison equations. The retained item still gives a unique induced
action, cover and quotient with both canonical invariant sheaves and geometric
orbits; comparison, equivariance, identity, composition, and the iterated inverse
are unchanged. Every application hypothesis (Noetherian, admissible, generically
free, log regular, very tame, invariant quotient, invertible order and freeness
on the triviality locus) is unchanged. Empty schemes, trivial group, nonflat and
nonstrict changes, identity and iterated changes retain the same quantifiers.
The new ownership records' signatures were extracted verbatim from the existing
source. Composition has no finiteness hypothesis; inverse equations test all log
sections in both directions. The restored dependency keeps the Q46 signature
(whitespace apart) and its lean-only repair note. No statement correction is needed.

Repair validation: the prescribed scompile.py compiled KummerGCover,
VeryTameLogQuotient and KummerGCoverFSBaseChange separately with no errors or
unexpected warnings. The repaired-packet deliver2.py --no-push passed server
preflight and compilation as b07ce5fa548. The record comparison with current main
shows the item changes only lean/stmt_deps and the restored dependency only lean;
the two ownership records use exact existing declaration signatures. No source
file in the read-only repository was edited and no direct Git command was run.


## Repair of returned head 1bef3c0dcaf8: missing composition node

The returned check (b) reports that def-per-kummer-g-cover cites a composition
node absent from that review base. Current main now has the reviewed Q67 node
`def-per-log-morphism-composition`, with existing:true declaration
`AlgebraicGeometry.EtaleLogMap.comp` in
`Sheaf.AlgebraicGeometry.LogMorphismOperations`. This repair removes the competing
Q110 copy from this packet and reuses Q67's landed node unchanged. The new-nodes
paragraph above describing a Q110 composition ownership record is superseded:
composition is an existing dependency, not a new node of this delivery.

The cover's prose now explicitly identifies its fs composition with the fs-endpoint
restriction of that general relative-section construction. The item directly cites
the landed composition owner too, since its coherence predicate uses composition.
The prior dry run a15e372f126 reported that it filtered differing fields of the
competing copy; removal of that copy avoids proposing any alteration to Q67's node.
No mathematical statement or Lean source changes. No parallel delivery is assumed:
the dependency node is present on current main and carries reviewed_lean.

## Second reading by Q110 (composition dependency repair)

I opened the landed node and LogMorphismOperations: EtaleLogMap.comp uses the
canonical U = Y times_Z W and V-to-U factorization, then composes the two log-section
maps. EtaleLogHom.comp is literally
`(f.toLogMap.comp g.toLogMap).toFSHom`, and toFSHom retains base, sectionMap,
naturality and compatibility. Thus the landed general construction supplies exactly
the composition in the retained cover and coherence definitions, with no new
assumption or theorem. Both cover references to composition and the item's direct
stmt_dep resolve to that landed node. The remaining new inverse-morphism owner
still supplies both full-log inverse equations. All retained hypothesis/clause and
edge-case checks above remain applicable; none changed in this repair.

Validation of this repair: every delivered node's stmt_deps resolves against current
main plus this packet. The composition node is absent from the packet and present
on current main with Q67's reviewed existing:true record. The prescribed scompile.py
compiled all three retained modules separately without errors or unexpected warnings.
