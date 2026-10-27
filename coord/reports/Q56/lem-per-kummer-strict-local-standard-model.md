## Worker report

The module `Sheaf.AlgebraicGeometry.KummerStrictLocalStandardModel` states
`AlgebraicGeometry.kummer_strict_local_standard_model`, with `sorry` as its only
theorem proof. Its helper definitions package the clauses of this same node and
construct the canonical chart, cokernel, monomial classes, and scalar maps from real
data. They do not choose a log scheme, map, or action from a postponed existence
proof. The repair adds two definition nodes with `existing: true` records; there
are no new Lean declarations or dependency-module repairs.

The live item is split and independently stage-1-reviewed on 2026-10-24, but has no
`lean` or `reviewed_lean`. `coord/queue.tsv` assigns stage 2. The stage handoff in
`coord/brief-stage2.md` section 0 explicitly permits recording its Lean statement
without reopening the reviewed split. Thus the inherited stage-1 live-wins refusal
is not a stage-2 blocker. No split field, source, proof, or mathematical statement
is changed. The `stmt_deps` additionally cite the definition owners actually used by this
statement: `def-per-fs-log-group-action`, `def-per-strict-log-morphism`,
`def-per-fs-log-pullback`, `def-per-log-morphism-identity`, and
`def-trf-log-regular-pair`. The two new nodes record existing declarations; the
others are already landed. The earlier theorem-node citations
`lem-trf-log-fan-chart-blowup` and `lem-sfb-log-morphism-operations` have been
replaced by definition owners, as requested in return L/H2. Each dependency was
checked not to lead back to this item through statement or proof dependencies.

Source checked directly with `pdftotext -f 78 -l 80 -layout` on
`literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`:
printed pp.72--73, VI 2.2--2.3. These pages give the ordinary cartesian chart square,
the fs diagonal, character formula (2.a), and both invariant-sheaf equalities.
Log regularity first appears in the subsequent additional paragraph, so it is not
an assumption of this statement. The docstring reproduces the eleven proof steps
of the current reviewed node, including their named dependencies.

### Hypotheses and conclusions

| Node clause | Lean rendering |
|---|---|
| Locally Noetherian fs log schemes `V,T` | `V T : FineSaturatedLogScheme.{u}` uses the recorded structure, including `locallyNoetherian` and `fineSaturated`. |
| Underlying base is the spectrum of a strictly henselian local ring `A` | `[IsAffine T.scheme] [IsStrictlyHenselianLocalRing Γ(T.scheme, ⊤)]`. Here `A` is the actual global-section ring. The canonical affine scheme isomorphism identifies `T` with `Spec A`. This is equivalent to the node's presentation by any such ring; no chosen arbitrary ring map is introduced. |
| Given log morphism `v` | `v : EtaleLogHom V T`, with the existing relative-test section maps. |
| Finite | `[IsFinite v.base]`. |
| Kummer | `hk : v.IsKummer`, the recorded characteristic-stalk predicate. |
| Log étale | `he : v.IsLogEtale`, the recorded chart-cover predicate. |
| Finite disjoint union, allowing the empty union | `m : ℕ`, `W : Fin m → FineSaturatedLogScheme`, and the scheme coproduct cocone with apex `V.scheme` is colimiting. `m = 0` is allowed. `Nonempty (IsColimit ...)` asserts a universal property, not an uncharacterized choice of data. |
| Components have the restricted log structures | `(ι i).IsStrict`; combined with the scheme coproduct this is precisely the log disjoint union. Scheme coproduct inclusions are open and closed, so the corresponding log structures are restrictions. |
| Component map is the restriction of `v` | `(ι i).CompEq v (f i)`, on both underlying maps and all log sections. |
| Each component is nonempty and strictly local | `IsAffine (W i).scheme ∧ IsStrictlyHenselianLocalRing Γ((W i).scheme, ⊤)`. A strictly henselian local ring is nontrivial, so no empty component is introduced. |
| Global sharp fs charts | `c : ∀ i, KummerStrictLocalChart (f i)`; the fields `fineP`, `fineQ`, `sharpP`, `sharpQ`, `chartP`, and `chartQ` give exactly these properties. Their sections live on the final étale objects, so these are global charts on the actual base and component. |
| One common base chart `P → M_T` | `(∀ i j, (c i).P = (c j).P ∧ HEq (c i).a (c j).a)`. This explicitly retains a common chart across the components; for the empty cover it is vacuous. Equality of the dependent homomorphisms retains their monoid structures as well. |
| Charts identify `P,Q` with the characteristic monoids at closed geometric points | `characteristicP` and `characteristicQ` require bijectivity of the actual `Associates.mk` of the chart germs at every geometric point with closed support. The existing characteristic monoid is precisely `Associates` of the log stalk. These are multiplicative monoid homomorphisms; bijectivity is therefore an isomorphism, with the specified canonical map. |
| Compatibility of the chart homomorphism with the given log morphism | `compatible` uses exactly `v.sectionMap` between the final étale objects. |
| Injective Kummer `h : P → Q` | `injective` and `multiple : ∀ q, ∃ d p, 0 < d ∧ q ^ d = h p`. Multiplicative powers encode the node's additive positive multiples. |
| Ordinary fibre-product standard model, including log structures | `cartesian : IsPullback v.base (chartToSpec ... b) (chartToSpec ... a) (Spec.map ... h)`. The chart maps use the existing `chartToSpec`, constructed by the global sections/spectrum adjunction from the monoid-algebra maps. Both actual log structures are those of the charts, so this scheme comparison is also a strict log isomorphism. This clause uses the ordinary scheme product and does not replace it by an fs product. |
| Surjectivity of each component map | `Surjective v.base` in `HasStandardCharacterDescription`. |
| Positive invertible integer annihilating `C` | `∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T.scheme, ⊤)) ∧ (∀ x : c.cokernel, x ^ n = 1)`. The quotient is the existing `FSLogChart.cokernel`, through the explicit `toFSLogChart` constructor. Finiteness of the cokernel also follows from the fs finite generation and this annihilator. |
| Cyclic root group of order `n` | `Nat.card (rootsOfUnity n Γ(T.scheme, ⊤)) = n ∧ IsCyclic (...)`. Mathlib's roots are the subgroup of units satisfying the nth-power equation, exactly the node's group. Positivity of the cardinal in particular excludes an infinite root group. |
| Finite constant character group | `c.characters n` is `c.cokernel →* rootsOfUnity n Γ(T.scheme, ⊤)`, with its ordinary pointwise group law, and `Finite (c.characters n)` is asserted. |
| Action by log automorphisms over `T` | An existing `FSLogGroupAction (c.characters n) V` is provided, with `(action.logMap γ).CompEq v v` for every character. Its existing fields impose the identity, composition, scheme automorphisms, and log section laws. |
| Character rule `z^q ↦ γ([q]) z^q` on the chart | `HasCharacterFormula` uses `StalkImage` for the actual action map. `monomialClass` is the quotient class of the canonical group-completion image of `q`. `kummerScalarGerm` pulls the root from the actual base ring by `v.base.appTop` and the canonical geometric germ. `unitsIn` includes that precise ring unit in the log stalk. The equation is imposed at every geometric point and for every chart monomial, hence is the global chart equation by conservativity of the stalks. Applying the structure map gives the same formula on regular functions. |
| Canonical character diagonal is an isomorphism to the fs product | `HasGaloisDiagonal` exhibits the log disjoint union `D` of copies of `V`, its projections `p₁,p₂`, the equations `(ι γ).CompEq p₁ (EtaleLogHom.id V)` and `(ι γ).CompEq p₂ (action.logMap γ)`, and the recorded universal property `p₁.IsFSPullback v p₂ v`. Thus its comparison to the fs product is the canonical map with components `(id,γ)` and is an isomorphism. This does not assert an ordinary scheme self-product: only the coproduct is an ordinary scheme coproduct. |
| Every log automorphism over the base is uniquely a character | For every `g : EtaleLogHom V V`, `g.IsStrict → IsIso g.base → g.CompEq v v → ∃! γ, action.logMap γ = g`. A log morphism is an isomorphism precisely when it is strict and its underlying scheme map is an isomorphism, so these hypotheses describe exactly all log automorphisms, not a chosen subgroup. Equality here is of the entire log morphism. |
| Canonical identification of the structure sheaf with invariant direct image | The first conjunct of `HasInvariantSheaves` tests every `E : T.scheme.Etale`. Its canonical pullback ring map `(pullback.fst E.hom v.base).appTop` is injective, and a target section is fixed by all character lifts fixing `E` if and only if it lies in this map's image. Since these are the actual natural pullback maps, these objectwise identifications give the claimed sheaf isomorphism. |
| Canonical identification of the log sheaf with invariant direct image | The second conjunct uses the given `v.sectionMap` on `logQuotientTest v E`. It is injective and its image is exactly `action.IsInvariantLogSection v E`, the existing invariant submonoid predicate on that pullback. This is precisely the canonical log-sheaf identification, on every étale object. |
| No log regularity, reducedness, or flatness assumptions | None occurs in the binders or helper conditions. The imported fs universal property has no such assumption. |

### Recorded declarations reused

The original statement dependencies were read, including their Lean signatures and
docstrings:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogStructure`, `EtalePrelogStructure.stalk`,
  `germ`, `unitsIn`, `IsChart`, `IsFineSaturated`, `characteristic`,
  `EtaleLogHom` and `EtaleLogHom.CompEq`.
- `Sheaf.AlgebraicGeometry.KummerLogMorphism`:
  `EtaleLogHom.StalkImage` and `EtaleLogHom.IsKummer`.
  The same node's `HasStrictLocalKummerChart` was read too: it concerns geometric
  strict-local stalk rings and does not itself state global sharp standard models,
  their character action, or their invariant sheaves.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`:
  `EtaleLogStructure.chartToSpec`, `FSLogChart`, its `groupMap` and `cokernel`,
  and `EtaleLogHom.IsLogEtale`. The specialized global sharp cartesian chart data
  is explicitly converted to this recorded chart; its group completion and quotient
  are reused rather than defined privately.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.condition`.
  The source was read through `scompile.py --source` because the local Mathlib
  package directory does not contain usable source files.

Additional already-landed statement providers (their relevant definitions and
signatures were read):

- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`,
  `logQuotientTest`, and `FSLogGroupAction.IsInvariantLogSection`.
- `Sheaf.AlgebraicGeometry.FSStrictLogMorphism`: `EtaleLogHom.IsStrict`.
- `Sheaf.AlgebraicGeometry.LogFanChartBlowup`: `EtaleLogHom.IsFSPullback`,
  including its common-composite square and uniqueness on every fs test object;
  now owned by new definition node `def-per-fs-log-pullback`.
- `Sheaf.AlgebraicGeometry.LogMorphismOperations`: `EtaleLogHom.id`, the actual
  identity including section maps, now owned by new definition node
  `def-per-log-morphism-identity`. This provider is imported explicitly.
- `Sheaf.AlgebraicGeometry.LogRegularPair`: `strictLocalRing` and
  `strictLocalGerm`, both recorded by `def-trf-log-regular-pair`, now explicitly
  cited in the item's `stmt_deps`. These are the actual ring-valued geometric
  stalk and its canonical germ maps used by `kummerScalarGerm`; citing this node
  adds no log regularity hypothesis.

The Mathlib notions used include `IsFinite`, `IsAffine`, `IsPullback`, `Cofan.mk`,
`IsColimit`, `rootsOfUnity`, `IsCyclic`, and `QuotientGroup.mk`. Strict henselianity
is the already published `IsStrictlyHenselianLocalRing` from
`WeilConjectures.Mathlib.RingTheory.Henselian`; its definition was read and says
henselian local with separably closed residue field.

All recorded project proof-dependency modules and the matched Mathlib proof tools
are imported without `public`, apart from modules already needed publicly for the
statement. The five unrecorded proof-only log-geometry prerequisites remain in the
reviewed DAG proof and in the full theorem docstring; this statement does not need
them in order to elaborate and does not replace their proofs by assumptions.

### Edge cases and self-review

- Empty cover: `m = 0` permits the empty coproduct. The component and common-chart
  conditions are vacuous; the base is still nonempty and strictly local.
- Nonempty factors: strict henselian locality includes nontriviality. There is no
  zero-ring factor disguised as a standard component.
- Trivial log structure and identity covers: `P,Q` may be the trivial monoid;
  `n = 1` is permitted, and the character group is trivial. The diagonal and
  automorphism uniqueness still say precisely what the node says.
- Nonreduced test: `A = k`, `P = Q = ℕ` with `h` multiplication by `n`, and the
  source ring `k[t]/(t^n)` is allowed. The ordinary standard model is nonreduced,
  the fs diagonal splits, and invariant sheaves are asserted without treating the
  ordinary self-product as the fs product. No reducedness or flatness was inserted.
- Positive characteristic: `0 < n` and `IsUnit (n : A)` exclude wild exponents
  exactly as stated. There is no characteristic-zero hypothesis.
- The common base chart is explicitly retained across all components; it was
  checked separately from the per-component characteristic identifications.
- Automorphism uniqueness ranges over every strict log endomorphism with an
  invertible scheme map and fixing the actual base log morphism.
- The ring and log invariant conditions are imposed on all small étale objects,
  not just the global ring, a closed stalk, or Zariski opens.
- The universe `u` is explicit throughout and matches the existing fs-log interface.
  There is no independent smaller universe of test schemes or fields. `autoImplicit`
  is false. There are no file-local notations, instances, or private declarations.
- The chart square commutativity used by `FSLogChart` is obtained from
  `cartesian.w`, rather than asserted as an extra tautological conclusion.

No mathematical statement fault or `STATEMENT-DISPUTED` issue was found. No
statement correction is made. No target or blueprint unit statement is changed.
The review in this report is the worker's self-review; independent maintainer
review remains required and has not been claimed here.

### Searches and validation

Searches made through the prescribed `msearch.py Q56
lem-per-kummer-strict-local-standard-model` wrapper:

1. `leanfinder`: "A finite Kummer etale cover of a strictly henselian local fine
   saturated log scheme is a disjoint union of standard Kummer covers with character
   action and invariant log sheaf". Eight hits, on `Scheme.Etale`, standard étale
   presentations, field étale decompositions and generic étale algebra tools; none
   states the log-geometric theorem.
2. `loogle`: "rootsOfUnity, IsStrictlyHenselianLocalRing, MonoidAlgebra". Zero hits;
   the public service does not know the project-specific strict henselian class.
3. `grep`: "Kummer|kummer|FineSaturatedLogScheme" in Mathlib `AlgebraicGeometry`.
   Zero hits.
4. `leansearch`: "finite Kummer etale strict local standard chart character
   automorphism invariant sheaf". Eight hits on formally étale algebras, Kummer
   field extensions, manifolds and standard étale rings, with no exact statement.

Local `rg` searches covered `lean/WeilConjectures` and `lean/Sheaf` for the node id,
`kummer.*strict|strict.*kummer|Kummer.*[Ss]tandard`, and the log morphism, group-action,
and fs pullback definitions. The node id is absent from the existing library.
`KummerLogMorphism` supplies only the lower-level predicates and strict-local-stalk
chart condition; the existing `FSLogGroupAction`, `FSStrictLogMorphism`,
`LogFanChartBlowup` and `LogMorphismOperations` supply the shared definitions reused
above. `python3 tools/blueprint_refs.py search 'strict local Kummer'` found no
blueprint-node match. A DAG scan found the strict-local model and related existing
Kummer nodes; none supplies an existing exact Lean declaration of this theorem.

Only `scompile.py` has been used to compile, always on the server against the live
published library. The module compiled cleanly in both sandbox and library modes
before the final documentation completion; the final file is checked again by the
prescribed delivery dry run. The only postponed proof is the matching named theorem
`AlgebraicGeometry.kummer_strict_local_standard_model`.

Validation of the retained packet: the initial prescribed `deliver2.py Q56
lem-per-kummer-strict-local-standard-model --no-push` returned `OK (dry run)` at
`9eafdcddf39` on 2026-10-24. That mechanical pass did not discharge the independent
H2 return; the repairs below do. Final repair validation is recorded below.


## New nodes

`def-per-fs-log-pullback` owns the existing definitions
`AlgebraicGeometry.EtaleLogHom.Square` and
`AlgebraicGeometry.EtaleLogHom.IsFSPullback` in
`Sheaf.AlgebraicGeometry.LogFanChartBlowup` (`existing: true`). The statement
introduces four fs log schemes, four arrows, equality of the full composites,
and existence and uniqueness of a full log factorization for every fs test
object. These are exactly `Square`, `CompEq`, and `IsFSPullback`; ordinary
scheme cartesianness is not asserted. The source is ILO VIII 3.3.9--3.3.11,
printed p.108, with the fs Galois diagonal of VI 2.2, printed p.72. LeanSearch
returned generic category squares and valuative criteria; LeanFinder returned
ordinary scheme pullbacks; Mathlib grep returned zero hits. Full outputs are
in the node's `mathlib_searches`. Project grep found the exact definitions at
LogFanChartBlowup.lean:168 and :176, with no upstream match. A DAG scan found
only their helper records under theorem `lem-trf-log-fan-chart-blowup`, no
definition owner. Blueprint search `fs log pullback` found zero nodes. Thus
this node registers the existing notion and does not duplicate its construction.

`def-per-log-morphism-identity` owns the existing concrete
`AlgebraicGeometry.EtaleLogHom.id` in
`Sheaf.AlgebraicGeometry.LogMorphismOperations` (`existing: true`), together
with the existing construction helpers `EtaleLogMap.id` and
`EtaleLogMap.toFSHom`. The statement introduces an fs log scheme and specifies
its identity by the identity scheme map and the restriction homomorphisms
on every relative etale log-section diagram. The declaration has precisely
those data, obtained from `EtaleLogMap.id` without changing them. The source
is ILO VI 1.1, printed p.69. LeanSearch and LeanFinder returned ordinary scheme
and sheaf identities; Mathlib grep returned zero hits. Full outputs are in
the node's `mathlib_searches`. Project grep found the exact concrete fs
identity at LogMorphismOperations.lean:140, and no upstream definition. The
DAG only recorded it as a helper of `lem-sfb-log-morphism-operations`.
`def-per-strict-log-morphism` already owns the distinct predicate
`EtaleLogHom.IsIdentity`, not this concrete identity construction. Blueprint
search `identity log morphism` found zero nodes. Both new nodes depend only
on `def-trf-fs-log-blowup` for fs objects, log morphisms, and `CompEq`, and both
are cited directly in the item's repaired `stmt_deps`.

## Repair of return L/H2

The independent review at immutable head `e5e1d63faf8f` accepted all mathematical
clauses and requested three ownership fixes. All three are implemented:

1. Replace `lem-trf-log-fan-chart-blowup` in the item's `stmt_deps` by the new
   definition owner `def-per-fs-log-pullback` for the plain fs-pullback predicate.
2. Replace `lem-sfb-log-morphism-operations` there by the new definition owner
   `def-per-log-morphism-identity` for the actual identity log morphism.
3. Add `def-trf-log-regular-pair`, whose recorded declarations own
   `strictLocalRing` and `strictLocalGerm`, both used by `kummerScalarGerm`.

The theorem and all helper definitions in the retained Lean file are unchanged.
The source modules and full signatures/docstrings of the reused definitions
were read again. Comparison with the current live node found only the retained
`lean` record and the authorized `stmt_deps` additions; the reviewed statement,
proof, source, and proof dependencies are preserved. No statement correction or
dependency-interface repair is made. The new nodes do not depend on either
theorem whose helper they register. Their records identify actual existing
definitions; they do not treat a theorem conclusion as data.

Self-check of the repaired ownership: `HasGaloisDiagonal` uses
`EtaleLogHom.id` to specify its first projection and `IsFSPullback` for the
universal property. `Square` includes commutativity, and uniqueness concerns
the entire log map. `kummerScalarGerm` composes `v.base.appTop` with the
canonical `strictLocalGerm` into `strictLocalRing`. Empty components, the
identity cover, and the trivial character group retain the previously checked
behavior. No new binder, hypothesis, action, map, or postponed proof is added.
This is the assigned worker's repair self-check, not a claimed independent
second reading; the maintainer supplies the independent review.

Repair validation on 2026-10-24: `scompile.py Q56
lem-per-kummer-strict-local-standard-model` compiled the retained module cleanly
in sandbox mode (19.9 s) and library mode (15.6 s). A read-only consistency
check passed for all three node files, exact existing signatures, the unchanged
theorem signature, JSON formatting, one `sorry`, the 100-character Lean line
limit, and absence of cycles through all statement/proof dependencies.

The first repaired-packet dry run exposed the current schema requirement for
`import_flags` (added to the gate on 2026-10-23). Both new nodes now have
`import_flags: []`. Its signature reader omits the `noncomputable` modifier,
so the existing identity record now starts at the `def` keyword, exactly as
the reader prints it. No Lean source change was needed.

Final repaired-packet validation: `deliver2.py Q56
lem-per-kummer-strict-local-standard-model --no-push` returned
`OK (dry run)` at `eeace9bc05a` on 2026-10-24, with both new definition
records, the strict-local germ owner, and all three H2 corrections included.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
