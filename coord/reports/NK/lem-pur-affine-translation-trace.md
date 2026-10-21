## Worker report

The module `Sheaf.Paper.AffineTranslationTrace` states
`AlgebraicGeometry.Etale.purAffineTranslationTrace`. Its only postponed proof is this
named theorem. Supporting declarations construct the composite action and base-change arrow,
the free trivial rank-d bundle, its standard frame and canonical chart identification,
the conjugate pro-etale translation action, and the compatibility propositions.
They contain real data and no `sorry`.

Clause-by-clause reading:

- The finite-field and coefficient datum is `P : WeilConjectures.PurityFiniteSetting`.
  Its `level` is arbitrary with `level_pos : 1 ≤ level`, and `P.Coefficient` is exactly
  the established universe lift of `O_E/(varpi_E^level)`. No ramification-index
  divisibility is imposed. The existing `coefficientFinite` instance supplies finiteness.
- A separated finite-type k-scheme is `(S : Scheme) (s : S ⟶ Spec (.of P.field.k))`
  with `[LocallyOfFiniteType s] [QuasiCompact s] [IsSeparated s]`. The compatibility
  definition derives `IsNoetherian S` using `isNoetherian_of_locallyOfFiniteType s`;
  it is not an additional geometric hypothesis.
- `d : ℕ` includes zero. `affineTraceTower S d` and `affineTraceProjection S d`
  are the recorded polynomial-coordinate model of A^d_S and q. Their canonical
  identification with Mathlib's `AffineSpace (ULift (Fin d)) S` is
  `affineTraceToAffineSpace`, from the trace dependency.
- `N`, `hN`, `hA`, and `hS` specify a presentation of the ordinary finite Tate line:
  N is positive, kills the actual coefficient ring, and is invertible on S. These
  are auxiliary coefficient-presentation data, not a restriction on n or S: for
  every n a sufficiently large power of ell gives such a presentation. The result
  applies to every permitted presentation, as does the recorded affine trace.
  In particular it does not use the restricted exponent `P.exponent` (n/e).
  The twist dependency identifies different annihilator presentations canonically.
- The unbounded category is the dependency's `DerivedCategoryModule P.Coefficient T`.
  `((affineTraceRight P.Coefficient N hA S d).obj (ordinaryFiniteUnit ... S))`
  is the recorded coordinate-tower expression for L = A_V(d)[2d]. The counit is
  `affineTraceCounit` with exactly `ambientAffineTraceTransport` and
  `ambientAffineTraceDatum`, selected by the published normalized-trace interface.
- A section is its coordinate vector `a : Fin d → Γ(S, ⊤)`. This is equivalent to
  a section of q even over a nonaffine base, by the affine-space representing
  property `AffineSpace.homOfVector`. Translation is the existing
  `ambientAffineTranslation S d a`, with sign z-a, not an arbitrary automorphism.
- `affineTranslationAction` is literally `ambientAffineTranslationExchange` followed
  by `(affineTraceLeft ...).map (ambientAffineTranslationTate ...).hom`. Thus the
  first section conjunct is exactly Ex followed by Rq_!(kappa) followed by t_q = t_q,
  with Lean's left-to-right composition order. It is an equality of derived maps.
- `AffineUniversalTranslationTraceEquation` explicitly uses parameter space
  `affineTraceTower S d`, translation coordinates `affineTraceCoordinate S d`, and
  the trace over that parameter space. This is the tautological section of the
  pulled-back affine bundle, not a fixed global vector on S. It is the first
  conjunct of the complete compatibility proposition.
- The second section conjunct quantifies over every separated finite-type k-scheme
  `(S',s')` and every k-morphism `g`, with `g ≫ s = s'`. No flatness, smoothness,
  surjectivity or affineness is imposed on g. The translated section has coordinates
  `fun i ↦ g.appTop (a i)`. The two equations state, respectively, that pullback of
  the action commutes with the canonical compact-support/Tate comparison, and that
  the normalized trace commutes with this same comparison and the constant-unit
  pullback isomorphism. `affineTranslationBaseChange` is exactly the pasted exchange
  followed by `affineTraceRightBaseChange` and `ordinaryFiniteUnitPullback`.
- The final section conjunct is `ProEtaleAffineTraceCompatibility P S s d a`.
  It is inside `∀ a`, and quantifies every annihilating prime-power level `r` and
  `hA`. Its equation is `proEtaleAffineTranslationAction ... a r hA ≫
  vectorIntegration ... = vectorIntegration ...`. Thus the pro-etale equality
  explicitly depends on the same translation vector, exchange and Tate action.
- The universal pro-etale equation is a separate conjunct over `affineTraceTower S d`,
  with structure map `affineTraceProjection S d ≫ s` and coordinate vector
  `affineTraceCoordinate S d`. It is the tautological section, including rank zero.
- `affineTraceTrivialFrame` is `Scheme.Modules.restrictFreeIso` at the top open.
  `affineTranslationChartBridge` is fixed by that frame: its local isomorphism `E`
  is precisely the three factors preceding the counit in `vectorIntegrationLocalTrace`.
  Its `C` is the canonical affine compact-support base-change isomorphism over the
  top-open inclusion, with its Tate and ordered-tower comparisons. Full faithfulness
  of pullback along this scheme isomorphism returns `E ≪≫ C.symm` to S by
  `Functor.preimageIso`. No trace or integration occurs in this construction.
- Writing `v = vectorSite`, `e = affineTranslationChartBridge`, `C = comparison`,
  and `rho = affineTranslationAction`, the actual pro-etale action is
  `v.hom ≫ C.map e.hom ≫ C.map rho ≫ C.map e.inv ≫ v.inv`.
  The canonical local normalization at the top frame identifies `e.hom` followed
  by the affine trace with ordinary bundle integration. The site-comparison dependency
  then identifies that map with actual pro-etale integration. The new conclusion
  is translation invariance under this fixed geometric action; it does not repeat
  `IntegrationCompatibility` or quantify an arbitrary isomorphism.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, via the
  ordered trace's actual open/proper compactifications.
- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `PurityFiniteSetting.Coefficient`, its finite-field, extension and positive level.
- Mathlib `AlgebraicGeometry.AffineSpace`: `AffineSpace`, `homOfVector`, and its
  `over` projection; the trace tower supplies the canonical polynomial identification.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and the coefficient module:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `def-weil-scheme-morphism-properties` is a collector, not an independent notion.
  Its finite-type and separated properties are Mathlib `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated`, used directly.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: `exists_affineSpaceTopTrace`;
  `AffineTraceConstruction`: `affineTraceLeft`, `affineTraceRight`,
  `affineTraceCounit`, `affineTraceExchange`, `affineTraceRightBaseChange`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleUpperStarIdIso`, `unboundedEtaleCompactSupportExchange`, and its
  bounded-below normalization, through the existing ambient exchange construction.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback`, `FiniteEtaleTwistPullbackData`, and its normalized
  root/tensor comparisons, through `OrdinaryFiniteTwistTransport`.
- `Sheaf.Paper.VectorIntegrationSiteComparison`:
  `VectorIntegrationSite.finiteTypeSiteComparison` and its underlying canonical
  `comparison`, `vectorSite`, and `vectorIntegration`. Its map equation is used only
  by the proof plan; the present conclusion is the additional translation equality.
- Newly cited existing definition node `def-trf-ambient-affine-translation-trace`:
  `Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace`, declarations
  `ambientAffineTranslationIso`, `ambientAffineTranslation`, the line expansion and
  square helpers, `ambientAffineTranslationTateStep`, `ambientAffineTranslationTate`,
  `ambientAffineTranslationLineExchange`, `ambientAffineTranslationExchange`, and
  the normalized `ambientAffineTraceTransport`/`ambientAffineTraceDatum`. The theorem
  `ambientAffineTranslationTrace` is retained only in `proof_deps`, as required.
- `def-amb-vector-integration`: `vectorBundleIntegration` and its canonical affine
  chart gluing, used for the explicit bridge in the pro-etale clause.
- `Sheaf.Paper.VectorIntegrationSiteComparison`: `vectorSite`, `vectorIntegration`,
  and `comparison` from `IntegrationCompatibility`; these are the actual pro-etale
  maps used by `ProEtaleAffineTraceCompatibility`.
- Proof imports: `compactSupportActionBaseChange`,
  `constantSheaf_sections_locallyConstant`, derived degree-zero full faithfulness,
  `IsLocallyConstant.apply_eq_of_preconnectedSpace`, and finite-type Noetherianity.

Edge cases checked before drafting: d=0 gives the identity tower and the unique
empty coordinate vector; a=0 gives the identity translation with its canonical
identity comparisons; the empty scheme has the unique maps and unit sections;
n=1 is included, and no e|n condition occurs; nonreduced/disconnected bases are
allowed; g can be the identity, a section, an arbitrary nonflat k-map, or have empty
source. All site/coefficient universes use the established u / u+1 convention.
The universal parameter scheme is separated finite type over k, so the same
base-change and site-comparison clauses apply over it as well.

Searches (2026-10-21 UTC):

- `msearch.py ... leanfinder "Translations of affine space preserve the normalized
  compactly supported etale cohomology trace with finite coefficients"`: eight
  hits on algebraic normalized traces, Hilbert 90 and etale loci; no matching result.
- `msearch.py ... loogle '"trace", "AffineSpace"'`: zero hits.
- `msearch.py ... grep 'translation.*trace|trace.*translation|affine.*compact.*support'`:
  four tactic-translation diagnostics; no mathematical match.
- `msearch.py ... leansearch "Translation invariance of integration in etale
  cohomology of affine space"`: eight integration/measure-theory results; no match.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for translation names and trace combinations: found the landed ambient theorem
  and reused all its concrete maps. The literal item id has no upstream declaration.
  No existing theorem contains the present combination of finite-field setting,
  universal equation, action/trace base-change diagrams, and site image equality.

## New nodes

`def-trf-ambient-affine-translation-trace` is a new existing:true definition record
for the already landed declarations in `Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace`.
It supplies the plain translation, exchange, Tate, and normalized transport/data
notions used by the item. The trace theorem remains a proof dependency only.

## Returned F1/H2 and F2/H3 repair

The accepted F1/H2 repair is retained: `def-trf-ambient-affine-translation-trace`
records exactly the ten plain definitions of the published ambient module. The
trace-invariance theorem is only in `proof_deps`; no theorem or `lineSquare` is
included in the definition record.

F2/H3 is repaired substantively relative to returned head `14f5203ab74f`.
The old existential bridge and its trace/site equalities are removed. The new
bridge uses the standard free frame on the top open and only the exchange,
coefficient and tower-comparison prefix of `vectorIntegrationLocalTrace`.
The pro-etale action is the conjugate of the ordinary Ex/Tate action through this
canonical bridge and `vectorSite`. The statement now says that action followed by
actual `vectorIntegration` equals actual `vectorIntegration`, both inside `∀ a`
and at the universal tautological coordinate vector. It contains no restatement
of `IntegrationCompatibility`. Advisory F3 concerns the existing ordinary trace
base-change equation, which is retained as the node explicitly requires it.

## Second reading by NK

I opened the retained node, the repaired module, the vector integration chart and
normalization definitions, and the site comparison source. The prior existential
bridge could be chosen from the two trace isomorphisms, independently of geometry;
its second equality merely repeated the dependency's site comparison. Both clauses
are removed. I traced the new bridge: `E` is the local chart prefix at the standard
frame on the top open; `C` transports the ordered affine source along that open;
`preimageIso` gives their unique preimage under the pullback equivalence. Neither
`E` nor `C` uses either integration morphism.

I checked the action's composition types: `vectorSource` goes through `v.hom` to
the compared ordinary bundle source, through `C.map e.hom` to the compared tower
source, through the compared Ex/Tate action, then back through `C.map e.inv` and
`v.inv` to `vectorSource`. Therefore its composition with `vectorIntegration` is
an actual derived-map equality on the pro-etale site. The vector `a` occurs in
that action. The universal conjunct uses the parameter scheme's tautological
vector rather than a fixed vector on S. The ordinary action and arbitrary-base-change
clauses are unchanged. All finite levels, rank zero, zero translation, empty bases,
and arbitrary nonflat base changes remain present. The sole postponed theorem is
`purAffineTranslationTrace`; supporting definitions have real data. This is the
worker's self-check; the dispatcher forbids spawning an independent reader, so the
maintainer's review supplies the independent reading.

Repair searches (UTC 2026-10-21):

- `msearch.py leanfinder "Canonical global trivialization chart identification for
  compactly supported vector bundle integration and translation invariance on the
  pro-etale site"`: eight manifold/topological vector-bundle chart hits, no exact match.
- `msearch.py loogle "Functor.preimageIso, Scheme.Modules.restrictFreeIso"`: zero
  hits, unknown identifier `Functor.preimageIso` in the hosted index. Direct source
  search located both declarations, which are reused.
- `rg` for `vectorIntegrationLocalTrace`, `VectorIntegrationNormalization`,
  `restrictFreeIso`, `preimageIso`, and compact-support exchange in the project and
  Mathlib found the exact component definitions used. No existing global-free-frame
  conjugate pro-etale translation action was found.

Validation: the retained packet's required initial dry run passed at `778ef4ff913`.
The repaired file compiled cleanly with `scompile.py` in both sandbox and delivery
module forms (12.1 s and 9.3 s); no warning was emitted. The delivery wrappers build
against current main in their own worktree; no direct git command or read-clone
mutation was used. The saved packet differs from main only by its already recorded
statement correction/dependency changes, the Lean attachment, and this repair.

## Statement corrected

The statement text remains the source statement, but its dependency interface was
corrected. The old `stmt_deps` incorrectly named the theorem
`lem-trf-ambient-affine-translation-trace`; the item uses only the theorem module's
plain definitions, so `def-trf-ambient-affine-translation-trace` is now the statement
dependency and the theorem remains in `proof_deps`. The old final conjunct was only
`comparison.map` applied to the ordinary composite and did not mention pro-etale
integration. It is now `ProEtaleAffineTraceCompatibility P S s d a`: the explicit equation
that the canonical conjugate translation action preserves `vectorIntegration`,
inside `∀ a` and also at the universal tautological vector. `vectorSite` and the
standard-frame chart identification fix the action; no existential bridge is used. Source: the item source place and the definitions
`def-amb-vector-integration` and `lem-pur-vector-integration-site-comparison`.
The sole citer is `lem-pur-projection-purity-agreement`; it still holds because its
proof dependency on the ambient theorem is retained.


## Returned L proof-dependency repair (2026-10-22 UTC)

The return on immutable head `60ab047e9131` identified exactly one mismatch:
`lem-trf-ambient-affine-translation-trace` was in `proof_deps` but not in the
union of the proof steps' `uses`. The required initial dry run of the retained
packet passed at `fa411d46e54`; it did not check this reviewer condition.

I read the current main node and the published `ambientAffineTranslationTrace`
signature and proof docstring. The theorem is precisely the ordinary coordinate
exchange/Tate/counit equation used here, for an arbitrary Noetherian base,
positive invertible annihilator, rank and coordinate vector. The final proof
step now explicitly invokes that theorem on S at a and on the universal
parameter scheme at its tautological coordinates, and its `uses` names the
same node. This matches step 5 of the retained Lean proof docstring, which
already names the ambient theorem. The retained definition-only statement
dependency and all earlier substantive statement repairs are preserved.

Self-check: `proof_deps` now equals the union of all four steps' `uses` exactly,
with no missing or extra id; each proof step remains below 2000 characters.
The Lean file and its recorded signature are unchanged, so this metadata repair
changes no hypothesis, conclusion, construction or citer use. I checked the
saved packet against current main through the initial delivery wrapper; its
changes remain the same retained statement correction and new definition
record, plus this explicit proof citation and report. No direct git command or
read-clone edit was used.


Validation after the L repair: `scompile.py NK lem-pur-affine-translation-trace`
compiled the retained Lean module cleanly in sandbox form (9.0 s) and library
form (9.1 s), with no diagnostics. The self-check also verified the exact
recorded signature, module header, explicit implicits, sole theorem `sorry`,
100-column limit, and preservation of the base proof in `statement_change`.
The current-main citer audit still consists exactly of
`lem-pur-projection-purity-agreement`, whose use holds as recorded.
