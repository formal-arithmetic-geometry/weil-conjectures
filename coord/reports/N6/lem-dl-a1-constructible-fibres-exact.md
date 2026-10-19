## Worker report

The main module `Sheaf.Paper.DlConstructibleFibresExact` states
`WeilConjectures.dlConstructibleFibresExact`. Its proof is `sorry`, as required in
stage 2. The source statement is unchanged. Its twelve proof steps are reproduced
in the theorem docstring, including the reduction of arbitrary Spec k points to
k-linear points, continuous coefficient realization, the constant-rank argument,
and the locally finite-type, non-quasi-compact locality argument.

Hypothesis and clause correspondence:

- The finite field, its fixed algebraic closure, the prime distinct from the
  characteristic and the coefficient algebraic closure are `D : FiniteFieldDatum`
  and `c : D.CoefficientDatum`. The conventional complex embedding is the explicit
  `_ι : c.Qbar ≃+* ℂ`; it has no role in exactness. No properness is assumed.
- A separated finite-type k0-scheme is `Y₀ : Over (Spec (.of D.k₀))` with
  `LocallyOfFiniteType Y₀.hom`, `QuasiCompact Y₀.hom`, `IsSeparated Y₀.hom`.
  The geometric scheme is exactly `(D.geometricFiber Y₀).left`.
- The heart is `sfCommonStageHeart c.l (D.geometricFiber Y₀).left c.Qbar`.
  This is the recorded full heart in the literal finite-field pair category,
  `generalAlgebraicallyClosedConstructibleCategory`, which is also the carrier
  of the recorded `intrinsicPbcQbarCategory`. No constant discrete Qbar sheaves,
  legacy coefficient category, or derived category of Weil sheaves replaces it.
- `dlAdicHeartFibre D c T x` is literally the composite of the heart inclusion,
  `commonStageDerivedPullback` along x, `pointQbarFibre D c.l c.different c.Qbar`,
  and `DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0`.
  The point parameter ranges over **all** `Spec (.of D.k) ⟶ T.left`, with no
  added `IsOver` condition, and therefore includes the base-automorphism cases.
  Residue-field inverses of l are supplied by
  `dlAdicGeometricResidueInvertible` in the new definition node. It transports
  `dlAdicBasePrimeUnit` through k0 → k and the residue-field map, without
  any additional assumption or dependency on a smooth-purity theorem module.
- `DlAdicFibreAssertions` requires every fibre to be additive and to preserve
  finite limits and finite colimits. It also asserts `FiniteDimensional c.Qbar`
  for every value. This states the exact finite-dimensional vector-space
  assertion, rather than making exactness a hypothesis.
- Joint conservativity is the second conjunct: for every arrow f, isomorphisms
  of all `F x |>.map f` imply `IsIso f`.
- The third conjunct is the explicit implication from every fibre map being
  zero to f being zero.
- The fourth conjunct quantifies over `S : ShortComplex C`, hence includes
  the equation that its two arrows compose to zero. `S.ShortExact` is equivalent
  to injectivity, `Function.Exact`, and surjectivity of the two fibre linear maps,
  for every displayed geometric point. These are the module-sequence conventions
  of `def-weil-pbc-exact-sequence`.
- For Weil sheaves, the category is the recorded `sfCommonStageWeilSheaf`.
  The existing `qbarCurveWeilHeartForget` works for every finite-type Y₀, despite
  its file/name: its signature takes no curve hypothesis. Its object is
  `⟨M.obj.carrier, M.property⟩` and its map is the underlying fixed-pair arrow.
  The theorem asserts that forgetting is additive, preserves finite limits and
  finite colimits, and that its composites with the geometric fibres satisfy
  exactly the same four fibre clauses. Thus no Weil clause is omitted.
- `DlAdicLocalExactness` quantifies over every locally finite-type k0-scheme,
  **without** quasi-compactness or separatedness. The local category is on that
  k0-scheme itself. A cover consists of an arbitrary `I : Type w` and separated
  finite-type opens U with `iSup U = ⊤`. For every short complex of locally
  constructible common-stage adic sheaves, global short exactness is equivalent
  to short exactness after every `dlAdicLocalEvaluation`. Local coefficients
  need not share one stage. The base prime unit is reflected from the algebraic
  closure to k0 and transported to residue fields by the structure morphisms.
- The final sentence restricting the theorem to adic constructible fibres is
  enforced by all the carrier types above: arbitrary pro-etale sheaves are
  never quantified over.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`, and
  `FiniteFieldDatum.geometricFiber` (the actual `Over.pullback` base change).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.Proper`,
  `.Separated`: `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `IsSeparated`;
  only the finite-type and separated classes enter this statement.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`,
  `sfCommonStageHeart`, and the standard-class/t-structure signatures.
- `Sheaf.Paper.IntrinsicQbarCategory`: `intrinsicPbcQbarCategory` and its actual
  `generalAlgebraicallyClosedConstructibleCategory` carrier. Its Noetherian,
  finite-dimensional and prime-invertibility domain follows from the given
  finite-type geometry; the heart uses the carrier directly.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointQbarFibre` and its object and
  representative formulas, its finite-stage scalar comparisons, and its
  explicit sections-plus-rationalization normalization.
- `Sheaf.Paper.CoefficientCohomologyModules`:
  `DerivedCategory.coefficientQbarCohomology`, its finite-dimensionality theorem
  and stage/tensor formulas.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilForget`, `sfCommonStageWeilSheaf`; these are IsoAlgebra
  fixed pairs on the current common-stage category.
- `Sheaf.Paper.CommonStageCurveWeilMiddleExtension`:
  `qbarCurveWeilHeartForget`, read in full and used without its unrelated curve
  direct-image operations.
- `WeilConjectures.DeligneLaumon.AffineLine.Defs`: the three recorded convention
  predicates were read, including `IsGeometricallyConstant`,
  `IsUnramifiedAtInfinity`, and upstream `IsIrreducibleLisse`. None is an
  additional hypothesis of the fibre statement; the finite-field/coefficient
  conventions are represented by D, c and the complex embedding.
- `Mathlib.Algebra.Homology.ExactSequence` and `.ShortComplex.ShortExact`:
  `ComposableArrows.Exact`, `ShortComplex.Exact`, `ShortComplex.ShortExact`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localQbarPullbackComposition`, used to
  construct the open-restriction compositor; no new arbitrary comparison is
  chosen.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`,
  recorded by `def-weil-derived-pullback-tensor-hom`, now explicitly cited.
- The additional new definition node below supplies the local category,
  evaluation functors and residue-field inverses. The existing
  `qbarCurveWeilHeartForget` is explicitly cited through its owning definition
  node `def-wf-middle-extension`.

The module privately imports the available proof-dependency modules below,
with the realization exception explained afterward:
finite-type Noetherianity, closed sections, immersion completed pullback,
rational transport, integral stratified-perfect characterization, point sections,
scalar exactness and comparisons, common-stage calculus, constructible
truncations, good stratification, connected components,
Nullstellensatz, w-contractibility, sheaf locality, open-closed triangles and
joint reflection of short exactness. The two proof nodes with no recorded
statement (`lem-tw-lisse-rational-realization` and
`det-lem-stratified-lattice-rank`) have no import to add yet. They are used in
the natural-language proof only, not assumed by the Lean statement.
The private import of `Sheaf.Paper.CondensedERealization` is also omitted as
requested by return F1: the independent review reported the landed module error
`Unknown identifier Data`, line 443. The saved dry run passed with its bundled
repair, but that unrelated repair is removed from this delivery; the realization
node remains a proof dependency, and no statement uses any of its declarations.

Searches for an existing statement:

- `msearch.py leanfinder`: “Geometric coefficient fibres are exact and jointly
  conservative on the constructible adic heart”: eight hits, principally
  `AdicCompletion.map_exact` and unrelated finite algebra/topology results;
  no exact match.
- `msearch.py loogle`: `CategoryTheory.ShortComplex.ShortExact,
  CategoryTheory.Functor.ReflectsIsomorphisms`: zero hits for the combined query.
- `msearch.py grep`: `jointly.*conservative|fibres.*exact|stalk.*exact` under
  CategoryTheory: zero hits.
- `rg` on the upstream WeilConjectures tree, the item ID, and corresponding
  fibre/exactness patterns: no declaration of this statement.
- `rg` on `lean/Sheaf/Paper`: found `AdicHeartPullbackFibres` and
  `AdicHeartIntrinsicFibres`. Those use different raw/category fibre interfaces
  and do not state this theorem's Spec k detection, Weil and non-quasi-compact
  locality clauses. Their recorded notions were read; no duplicate of them is
  introduced. The exact point/cohomology composite is the one required here.
- The upstream-name inventory and the project/source trees contain none of the
  new `DlAdic*` or `dlConstructibleFibresExact` declaration names.

Edge cases checked before and after writing: the empty scheme is permitted;
the point family can be empty, and joint detection then correctly forces its
heart to be zero. The local basis includes the empty open, with no nonemptiness
hypothesis. Cover indices may be empty, so the empty-scheme/empty-cover case is
retained. Zero sheaves, zero maps, zero-dimensional fibres, identity restrictions
and repeated opens are included. No connectedness, smoothness, properness,
lissity or semisimplicity is imposed. The independent cover universe w allows
arbitrary covers. Different coefficient fields on different connected components
of a non-quasi-compact scheme are allowed by the local data. Spec k maps need
not be k-linear. No equality between site object and morphism universes is added.

## New nodes

`def-dl-a1-locally-constructible-adic-heart`, in
`Sheaf.Paper.DlLocallyConstructibleAdicHeart`, fills the genuinely missing notion
in the final clause. It defines the separated finite-type open basis, actual
common-stage restriction, its existing integral-normalized composition
comparison, compatible families of heart objects, their compatible arrows,
componentwise zero and evaluation. It uses `InducedCategory`, `WideSubcategory`
and the pi-category from Mathlib rather than a second implementation of those
category constructions. Closure under identities/composition, zero compatibility,
zero absorption and evaluation-zero are named `sorry` theorems with proof
instructions; all these clauses are explicitly part of the new node's statement.
The definition data and comparison maps contain no `sorry`.

Source: BS 6.8.4(5) (descent), 6.8.6 (constructibility), 6.8.14 (finite-stage
realization), and 6.8.15 (restriction). On a locally finite-type scheme,
separated finite-type opens form a basis. Cartesian data on this entire basis,
with the restriction cocycle including repeated opens, is the local-heart
presentation of locally constructible adic sheaves. Using every basis open
avoids picking a cover or a global coefficient stage.

Searches: `blueprint_refs.py search 'locally constructible adic'` returned zero
blueprint nodes. `rg` of all DAG nodes found the consumer's local clause and
unrelated local constructibility notions; `def-sfb-affine-locally-constructible-
proetale-modules` is for discrete Noetherian constant-ring modules, not adic
common-stage hearts, so it cannot supply this notion. LeanSearch for the category
of compatible local adic hearts returned topology/local-constructibility and
generic sheaf-category hits. Loogle returned Mathlib's useful generic
`WideSubcategory`, not an adic heart. Mathlib grep for
`LocallyConstructible.*Adic|Adic.*LocallyConstructible|cartesian sections` returned
zero hits. The same project/upstream patterns found no existing local adic heart.
The raw search outputs are preserved in the new node's `mathlib_searches`.

## Second reading by N6

Resumed-worker self-check on 2026-10-18, with the saved node files and both
remaining modules open. This is the direct-delivery author's check; the
maintainer supplies the independent review, as required by the dispatcher brief.

The finite-field/coefficient binders and complex embedding render the conventions.
The three geometric instances render separated finite type without properness.
The geometric base change and full common-stage heart are the recorded objects.
`dlAdicHeartFibre` composes their actual inclusion, completed pullback, point
sections and degree-zero cohomology. Its point family contains every scheme map
from Spec k, including the maps that are not k-linear. `DlAdicFibreAssertions`
then renders exact additive finite-dimensional fibres, joint isomorphism detection,
zero-map detection, and both directions of short exactness. The second use of
that predicate composes with the actual fixed-pair heart forgetful functor, so
it retains all four assertions for Weil sheaves. The final conjunct quantifies
over locally finite-type k0-schemes and arbitrary covering families of separated
finite-type opens; it adds neither quasi-compactness nor separatedness globally.
The empty scheme, empty cover and zero sequence remain permitted.

For the new local-heart node, the family of heart values, restriction isomorphisms,
cocycle (including repeated opens), compatible arrows, componentwise zero arrows,
and evaluation functor match the stated local-data presentation. Completed
restriction and its compositor use the recorded canonical constructions. Every
postponed law is a named theorem with a proof docstring, and the definition data
are explicit. The new geometric residue helper maps the already specified
base-field unit
through the fixed field inclusion and the scheme structure map. Its data are
explicit; it neither uses `smoothQbarResidueInvertible` nor imports
`Sheaf.Paper.SmoothPurityQbar`. The item cites both owning definition nodes
for its completed pullback and Weil-heart forgetful functor.


The main mathematical statement is unchanged. Both residue-inverse helpers use
`@[instance_reducible]`, retaining the warning fix from the saved packet.
The additional geometric transport is included in the new definition node's
statement and declaration inventory. The requested dependency mismatches F1–F3
are repaired below. Compilation and mechanical checks are supplied by the
required wrappers.

## Returned delivery repaired

Compared the retained packet against returned head `f563ae1b5612` as described
in the return and against the current shared node records. The initial saved
packet dry run passed at `42df6f39f3`; its mathematical statements were retained.
The required self-check identified the returned dependency findings still present.

- F1: removed `lem-weil-pbc-condensed-e-realization` from statement dependencies,
  removed its dependency-node copy and module from this packet, and omitted its
  private import. Its role remains entirely in the unchanged natural-language
  proof and proof-dependency list. The reported landed-module diagnostic is quoted
  above; that node requires its own repair delivery.
- F2: removed the public import of `Sheaf.Paper.SmoothPurityQbar`. The helper
  `dlAdicGeometricResidueInvertible` belongs to the new local-heart definition
  module and is included in that node's `lean.declarations`. It transports the
  existing k0 unit through k and each residue-field map. The fibre composite uses
  this helper for both Spec k and its target. All Spec k maps remain allowed.
- F3: added the landed definition nodes `def-weil-derived-pullback-tensor-hom`
  and `def-wf-middle-extension` to the item's statement dependencies. Their
  recorded source signatures and docstrings were reread: the first supplies
  completed common-stage pullback; the second supplies the actual forgetful
  functor on every finite-type scheme, with no curve hypothesis.

Self-check: only the item's `lean` and `stmt_deps` differ from its current base
record. No dependency-node repair remains. The new definition node records its
additional geometric residue helper. The main theorem signature and its twelve
proof steps are unchanged, including every edge case listed above.

Validation on 2026-10-18: `scompile.py N6 lem-dl-a1-constructible-fibres-exact`
compiled both delivered modules separately and in dependency order, with no
errors or warnings. The library checks took 13.2 s for the local-heart module
and 34.1 s for the theorem module, each below the fixed 60 s limit. The
unchanged theorem signature matches its `lean.statement` verbatim.
