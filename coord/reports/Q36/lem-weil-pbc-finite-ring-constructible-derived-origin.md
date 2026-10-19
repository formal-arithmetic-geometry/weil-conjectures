## Worker report

The delivery states `AlgebraicGeometry.Scheme.finiteRing_constructibleDerived_origin` in
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`. Its proof is `sorry`. It also supplies
two dependency repairs described below. No mathematical assertion is proved in this delivery.
The item's natural-language statement, proof and proof dependencies are unchanged.

The theorem states the equivalence by the logically equivalent full-faithfulness and
essential-image criterion for the specified functor. This avoids an arbitrary equivalence:
the functor in every clause is the canonically constructed exact comparison inverse image.
`Functor.essImage` is exactly `∃ L, Nonempty (F.obj L ≅ K)`, and the source object `L`
belongs to the existing full bounded constructible etale subcategory. Consequently the
reverse implication in the essential-image biconditional is precisely the requested
bounded constructible etale-origin assertion. Fullness and faithfulness plus this
biconditional say that this same functor induces an equivalence onto the indicated full
subcategory; no extra hypothesis on objects or morphisms is imposed.

Clause-by-clause correspondence:

- An arbitrary scheme is `(X : Scheme.{u})`. There is no quasi-compactness, separation,
  Noetherian or base-field hypothesis.
- The coefficient ring is `(B : Type u) [CommRing B] [Finite B]`. There is no nonzero
  assumption, DVR, uniformizer, characteristic, or adic coefficient datum. Its lifted
  copy `ULift.{u + 1, u} B` allows the existing etale module sheaves to take values in
  `ModuleCat.{u + 1}`. The intrinsic pro-etale category already uses exactly this lift
  internally in `proEtaleConstantRing X B`.
- The small etale site is `X.smallEtaleTopology`; the small pro-etale site is
  `Scheme.ProEt.topology X`, as used in `proEtaleRingModules` and `proEtaleDerivedCategory`.
  Their original object and morphism universes are retained.
- The exact derived inverse image is
  `ProEtale.finiteCoefficientIntrinsicDerivedComparison X B`. The dependency repair
  constructs it from the recorded `comparisonUpperStar`, the recorded
  `finiteCoefficientModulePresheaf`, and Mathlib's associated-module sheafification
  along the actual commutative constant-ring sheafification unit. Finally
  `Functor.mapDerivedCategory` applies this exact functor termwise. This is a canonical
  change of coefficient presentation of the specified inverse image; its action is
  determined by the scalar unit and sheafification, rather than by a choice of a map.
- Bounded etale complexes with constructible cohomology are the existing
  `Etale.DerivedCategory.isBoundedConstructible (ULift B) X`. Its definition is the
  conjunction of `∀ i, IsConstructibleEtaleModuleSheaf (H^i L)` and vanishing outside
  some `[a,b]` with `a ≤ b`. `ObjectProperty.ι` is the inclusion of its full subcategory.
  The item's `stmt_deps` gains the already recorded
  `def-weil-pbc-constructible-complexes` because this declaration is used directly.
- The first and second conjuncts are `.Full` and `.Faithful` for that inclusion followed
  by the specified derived comparison. All morphisms are ambient derived morphisms.
- The third conjunct identifies its `.essImage K`, for every pro-etale `K`, with
  intrinsic constructibility of each cohomology sheaf plus the existence of integers
  `a ≤ b` with vanishing outside `[a,b]`. Cohomology is exactly
  `DerivedCategory.homologyFunctor (proEtaleRingModules X (proEtaleConstantRing X B)) i`.
  Intrinsic constructibility is the recorded `IsConstructibleProEtaleModuleSheaf X B`,
  repaired to include the constructible-subset condition that the node requires.
- The last conjunct quantifies over every etale derived complex `L` and integers `a b`.
  It states the biconditional between `IsZero (H^i L)` for `i < a ∨ b < i` and the same
  vanishing for its specified inverse image. Thus every interval is both preserved and
  reflected. Neither the source complex nor the interval is unnecessarily restricted.

Dependency declarations read and used:

- `def-weil-pbc-proetale-modules`: read
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` in full, and confirmed the current
  server source with `scompile.py --source`. Used its
  `FiniteCoefficientEtaleDerivedCategory` and `finiteCoefficientModulePresheaf`, and
  re-exported the whole original module in the interface repair. The original
  `finiteCoefficientDerivedComparison` is in the continuous-function ring presentation;
  the repair supplies its intrinsic constant-ring presentation.
- `def-weil-pbc-etale-constructible-sheaf`:
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, used through the existing
  bounded constructible predicate. Read its definition and docstring.
- `def-weil-proetale-constructible-sheaf`:
  `Sheaf.Paper.ProEtaleConstructibleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`. Read its full definition,
  its docstring, and `LocallyClosedStratification` to check its actual conditions.
- `def-weil-derived-cohomology-sheaves` is a Mathlib leaf, with no Lean record needed:
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`. Read its signature, docstring and representative
  factorization. This supplies both sides' cohomology.
- The additionally cited `def-weil-pbc-constructible-complexes` is in
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, declarations
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` and
  `AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory`; read their definitions.
- The already stated proof inputs are imported: the finite-ring sheaf-origin theorem,
  finite-level exactness/unit theorem, and Mathlib's single-degree, truncation,
  homology-sequence, exact-derived-functor and triangulated-category interfaces.
  `thm-weil-pbc-site-comparison` has no recorded Lean declaration in the inspected DAG,
  so there is no module to import for that proof-only input. This does not prevent
  writing the requested statement. Its use remains explicit in the proof docstring.

Edge cases checked before writing:

- The zero finite ring is allowed by `CommRing` and `Finite`; no nontriviality is required.
  The zero module and complex satisfy all vanishing bounds, and zero cohomology is
  constructible using constant zero modules.
- The empty scheme and empty strata are allowed. The positive-stratum condition of the
  intrinsic node is retained: the empty scheme admits a one-empty-stratum partition.
- For `a = b`, the last conjunct states the single-degree assertion. For `a > b`, every
  integer lies outside the interval, so it states preservation/reflection of acyclicity.
  The boundedness existential still has `a ≤ b`, which includes the zero object, e.g.
  `[0,0]`. Negative bounds and shifts are allowed because all degrees are integers.
- Each cohomology sheaf may have its own finite global stratification. No common
  stratification across infinitely many degrees, affine-local replacement, or closure
  incidence condition is inserted. Constructibility of the subsets is explicit on both
  sides after the dependency repair.
- The coefficient lift is a ring-equivalent copy with unchanged finiteness; it adds no
  size restriction on the small sites, test objects or geometric points.

Searches for reuse (also recorded by the launcher in `searches.jsonl`):

- `msearch.py leanfinder`, query “The exact inverse image from etale to proetale induces
  an equivalence on bounded constructible derived complexes for any finite commutative
  ring”: eight unrelated results (solid condensed modules, formally etale algebra
  equivalences, coherent extensive sheaf comparison, and discrete light condensed
  modules), no matching statement.
- `msearch.py loogle`, query `DerivedCategory.homologyFunctor, Functor.IsEquivalence`:
  no hits; service reported unknown identifier `Functor.IsEquivalence`.
- `msearch.py grep`, query `proetale.*constructible|constructible.*derived`: no Mathlib hits.
- `msearch.py leansearch`, query “Equivalence of bounded constructible derived categories
  on etale and proetale sites”: service unavailable, Internal Server Error. This is
  recorded as unavailable, not as a negative search result.
- `rg` over `WeilConjectures/` and `lean/Sheaf/`, including exact item-id and proposed-name
  searches, found no existing derived-origin statement. Existing bounded constructible
  predicates and the finite-ring sheaf-origin theorem were read and reused. The source
  constructible predicate differs from the recorded finite-global-stratification
  predicate, as the existing `BoundedConstructibleComplexes` docstring explains.
- For the coefficient interface, `msearch.py leanfinder`, query “Sheaves of fixed ring
  modules are equivalent to sheaves of modules over the sheafification of the constant
  ring presheaf”: eight results, principally `PresheafOfModules.sheafification`,
  `sheafify`, and their Hom equivalences. These provide the actual construction used.
  Searches of Mathlib, upstream and project sources found only the etale-specific
  `EtaleConstantRingModuleEquivalence` and the continuous-function presentation in
  `ProEtaleFiniteModules`, not the needed intrinsic pro-etale presentation. Both were
  read; no existing general interface was copied or redefined.

Source check: opened https://stacks.math.columbia.edu/tag/09AL. It states the comparison
for Noetherian coefficient rings on the constructible bounded-below subcategories. The
node restricts to finite coefficients and bounded intervals, with its explicit global
finite-stratification convention; the seven-step node proof supplies that global form.
No item-statement correction or STATEMENT-DISPUTED flag is needed.

Validation: all three delivered files compiled individually in dependency order in the
private overlay through `scompile.py`, with no errors and no warnings. All universes and
variables are explicitly bound. Every definition has actual construction data, and each
postponed theorem has its source, owning DAG node and natural-language proof docstring.
The three new postponed assertions are the scalar unit's local bijectivity, exactness of
its canonical module realization, and the requested derived comparison theorem.

## Dependency modules

`def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`
publicly imports the original module, preserving all its constructions. The original
record supplies the continuous-function coefficient presentation, which cannot be passed
directly to the intrinsic constructibility predicate over the commutative constant ring
sheaf. The added scalar unit is precisely `whiskerRight (toSheafify ... constCommRing) forget₂`.
The fixed-scalar module presheaf and associated-module sheafification along this unit give
the canonical intrinsic realization. Its local-bijection and exact-equivalence properties
are named postponed theorems, with named instances projecting the required properties.
Composition with the recorded comparison inverse image, then `mapDerivedCategory`, gives
the exact derived comparison in the required presentation. The node changes only in
`lean`; `lean.note` explains this interface extension. Its main recorded declaration is
the added derived comparison, and `lean.declarations` lists all declarations of its module.

`def-weil-proetale-constructible-sheaf`: the delivery repairs the owning
`Sheaf.Paper.ProEtaleConstructibleSheaf` module in place. The previous Lean omitted
`∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)`, although the node explicitly
requires constructible locally closed strata. `LocallyClosedStratification` explicitly
has no such condition. The repaired definition inserts that conjunct and preserves every
other binder and condition, including `0 < S.n`, immersed subscheme data, canonical module
pullback, local constancy and finite geometric stalks. Only this dependency node's `lean`
record changes, with an explanatory note. No natural-language node is corrected.

## Earlier second reading (a previous round; superseded)

The node statement was read as the following list.

1. Objects and hypotheses: an arbitrary scheme `X : Scheme`, a finite commutative ring
   `B`, the small etale and small pro-etale sites, their coefficient module categories,
   and the exact derived inverse image `nu_X^*`.
2. First conclusion clause: this inverse image is the functor from bounded etale
   complexes with constructible cohomology to pro-etale complexes.
3. Second conclusion clause: it induces an equivalence onto precisely the pro-etale
   complexes whose cohomology sheaves are intrinsically constructible and vanish outside
   one finite integer interval.
4. Third conclusion clause: every such pro-etale complex has bounded constructible
   etale origin.
5. Fourth conclusion clause: no quotient-of-a-DVR hypothesis on `B` is present.
6. The interval clause requires preservation and reflection of every cohomological
   interval `[a,b]`.

The Lean renders these items as follows, with no mismatch found. `X` and `B` are the
explicit binders `(X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]`; there is no
Noetherian, separated, field, nonzero, characteristic, DVR, or uniformizer hypothesis.
The comparison functor is exactly
`ProEtale.finiteCoefficientIntrinsicDerivedComparison X B`, built from the recorded
comparison and canonical constant-scalar sheafification. Its source is the full
subcategory selected by `Etale.DerivedCategory.isBoundedConstructible`; its target is
`proEtaleDerivedCategory X B`. The `.Full` and `.Faithful` conjuncts express the
categorical equivalence's full-faithfulness. The `essImage` biconditional quantifies
over every target object and says exactly that all cohomology objects are
`IsConstructibleProEtaleModuleSheaf` and that some `a <= b` kills every degree outside
`[a,b]`; this also supplies the etale-origin clause. The final universal biconditional
quantifies over every etale object and all integers `a,b`, and compares `IsZero` of
the two homology sheaves outside that interval, giving preservation and reflection.
The final conjunct therefore also covers `a > b` (acyclicity) while the essential-image
existential correctly requires `a <= b`.

Edge cases checked: `B` may be the zero finite ring; zero modules and zero complexes
are admitted; the empty scheme is admitted by the intrinsic constructibility
definition; `a = b`, negative degrees, arbitrary shifts, and the zero complex are
covered; and no index type or test-algebra universe is independently quantified. The
`ULift.{u + 1, u} B` coefficient used by the etale module category is the recorded
universe transport and does not restrict the scheme or geometric-point cases.

Searches were repeated with `rg` over the project and upstream `WeilConjectures`, exact
name and item-id searches, and the recorded `msearch.py` LeanFinder/Loogle/Grep queries.
Only the existing bounded-constructible predicate, comparison infrastructure, and
sheaf-origin theorem were found; no statement or definition of this derived-origin
assertion exists in Mathlib or upstream. The Stacks source was checked at Tags 09AK
and 09AL: it assumes a Noetherian coefficient ring and gives the constructible
sheaf and bounded-below derived equivalences, which specialize to the node's finite
ring and bounded-interval formulation.

The dependency repairs were reread against their nodes. The intrinsic comparison
module uses real canonical sheafification data and only postpones its named local
bijectivity/exactness theorems; the constructibility definition now explicitly
requires constructible strata as its node requires. No hollow definition, unbound
variable, extra hypothesis, or stronger target clause was found. No source statement
correction was needed, so no citer audit or node statement edit was made. I changed no
Lean or node content in this second reading; the existing three modules compile cleanly
with the prescribed `scompile.py` invocation.

## Maintainer independent reading, 2026-10-16

The immutable delivery's three modules compiled cleanly, separately in dependency
order through scompile.py, in both sandbox and library modes. The mathematical
statement and both dependency repairs agree with their nodes. No statement
correction or citer audit is required.

H4 reuse repair: finiteCoefficientIntrinsicScalarMap_locallyBijective duplicated
Scheme.proEtaleConstantRingUnit_locallyBijective, already stated in
Sheaf.Paper.ProEtaleLocallyConstantSheaf. The earlier search and second reading
missed this exact existing theorem. The complete replacement imports that owning
module and projects the two required local-bijection instances directly from its
theorem, removing the duplicate theorem and its lean.declarations entry. The
canonical scalar map, module sheafification, exact realization theorem and derived
comparison are unchanged. There are two new postponed assertions after this repair:
the intrinsic realization's exact-equivalence properties and the item theorem.
The earlier report's references to three new assertions and a new scalar-unit
local-bijectivity theorem describe the original delivery, superseded here.

The fixed module, unchanged constructibility module and unchanged item module are
recompiled together through scompile.py as separate files in dependency order.
All source and declaration checks, edge cases and compiler outcomes are recorded
in the independent maintainer review.md.

Record clarification: the currently available upstream Topology.Stratification has
isConstructible_stratum (Topology/Stratification.lean:63), inherited by
LocallyClosedStratification. Thus the explicit constructible-strata conjunct is
redundant against that version. The owning dependency module's docstring saying
that it adds no constructibility condition describes its own extra fields and is
not evidence that inherited data lacks it. The earlier report's claim that the
whole inherited structure lacks constructibility is inaccurate. The added explicit
conjunct remains mathematically correct and is retained; the dependency lean.note
is corrected to record the actual source situation.

Fixed per-file compilation completed successfully in both sandbox and library
modes with no diagnostics. Library times: intrinsic comparison 5.4 seconds,
constructibility 8.0 seconds, and item theorem 8.4 seconds; each is below the
60-second per-file limit.

## Second reading by Q36

I reread the node, its source place, every dependency record, and all three delivered
modules. The source is Stacks Tag 09AL (Lemma 61.27.4): for a scheme and Noetherian
coefficient ring, inverse image gives an equivalence on constructible bounded-below
derived categories. The node's finite-ring and bounded-interval specialization, together
with its global finite-stratification convention, is the statement being rendered here.

The node's objects, hypotheses, and conclusion clauses match as follows.

1. The arbitrary scheme and coefficient data are `(X : Scheme.{u})`, `(B : Type u)`,
   `[CommRing B]`, and `[Finite B]`. The Lean has no field, nonzero, Noetherian,
   separated, characteristic, DVR, uniformizer, or quotient-of-a-DVR hypothesis.
   The `ULift.{u + 1, u} B` in the etale module category is only the recorded
   universe transport. The small etale and small pro-etale sites are rendered by
   `X.smallEtaleTopology` and `Scheme.ProEt.topology X` through the recorded module
   categories.
2. The specified inverse image is the canonical
   `ProEtale.finiteCoefficientIntrinsicDerivedComparison X B`, whose construction in
   `ProEtaleFiniteModuleIntrinsicComparison` is the recorded comparison followed by
   associated-module sheafification along the constant-scalar unit. It is therefore
   the repaired intrinsic presentation of the dependency's exact inverse image, not an
   arbitrary equivalence or a chosen map.
3. The source subcategory is exactly the full subcategory selected by
   `Etale.DerivedCategory.isBoundedConstructible (ULift B) X`; this uses the recorded
   etale constructible-sheaf predicate and an existential finite interval. The first two
   conjuncts, `.Full` and `.Faithful` of the inclusion followed by the comparison,
   express the full-faithfulness part of the claimed equivalence.
4. For each target `K : proEtaleDerivedCategory X B`, the `essImage` biconditional
   says precisely that every cohomology object of
   `proEtaleRingModules X (proEtaleConstantRing X B)` is
   `IsConstructibleProEtaleModuleSheaf X B` and that some `a ≤ b` annihilates all
   degrees outside `[a,b]`. Since `Functor.essImage` is the existence of a source
   object and an isomorphism from its image, this is exactly the etale-origin and
   boundedness clause of the node.
5. The final universal clause quantifies over every etale derived object `L` and every
   pair of integers `a b`; it gives the biconditional between vanishing of the etale
   cohomology outside `[a,b]` and vanishing of the comparison's pro-etale cohomology
   outside that interval. This is the node's preservation and reflection clause.

No mismatch was found in the item statement, quantifier order, coefficient categories,
or conclusion strength. The sandbox node correctly includes the already recorded
`def-weil-pbc-constructible-complexes` dependency used by the source subcategory.
The dependency repair for `def-weil-pbc-proetale-modules` supplies the intrinsic
constant-ring comparison and real sheafification data. The constructibility dependency
retains the explicit constructible-strata conjunct; `Topology.Stratification` already
inherits `isConstructible_stratum`, so this conjunct is redundant in the current
library but is faithful to the node and was retained. The earlier duplicate
`finiteCoefficientIntrinsicScalarMap_locallyBijective` theorem is absent: the module
projects the existing `Scheme.proEtaleConstantRingUnit_locallyBijective` theorem.
No statement correction, citer audit, or STATEMENT-DISPUTED marker is needed.

Edge cases checked: the zero finite ring and zero complexes are admitted; the empty
scheme and empty strata remain allowed; `a = b` gives the single-degree case; `a > b`
gives the acyclic case in the final universal clause; the essential-image existential
still requires `a ≤ b`; negative bounds and arbitrary shifts are allowed; and each
cohomology degree may use its own finite stratification. No independent test-object or
index universe is introduced.

Reuse searches were checked again with exact-name and item-id `rg` searches over the
project and slopmaster2 source, plus the recorded LeanFinder, Loogle, grep, and
LeanSearch queries in `searches.jsonl`. They found no existing derived-origin statement
or intrinsic pro-etale comparison. LeanSearch remains unavailable; Loogle's query
reports its unknown identifier rather than a theorem match. The only reused declarations
are the recorded bounded constructibility predicate, cohomology functor, comparison
infrastructure, existing scalar-unit local-bijectivity theorem, and the two dependency
definitions listed above.

All three files were compiled separately in dependency order with the prescribed
`scompile.py` wrapper, and also in one combined invocation. Each completed with no
diagnostics within the 60-second limit. The theorem signature remains verbatim equal to
the node's `lean.statement`; every postponed assertion has a source and blueprint
docstring, and no hollow definition was introduced.
