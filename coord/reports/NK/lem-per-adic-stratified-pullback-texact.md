## Worker report

Item: `lem-per-adic-stratified-pullback-texact`; group NK; 2026-10-21 UTC.
Module: `Sheaf.Paper.PerAdicStratifiedPullbackTExact`.
Main declaration: `AlgebraicGeometry.Scheme.perAdicStratifiedPullbackTExact`.
This is stage 2: its only theorem has proof `sorry`. The auxiliary structures package
this theorem's simultaneous assertions; none is chosen to manufacture a mathematical
object. The coefficient map and geometric bundle contain actual data, and `free` is
only an abbreviation of Mathlib's free module sheaf.

Read the node, all statement-dependency statements and records, the recorded interfaces,
coord/brief-stage2.md in full, stages/2-statements.md, delivery-errors.md H, the worker
role, SETUP/GOAL/STATE, tools/README and the withdrawn CompactObject example. There is
no repair-note JSON for this item; this packet repairs the independent return at head
`746b5293073b` (H13/H2 and H3). Source read: Bhatt--Scholze PDF, Lemma 6.8.2,
Definitions 6.8.6/6.8.8, Proposition 6.8.14 and Remark 6.8.15, and the current
main-20261015 blueprint proof of lem-per-smooth-pullback-t-exact, first paragraph.
The latter explicitly uses exact ordinary pullback on cohomology. The module docstring
copies all nine DAG proof steps, including their cited nodes, for stage 3.

Hypotheses, objects and conclusions, clause by clause:

* `k : Type u` with `[Field k]` is the base field. `l : ℕ`, `[Fact l.Prime]`
  and `_hl : IsUnit (l : k)` state exactly the prime and invertibility hypotheses.
* `X Y : Scheme.{u}`, their `Over (Spec (CommRingCat.of k))` instances, and
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on each structure map give
  precisely the two separated finite-type schemes. `g : Y ⟶ X` is arbitrary;
  it is not required to commute with the maps to the base field, to be smooth,
  flat, surjective, nonempty, or of any positive relative dimension.
* `Ω : Type v`, `Field Ω`, `Algebra ℚ_[l] Ω`, `IsAlgClosure ℚ_[l] Ω` give the
  fixed algebraic closure, in an independent universe. Finite intermediate fields
  and every inclusion are `Padic.FiniteCoefficientFields l Ω` and `A ≤ B`.
  The published `pbcFiniteField.{u}` supplies their existing small presentations;
  no equality of the scheme and algebraic-closure universes is imposed.
* Integral coefficients are `pbcIntegralDatum l A`, `pbcAdicCompletion` and
  `pbcUniformizer`, used inside the existing integral and rational categories.
  These contain the actual valuation ring, chosen uniformizer, positive quotient
  tower, completed coefficient sheaf and raw localization, not an arbitrary ring.
* Noetherianity, finite dimension and stalkwise invertibility appear as the six
  initial existential conclusions, not added assumptions. `StratifiedAdicPullback.base`
  bundles precisely these conclusions for `ContinuousRational.Base`.
* `GlobalCalculation.integral` says the actual `pbcActualCompletedPull g` carries
  every object of `PbcBoundedConstructibleComplete` into the same target category.
  Its predicate is the conjunction of intrinsic completeness, uniformly bounded
  constructible reductions and compatible etale-origin witnesses, so the last
  witnesses and their quotient compatibility are not discarded.
* The rational finite-stage functor is literally `(pbcQbarPullFamily l Ω g).Φ A`.
  The recorded family's existence/uniqueness specification fixes this to
  `pbcDescentPullback`, the raw rationalization of the integral restriction,
  and fixes its beta by `PbcPullbackBetaSpec`. Its common functor is literally
  `pbcQbarCompletedPull`, the existing descent with the prescribed object and
  common-stage conjugation formula. There is no arbitrary functor parameter.
* `tX` and `tY` use the recorded `AdicCommonStageTruncations` interface.
  `GlobalCalculation.standardX` and `.standardY` fix both finite-stage halves at
  every integer to the isomorphism closures of the corresponding integral halves.
  The main theorem fixes their common structures by equality to `pbcQbarStandardT`.
  Thus existential t-structures cannot substitute unrelated structures.
* `.integralShift` is on the actual integral restriction `pbcConditionalIntegral`
  of `pbcActualCompletedPull`, with its existing preservation certificate
  `pbcQbarIntegralPull_mem`. `.integral_shift` fixes its components, after the
  full-subcategory inclusion, to the canonical ambient completed-pullback shift.
  `.finite_fraction` uses `CoefficientStageDescent.FractionExtension` on that
  exact integral functor and the specified rational `Φ A`: its `factor_id`
  fixes the comparison to the identity and its `factor_shift` forces the rational
  shift to be the localized integral shift. `.common_shift` is exactly the
  descent theorem's HEq equation at every finite-stage image and every integer.
  Hence `.finiteShift` and `.commonShift` are now pinned, and `.finite.exact`,
  `.common.exact`, `q_formula` and `scalar_shift` use these compatible shifts.
  The triangles and category instances are the existing ones.
* The family beta maps already carry the associator composition equation in
  `StageSystem.Morphism.coh`; their integral scalar normalization is fixed by
  `pbcQbarPullFamily_existsUnique` and `PbcPullbackBetaSpec`. `.scalar_unit` writes
  the repeated-field identity explicitly; `.scalar_shift` adds the shift equation.
  The ambient completed integral scalar comparisons, scheme-identity/composition
  comparisons and coefficient-tower equations are those of PbcScalarExtension,
  retained by the normalized pullback family, not new existential comparisons.
* At a finite field `E : Type u`, the local assertion quantifies over every
  normalized `ContinuousRational.Family` and every `K` with `J_X(K) ≅ F[0]`.
  This expresses `J_X^{-1} F` without choosing an arbitrary inverse representative.
  `ContinuousRational.IsConstructible` is the recorded sheaf predicate, via the
  realization's normalized coefficient encoding. The quantification is over every
  finite field model, not only a particular subfield presentation.
* `S : Scheme`, `i : S ⟶ X`, `IsImmersion i`, and finite local freeness of
  `(ContinuousRational.modulePull i (coefficient l E i)).obj F` express any
  locally closed stratum with a locally finite free restriction. No nonempty or
  reduced stratum hypothesis is inserted.
* The restriction of `J_Y(Lg* K)` is `ContinuousRational.derivedPull (pullback.fst g i)`
  over the canonical continuous coefficient map. `IsLE 0 ∧ IsGE 0` asserts that
  it is concentrated in degree zero, on the actual fibre-product stratum.
* For every chart `U : S.ProEt` and every rank `r : ℕ`, the antecedent is exactly
  a trivialization of `F|_U` by the existing finite free continuous module.
  The pulled chart is `pullback U.hom (pullback.snd g i)`, canonically
  `U ×_S (Y ×_X S)`. Its map to Y is `pullback.snd ... ≫ pullback.fst g i`.
  The final isomorphism identifies the restriction on this chart with the target
  continuous free module of rank r in degree zero. These ambient functors require
  no Noetherianity or finite-dimensionality instance on U or its pullback.
* `FreeCalculation.ordinary` is the balanced tensor identification for the free
  chart model. `.basis` fixes it on `a • (1 ⊗ e_j)` as `a • e_j` at every
  base-changed site object. Linearity, additivity and balancing give the displayed
  formula on a general finite vector; invertibility fixes the inverse by inserting
  the basis vector. `.normalized` and `.universal` fix the computation counit;
  `.computes` and `.derived_formula` identify the derived map with precisely this
  ordinary map in degree zero. No flatness instance on the structural ring map
  is assumed. `coefficient` is constructed from the existing continuous-map
  pullback with the finite extension's norm, not chosen from existence.
* `.finite.tExact` and `.common.tExact` preserve both halves at every cutoff.
  Their `.heart`, `.heartAdditive` and `.heartExact` assert preservation and exactness
  of the actual restriction to the heart. `.finite_interval` and `.common_interval`
  explicitly preserve every pair of bounds, with no `a ≤ b` restriction.
* The `CoefficientStageDescent.Comparisons` fields `.le` and `.ge` are the two
  canonical truncation comparisons; `.le_counit`, `.ge_unit`, `.le_unique`,
  `.ge_unique` fix their normalization. `.q` is the natural cohomology comparison,
  with `.q_formula` fixing its composite from truncations and integer shift.
  Inverting its components gives exactly `H^j(Lg* K) ≅ g* H^j(K)`.
* `.scalar_square` uses the existing `SquareCompatible` predicate for the actual
  beta and the canonical scalar-extension comparisons. Its three equations are
  precisely compatibility for upper truncation, lower truncation and cohomology.
  Equal finite fields are included.

Dependency interfaces used (source modules read, with their signatures/docstrings):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its public coefficient extension
  ring of integers, uniformizer and finite quotients.
* `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.completedReductionTower` and the
  completed quotient-coefficient constructions. The positive index is n+1.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, the weakly etale
  small site, object universe u+1 and morphism universe u.
* `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete`
  and the public `PbcBoundedConstructibleComplete`/`PbcIsBoundedConstructibleComplete`
  used by the other recorded dependencies, including all three witness conditions.
* `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory`,
  `PbcRationalCategory`, `pbcRationalization` (raw scalar localization).
* `Sheaf.Paper.LocalizedTStructure`: `pbc_localized_tstructure`; its two image
  classes are rendered by `standardX`/`standardY` using the common-stage interface.
* `Sheaf.Paper.IntrinsicQbarCategory`: its public import of
  `Sheaf.Paper.PbcQbarCategory` retains `pbcQbarCategory`, the completed-stage pair
  type already used by `pbcQbarStandardT` and `pbcQbarCompletedPull`. NM's module,
  file, primary declaration and all eight recorded declarations are retained
  byte-for-byte in the dependency record.
* `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension`, normalized
  scalar transitions and associators, and completed-pull scalar comparisons.
* `Sheaf.Paper.PerAdicCommonStageTruncations`:
  `perAdicCommonStageTruncations`, `StageSystem.AdicCommonStageTruncations`.
* `Sheaf.Paper.PbcQbarCompletedPullback`: `pbcQbarCompletedPull`,
  `pbcQbarPullFamily`, `pbcQbarPullFamily_existsUnique`, `pbcQbarIntegralPull_mem`.
* `Sheaf.Paper.ContinuousRationalDerivedRealization`:
  `ContinuousRational.continuous_rational_derived_realization`, `Family`, `At`,
  `Along`, `modulePull`, `moduleUnit`, `derivedPull`, `IsNormalizedPullCounit`.
* `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`. Degree-zero images use `singleFunctor`;
  the generic recorded comparisons express cohomology inside the heart.
* Proof interface `Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent`:
  `texact_coefficient_stage_descent`, `Comparisons`, `SquareCompatible`.
* `Sheaf.Paper.ContinuousCoefficientSliceNormalization`:
  `ContinuousSlice.continuous_coefficient_slice_normalization`, with exact slice
  module restriction and normalized coefficient/ambient comparisons on arbitrary U.
  All other stated proof-dependency modules are imported privately as the stage-3 plan.

Searches actually run:

* msearch leanfinder: “Completed pullback of constructible adic sheaves preserves
  standard t structure and finite free sheaves on strata”. Eight hits: ordinary
  sheaf free pullback (pullbackObjFreeIso, freeFunctorCompPullbackIso), scheme
  module pullback, solid modules. No exact adic completed assertion.
* msearch loogle: “Functor.IsTExact, TStructure”. Zero hits, unknown identifier
  Functor.IsTExact; this failed name query was not counted as a theorem match.
* msearch grep: “completedPullback|pbcQbarCompletedPull|stratified.*pullback”.
  Zero Mathlib hits.
* msearch leansearch: “Derived pullback on constructible adic categories is t-exact”.
  Eight hits for ordinary sheaf pullback/adjunctions and categorical pullback
  exactness. No completed constructible adic statement.
* rg in lean/WeilConjectures and lean/Sheaf for stratifiedPullback,
  stratified_pullback, adic pullback, and the exact item id; the item has no
  existing declaration. Upstream Adic.Constructible/Truncation concern the other
  adic sheaf realization; the former parent AdicHeartPullbackFibres additionally
  bundles point-fibre statements and does not state this split node's normalized
  continuous local formula. Neither is an exact existing match.
* Read Mathlib Sheaf.Free and Homology.Additive: reused `SheafOfModules.free`,
  `freeSection`, `HomologicalComplex.singleMapHomologicalComplex`.
* Read both Qbar interfaces and their stage definitions before the record repair.

Edge cases checked before and after writing:

* Empty X, Y and strata are permitted; no point or nonemptiness witness is bound.
* Rank zero uses the free sheaf on `ULift (Fin 0)`, hence zero; basis normalization
  quantifies over the empty set and the isomorphism asserts the zero calculation.
* No positivity condition on rank and no constant global rank are imposed.
* Empty cohomological intervals a>b are still quantified; both bounds force zero.
* g=id, arbitrary immersions, and non-flat coefficient structural maps remain in scope.
* All integer cutoffs and cohomology degrees, including negative degrees, are quantified.
* All finite-field inclusions include the identity; the unit equation is explicit.
* Charts may be non-Noetherian, and may have empty base change. No bound on their
  size, topological dimension or flatness of their coefficient map is requested.

Compilation uses only the prescribed scompile.py, under the unchanged 60-second
per-file limit. The initial sandbox-name and library-name passes were clean. After a later
import change the file reached the limit, so repeated elaboration was reduced
without changing the mathematical clauses. Final delivery validation is recorded below. The
scoped heartbeat budgets control elaboration steps only, not the time limit.
No theorem was proved and no target/node statement was changed. No disputed statement.

## Dependency modules

There is no dependency-interface replacement in this repair. The sandbox copy of
`def-weil-pbc-qbar-category.json` is restored byte-for-byte from the current live
read clone. In particular its `lean` remains NM's `IntrinsicQbarCategory` module,
`existing: false`, the original file and all eight declarations. The module
publicly imports `PbcQbarCategory`; importing that recorded module gives this
item the exact `pbcQbarCategory` interface used by its other dependencies. The
item continues on that category. The previous claim that NM's record had to be
replaced was incorrect, as the independent return explains.

## Second reading by NK

Second pass by the assigned dispatcher worker, with the final Lean module and node
open; the dispatcher's explicit prohibition on starting other agents is respected.
The maintainer supplies the independent delivery review.

Matched the six scheme properties, prime/unit hypotheses, and arbitrary g against
all binders. Verified that the Noetherian, dimension and stalk-unit facts are
conclusions. Compared the source formula `f_naive* K tensor Λ_Y` with the actual
coefficient map and `ContinuousRational.derivedPull`; no coefficient isomorphism
or flatness is assumed for g. Checked the pullback chart projections explicitly:
its first projection goes to U, and its second followed by pullback.fst goes to Y.
Checked that the finite free output ring is on that chart, not on S or X.
Checked the zero-rank and empty-stratum quantifiers directly in LocalCalculation.

Found and fixed during this pass: the initial global package did not fix its
existential finite t-structures to the localized standard halves. Added
`standardX` and `standardY`, both le and ge at every integer, exactly matching the
integral-image characterization in the dependency. The common t-structures are
also fixed by equality to pbcQbarStandardT. The canonical Comparisons fields give
heart exactness and normalized cohomology, and scalar_square refers to the beta
of the specified actual family. Read the Qbar dependency source and retained NM's full
record and public reexport, as described above.

Confirmed that FreeCalculation's ordinary isomorphism is basis-normalized, its
computation counit is normalized and universal, and derived_formula fixes the
derived free-module identification. All helper data are real constructions or
fields of the theorem's assertion record; no hollow data definition was introduced.
Verified the stored theorem signature is copied verbatim, every declaration has a
source/blueprint docstring, the proof docstring has all nine steps, and no Lean
line exceeds 100 characters. The independent return subsequently identified the
unconstrained shifts; the repair reading below fixes that mismatch.

## Returned delivery repair

The saved packet first passed the required dry run (commit `f3491702950`), but
that mechanical success did not discharge the return's mathematical findings.
Both findings have substantive repairs:

* H13/H2: restored the Qbar dependency JSON exactly as live, preserving NM's
  module, file, `existing: false` and every one of its eight declarations.
  The item publicly imports `IntrinsicQbarCategory` and still uses the legacy
  `pbcQbarCategory` already shared by its standard t-structure and pullback.
* H3: added `integral_shift`, `finite_fraction` and `common_shift` to the
  assertion package. Read the full `FractionExtension` signature and the
  conclusion of `texact_coefficient_stage_descent` in
  `Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent`. The former's
  `factor_shift` fixes finite rational shifts through the identity-normalized
  factorization; the latter's HEq clause is copied at the common-stage level.
  The additional integral HEq fixes the restriction shift to the ambient
  `pbcActualCompletedPullShift`, itself the composite of the existing normalized
  derived-pull and completion shifts. No arbitrary functor, category, comparison
  or scalar action replaces a canonical construction.

Removed the advisory unused public import `Indization.LocallySmall`.
Rechecked zero shifts and negative shifts (all n : ℤ are included), equal fields,
zero objects, empty schemes/strata, rank zero, and empty intervals. The new shift
clauses apply uniformly in each case and introduce no extra hypotheses on the
main theorem. Its signature and the node statement are unchanged. The packet
changes only the item's `lean` record; the restored dependency has no live delta.

The repair reading compared the full GlobalCalculation fields with the node:
canonical integral restriction -> identity-normalized fraction extension ->
common-stage shift equation -> exactness and canonical cohomology. This closes
the exact gap reported at head `746b5293073b`. There are no new definitions or
nodes, no additional postponed theorem, and still exactly one theorem with
`sorry`, `AlgebraicGeometry.Scheme.perAdicStratifiedPullbackTExact`.

Repair validation: the prescribed scompile.py compiled the delivered module both
as `Sheaf.Stage2.Sandbox0` (46.7 seconds) and under its library module name
(43.6 seconds), cleanly within the unchanged 60-second limits. The explicit
self-check confirms that the dependency JSON is byte-for-byte equal to the live
copy, all Lean lines are at most 100 characters, and lean.statement equals the
main theorem signature verbatim. The dry run and push run provide the final
server preflight and compilation verification.
