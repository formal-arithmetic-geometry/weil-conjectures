## Worker report

This delivery states lem-sf-open-exchange-roos-restriction in
`Sheaf.SixFunctors.OpenExchangeRoosRestriction`. The principal theorem is
`WeilConjectures.OpenExchangeRoos.openExchangeRoosRestriction`. All theorem proofs
are postponed with `sorry`. Definitions contain actual constructions, not postponed
data. The subsidiary theorems are the finite, product, signed-Roos, and limit
normalization clauses of this same DAG node. Two existing-interface definition nodes register the already published constructions.
No Lean construction is duplicated and no dependency record is replaced.

### Hypotheses and objects

* The fixed algebraic closure of a finite field is `F : FiniteFieldDatum.{u}`.
  The schemes are objects of `Over (Spec (.of F.k))`; the four arrows are arrows
  of that over-category, so they are morphisms over this fixed field.
* The prime is `l : ℕ` with `[Fact l.Prime]`, and `_hl : l ≠ F.p` is retained.
  The coefficient field is `E : Type u` with `[Field E]`, `[Algebra ℚ_[l] E]`,
  and `[FiniteDimensional ℚ_[l] E]`.
* The existing `pbcIntegralDatum l E` supplies the valuation ring, uniformizer,
  uniformizer ideal, positive quotients and completed coefficient sheaf. Its
  carrier is the existing ULift of the valuation ring. `generators` is exactly
  the singleton uniformizer tuple; `generators_span` states its ideal equality.
  Level `n : ℕ` in these APIs is the paper's positive level n+1.
* Its completed ring is the actual limit of finite constant coefficient sheaves.
  `ImmersionCompletedPullback.completedRingIso` fixes the comparison to the
  recorded integral presentation on every finite projection. `complete` is
  precisely `IntegralOnSlice.IsComplete ... none` after its exact `transport`.
  It is not intrinsic completeness substituted without a comparison theorem.
* `d.derived W` is the ordinary unbounded module derived category for
  `d = pbcIntegralDatum l E`. Neither K nor H is assumed bounded, constructible,
  torsion, perfect, or of finite Tor amplitude. H ranges over the full subcategory
  given by `complete`; K is arbitrary in `d.derived U` subject only to `complete`.
* All four schemes are finite type: `[LocallyOfFiniteType W.hom]` and
  `[QuasiCompact W.hom]`. The arrows j and j' have their open-immersion instances.
  `sq : OpenImmersionSquare ...` is the recorded Cartesian square, including its
  commutativity and pullback identification. The extra j' instance is already
  part of that same square's open-immersion data.
* Quasi-compactness of j is not an added assumption. `finiteOpenQC` derives it
  from the finite-type Noetherian target, and the main theorem explicitly supplies
  that derived instance. Quasi-compactness of j' is supplied by the published
  pullback `cbcOpenMateQC`.

### Every conclusion and normalization

1. Open extension, restriction and the unit use `cbcDerivedOpenShriek`, `d.pull j`,
   and the actual `cbcDerivedOpenAdjunction`. `openUnit` is `asIso` of precisely
   that unit, using the published invertibility theorem; it is not a chosen iso.
2. The strict quotient tower and its canonical open scalar identification are
   the published `cbcOpenMateM`, `cbcOpenMateBeta`, `cbcOpenMateCompletedA` and
   `cbcOpenMateCompletedB`. Their construction uses the strict reductions and
   flat-term K-flat pullback models, with every transition retained. No arbitrary
   representative or arbitrary exchange is passed as an additional hypothesis.
3. `Assertion` first quantifies the restriction square c on complete objects.
   `Square` has source complete-objects inclusion followed by completed h-pullback
   and ordinary j'-restriction, and target inclusion followed by j-restriction
   and completed a-pullback. `SquareUnit` pins c on the *actual*
   `d.ordinaryToCompleted` arrows and the actual ordinary square compositor
   `cbcSquarePull`. The unique-existence binder records the canonical comparison
   determined by this normalization, rather than assuming a comparison input.
4. For every complete K, the witness hI identifies the Roos-complete object with
   `cbcCompleteProperty` for the fixed uniformizer ideal. It is a conclusion,
   not a hypothesis. The hJ witness states completeness of j!K needed to evaluate
   c there. The next two conjuncts state completeness of both displayed exchange
   endpoints, in the same transported Roos predicate as K.
5. `IsIso ((cbcDatumCompletedExchange ...).app ⟨K,hI⟩)` is the specified exchange's
   invertibility. The following equality uses `cbcRealizationRes` on that very
   arrow, with `cbcOpenMateCompletedA/B` on its endpoints. Its right side is
   exactly the A-coordinate, then `completedRlim.map (cbcOpenMateBeta ...).hom`,
   then the inverse of `cbcRealizationOpenLimit`. Thus in fixed coordinates the
   specified Beta is lambda inverse after Rlim(b), in that order. Both endpoints
   and the scalar reduction identifications come from the published construction.
6. The last equality of `Assertion` is the actual restriction formula. Its left
   side is `d.pull j'` applied to the specified Beta followed by the inverse
   normalized j' unit. Its right side is c at j!K followed by completed a-pullback
   of the inverse normalized j unit. This is the node's Theta, with exactly the
   two stated open-unit identifications. `SquareUnit` is the accompanying
   restricted ordinary-to-completed unit compatibility, for every complete H.
7. `finite_restriction` states the simultaneous strict-system equation: restriction
   of the published `StrictTower.beta` equals `StrictTower.squareG`, then pullback
   of inverse source unit, then target unit. It quantifies a whole derived strict
   tower M, not independent finite evaluations. After these specified coordinates
   its map is the identity. The finite constant coefficient exchange and scalar
   compatibility are those of the recorded dependency.
8. `product_restriction` states the projection formula for every family of strict
   modules and every n. The two actual canonical `piComparison` maps are preceded
   by the actual unit; after the n-th projection the result is the original
   n-th projection followed by its unit. These jointly determine the identity
   comparison in open-unit coordinates.
9. `SignedComparison.coordinates` pins its iso on *both* signed summands to these
   canonical product comparisons, using the published `strictRoosCoordinates`.
   `roos_restriction` supplies those comparisons and states that their restricted
   composite is exactly `integralOperationsRoosMap` of the termwise open unit.
   This is equality of chain maps, not an assertion about derived evaluations.
   The coordinate order in the published API is (y,x), so its augmentation is
   (0,gamma), which is the paper's (gamma,0) after the recorded braiding. Equality
   of the full chain maps includes every strict augmentation.
10. `constantOpenAdjunction` is the actual module adjunction descended to derived
    categories with its canonical right-derived comparison. `limit_restriction`
    compares the actual `cbcRealizationOpenLimit` and canonical constant-diagram
    mate `cbcRealizationLimitMap`: their restricted composite is Rlim of the
    simultaneous strict open unit. The normalized strict-Roos/Rlim comparison
    identifies this with items 8--9 and preserves augmentations. Together with
    `SquareUnit`, this retains the actual completion units. No faithfulness of
    separate reductions is assumed or used.

### Dependency declarations

All original statement dependencies are reused. Their recorded modules are imported;
proof dependencies with published modules are also imported. The underlying scheme
properties use Mathlib's existing `LocallyOfFiniteType`, `QuasiCompact` and
`IsOpenImmersion`, not a new definition.

* `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
* `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
* `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
* `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
* `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
* `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
* `lem-pur-site-restriction-module-adjunction-exact`: `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, `SheafOfModules.localizedSystemExact`.
* `def-cbc-open-immersion-square`: `Sheaf.AlgebraicGeometry.OpenImmersionSquare`, `AlgebraicGeometry.OpenImmersionSquare`.
* `def-weil-scheme-morphism-properties`: `None`, `None`.
* `def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteOnSlices`, `WeilConjectures.IntegralOnSlice.IsComplete`.
* `def-weil-integral-reduction-tower`: `Sheaf.Paper.IntegralReductionTowerCanonical`, `WeilConjectures.canonicalIntegralReductionTower`.
* `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`.
* `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
* `lem-pc-kflat-resolution`: `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
* `lem-cbc-exact-product-functor-strict-limit`: `Sheaf.Paper.ExactProductFunctorStrictLimit`, `CategoryTheory.exactProductFunctorStrictLimit`.
* `def-weil-pbc-completed-pullback`: `Sheaf.Paper.PbcQbarCompletedPullback`, `AlgebraicGeometry.Scheme.pbcQbarCompletedPull`.
* `lem-cbc-finite-open-exchange-scalars`: `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`, `AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars.exchange_restrictScalars`.
* `lem-sf-integral-open-reduction-comparison`: `Sheaf.SixFunctors.IntegralOpenReductionComparison`, `WeilConjectures.IntegralOpenReduction.integralOpenReductionComparison`.
* `lem-cbc-completed-extension-zero-comparison`: `Sheaf.Paper.CompletedOpenExchangeTransport`, `AlgebraicGeometry.Scheme.completedOpenExchangeComparison`.
* `lem-weil-pbc-proetale-derived-pullback-composition`: `Sheaf.Paper.IntegralFinitePullbackComposition`, `WeilConjectures.integralTowerGeneralPullbackComposition`.
* `def-sf-pull-completion-comparison`: `Sheaf.SixFunctors.OpenFactorPullModel`, `WeilConjectures.OpenFactorCoherence.Pull`.
* `lem-cbc-adic-pullback-presentation-transport`: `Sheaf.Paper.AdicPullbackPresentationTransport`, `AlgebraicGeometry.Scheme.adic_pullback_presentation_transport`.
* `lem-cbc-completed-ring-strict-finite-exchange`: `Sheaf.Paper.CompletedRingStrictFiniteExchange`, `AlgebraicGeometry.Scheme.completedRingStrictFiniteExchange`.
* `lem-cbc-ringed-open-extension-products`: `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts`, `AlgebraicGeometry.Scheme.proEtaleRingedExtensionByZero_products`.
* `lem-cbc-ringed-open-flat-resolution`: `Sheaf.Algebra.Homology.RingedOpenFlatResolution`, `SheafOfModules.ringedOpen_preserves_flat_resolution`.
* `def-a1-integral-completed-pullback-interfaces`: `Sheaf.Paper.SfImmersionCompletedPullbackComparison`, `AlgebraicGeometry.Scheme.ImmersionCompletedPullback.completedRingIso` and `transport`. The immersion comparison theorem stays in proof dependencies.
* `lem-sf-open-roos-unit-adjunction`: no declaration is required by this statement; this is a proof-only dependency (or the scheme-properties umbrella). It is not introduced as a premise.
* `lem-sf-open-tensor-normalization`: `Sheaf.SixFunctors.OpenTensorNormalization`, `SheafOfModules.openTensorNormalization`.
* `lem-weil-pbc-right-adjoint-preserves-limits`: existing Mathlib match `{'declaration': 'CategoryTheory.Adjunction.rightAdjoint_preservesLimits', 'file': 'Mathlib/CategoryTheory/Adjunction/Limits.lean', 'how': "exact: for adj : L ⊣ R, `PreservesLimitsOfSize.{v, u} R` for every universe pair (line 207, tagged @[stacks 0038]), so `isLimitOfPreserves R hc` makes the image of a limit cone a limit; the finite-product case is `PreservesFiniteProducts R` (instance from PreservesFiniteLimits, Limits/Preserves/Finite.lean:113), with `CartesianMonoidalCategory.prodComparison R Y Y'` an isomorphism (`isIso_prodComparison_of_preservesLimit_pair`)"}`.
* `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
* `lem-weil-proetale-countable-products-exact`: `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`, `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`.
* `lem-weil-strict-roos-comparison`: `Sheaf.CategoryTheory.StrictRoosComparison`, `CategoryTheory.strictRoosComparison`.

The added statement dependencies are definition nodes:
`def-sf-completed-open-strict-mate-data` owns the existing `cbcOpenMate*` data in
`Sheaf.Paper.CompletedOpenStrictMateIdentification`, and
`def-sf-strict-roos-coordinate-interface` owns the existing `strictRoos*` coordinate
interface in `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`.
`def-a1-integral-completed-pullback-interfaces` owns the projection-normalized
`ImmersionCompletedPullback.completedRingIso` and `transport` actually used here.
`def-weil-pbc-bounded-constructible-complete` supplies `pbcIntegralDatum` through
`Sheaf.Paper.BoundedConstructibleComplete`; its bounded-constructible predicate is
not imposed. `def-pur-completed-rlim-functor` supplies the actual `completedRlim`.
The two theorems `lem-cbc-completed-open-strict-mate-identification` and
`lem-sf-strict-roos-derived-limit-comparison` are proof dependencies only.
No `.choose` of either theorem supplies any object in this statement.

The return's advisory base-era definitions are used as published:
`cbcDerivedOpenAdjunction`, `cbcSquarePull`, and `cbcOpenUnit_isIso` in
`Sheaf.Paper.CompleteCompactSupportProetale`; `cbcRealization*` in
`Sheaf.Paper.CompleteProetaleStrictTowerRealization`; and
`integralOperationsRoosMap` in `Sheaf.Paper.IntegralOperationsWellDefined`.
Their existing defining interfaces are retained. The completion-ring transport
itself uses the uniquely projection-normalized `completedRingIso_exists`, which is
owned by the live interface node, rather than inferred from the immersion theorem.

### Sources and searches

Read the actual source text: Stacks `proetale.tex`, lemma-pushforward-Noetherian-case
(Tag 099N), especially (2),(5), and lemma-open-immersion (09BN);
`sites-cohomology.tex`, lemma-derived-pullback-composition (0D6D).
Read the current blueprint `main-20261015` proof of `sk-prop-sf-pf-coherence`,
particularly its open-factor/base-change paragraphs. The nine-step natural-language
proof in the main theorem docstring follows the DAG's proof and explains the
canonical strict maps, scalar identifications, signed summands and unit equation.
Every postponed helper theorem also has its source and complete natural-language
proof in its own docstring, carrying this node's blueprint identifier.

Actual discovery searches (msearch output is also in sandbox searches.jsonl):

* LeanFinder: “Restriction of completed open base change exchange via derived
  inverse limit Roos model preserves completion units”; eight unrelated adic
  completion results, no exact match (query repeated once).
* Loogle: `CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.Adjunction.unit`;
  no result. `CategoryTheory.Adjunction.unit`; twelve generic unit results,
  none the required strict completed exchange assertion.
* Mathlib grep via msearch: `Roos|roos` in CategoryTheory; no match.
* LeanSearch: “exact functor commuting with countable products commutes with
  homotopy inverse limits”; eight generic ExactFunctor results, no exact match.
* rg in project `WeilConjectures` and `Sheaf` for the item identifier, Roos,
  completed exchanges, restriction and normalization: no existing declaration of
  this entire assertion. Found and reused the strict completed-mate endpoint
  construction, the coefficient transport, actual strict exchanges, and the
  signed-Roos coordinate API. The downstream OpenFactorCoherence assertion is
  restricted to a constructible domain and is not imported or substituted.
* Read the full recorded signatures/docstrings of statement dependencies; the
  Mathlib site, module category, derived category and adjunction-limit definitions
  are used as recorded. Generic right-adjoint preservation of limits is the
  recorded `Adjunction.rightAdjoint_preservesLimits` (Tag 0038).

### Edge cases and validation

Checked mathematically before finishing the signature: zero K and zero systems;
empty open and empty schemes; identity open and identity/arbitrary remaining
scheme maps; first positive quotient (Lean n=0 means exponent 1); arbitrary
unbounded complete complexes. Finite type supplies the quasi-compactness used by
the exact-product comparison even for the empty open. No hypothesis of product
preservation is imposed on a or h: only exact open extension/restriction need it.
The coefficient inverse-image comparison is the published canonical comparison,
not an additional invertibility assumption on the user's input. No pointwise
finite-reduction faithfulness or boundedness restriction was inserted.

The file was compiled using the prescribed server scompile.py wrapper. All
variables and universes are explicit, with `autoImplicit false`. No proof other
than `sorry` was supplied. No node statement, proof, source, or status was changed;
only the lean record, definition-node statement dependencies, and the two required
comparison proof dependencies were added.
No STATEMENT-DISPUTED flag and no statement correction.

## Second reading by Q21

This is the author's separate rereading with the node and final file open. The
dispatcher explicitly prohibits starting other agents; the maintainer supplies
the independent review. No independent worker review is claimed here.

Rechecked each hypothesis and each numbered clause against the source: finite field,
prime exclusion, finite coefficient extension, finite-type Cartesian square,
Roos-complete unbounded K; the actual Beta, fixed endpoint identifications,
completeness, the ordered Rlim formula, restriction Theta, unit square, simultaneous
finite identity, every product projection, both signed summands and augmentations.
The rereading found and removed an unnecessary quasi-compactness input from the
main theorem, replacing it by the named finite-type consequence `finiteOpenQC`.
It also made both signed coordinates and the derived-limit unit equation explicit
instead of relying on prose alone. The square uses the actual quotient completion
unit and ordinary compositor, and the final restriction equation uses the actual
open adjunction units on each side. All definitions have real data. The two new existing-interface nodes were also reread against their full published
signatures and definitions: neither invokes the comparison theorem to construct its
data. No dependency-module repair is needed.


## Returned H2 repair

The immutable returned head was cab34a758f38. The saved packet initially passed
`deliver2.py --no-push` at 985d06369ef; that mechanical success did not resolve the
independent review's dependency-ownership fault. This repair changes the packet:

* Replace added statement dependency
  `lem-cbc-completed-open-strict-mate-identification` with
  `def-sf-completed-open-strict-mate-data`, an existing:true ownership record on
  the exact plain definitions `cbcOpenMate*` in the published module.
* Replace added statement dependency
  `lem-sf-strict-roos-derived-limit-comparison` with
  `def-sf-strict-roos-coordinate-interface`, an existing:true record for the five
  plain `strictRoos*` constructions. It explicitly cites
  `def-weil-strict-roos-model` for the same underlying construction with the
  published `roosP`/`roosU`/`roosF`/`roosχ` interface; no second Lean definition is made.
* Replace added statement dependency
  `lem-sf-immersion-completed-pullback-comparison` with the live existing:true
  `def-a1-integral-completed-pullback-interfaces`, whose declarations are exactly
  the projection-normalized coefficient comparisons and transport used here.
* Keep the strict-mate and strict-Roos comparison theorems in proof_deps, and cite
  the live `def-pur-completed-rlim-functor` as advised for `completedRlim`.

The item's Lean file is unchanged. Its natural-language statement and proof remain
verbatim. All original statement and proof dependencies are retained. The repair
adds no hypotheses, changes no mathematical conclusion, and creates no construction
from an unpinned existence theorem. No STATEMENT-DISPUTED flag or statement correction.

## New nodes

`def-sf-completed-open-strict-mate-data` records the existing source and target
strict towers, actual strict exchange, constant-scalar reduction tower, the two
constant endpoints and their strict mate, base-changed quasi-compactness, and the
two specified completed endpoints (`cbcOpenMateSource/Target/Omega/M/N/N'/A/B/Beta/
QC/CompletedA/CompletedB`). Its source is the blueprint open-factor base-change
paragraph, Stacks 03DI and 099N, and the actual published construction. It asserts
none of the strict-mate or completed-limit equalities. The search found these
exact declarations already in `Sheaf.Paper.CompletedOpenStrictMateIdentification`,
but no definition node owning them; the theorem node owns the comparison theorem.
The existing `def-cbc-completed-strict-open-exchange` supplies the underlying actual
exchange and is explicitly cited. No module or declaration is copied.

`def-sf-strict-roos-coordinate-interface` records the existing termwise product,
endomorphism 1-s, shifted cone, fixed signed coordinates and product map
(`CategoryTheory.strictRoosProduct/Endomorphism/Complex/Coordinates/ProductMap`).
Its source is Stacks 08TC and the actual strict cone-coordinate definitions, with
0941 as the strict realization context. It requires an abelian category with
countable products, with no exact-product or K-injective assumption. Searches
found `def-weil-strict-roos-model` for the same underlying construction under other
names; this node cites that owner and registers only the already-existing alternate
interface used by the consumer, as required by the return. It does not restate the
comparison theorem or introduce a new Lean notion.

For both nodes the recorded fresh searches are the actual `msearch.py` LeanSearch,
Loogle, and Mathlib grep results from this repair: eight generic cone/shift hits,
zero exact Loogle hits, and zero Mathlib identifier hits. Project rg located the
exact constructions in the two modules; no upstream WeilConjectures hit. The DAG
and `blueprint_refs.py` searches located the related owners above, but no definition
node for the exact interfaces. The records retain the search output unchanged in
`mathlib_searches.results`. Zero towers, the first positive level n=0, arbitrary
integer degree p, identity open squares and the empty open all use the same data.
The full strict Roos source was additionally checked through `scompile.py --source`.


## Repair validation and tool failure

The unchanged main Lean module compiled cleanly through the prescribed
`scompile.py`: sandbox 12.7 s, library module 12.5 s. The repaired packet's
`deliver2.py --no-push` also compiled its main module and existing-declaration
probes successfully. The two definition records have verbatim primary signatures,
existing:true declarations in their actual owning modules, and exactly the cited
statement dependencies. A dependency traversal from each of the six newly cited
or reclassified interfaces/comparisons finds no path back to the item. Existing
unrelated graph cycles were not modified; no claim of global DAG acyclicity is made.

The repaired packet is not pushed because server preflight refused the explicitly
requested proof-dependency additions. Its exact diagnostic is:

> (b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

The item's statement has not changed; both comparisons were added only to
proof_deps, as the maintainer return requires. The wrapper explicitly permits
additions to proof_deps for a maintainer-return dependency-only repair, but server
preflight applies the older statement-correction gate. A fabricated mathematical
statement correction would misdescribe this repair. No tool was edited or patched,
and no authorized dependency addition was removed to bypass the refusal. The
complete repaired packet remains in the sandbox for a corrected gate.

## Repair retry validation (2026-10-21)

Inspected the retained packet and ran the prescribed `deliver2.py Q21
lem-sf-open-exchange-roos-restriction --no-push` before making any changes. It
again exited 1 with exactly the two preflight diagnostics quoted above. Compared
the packet with the current read-only repository node: the mathematical statement,
proof, and statement_change are unchanged (statement_change is absent on both).
Apart from lean, the only changes are the five added definition/interface
statement dependencies and the two return-required proof dependencies. Neither
dependency list drops a current-base dependency. The return-required new
existing:true definition records are retained, as is the live
def-a1-integral-completed-pullback-interfaces reference.

Confirmed by reading the unmodified delivery wrapper that its dependency-only
repair branch expressly permits these proof_deps additions while retaining the
natural-language statement. The server preflight nevertheless classifies the
packet as a statement correction and rejects those same additions. Removing the
required proof dependencies or inventing a mathematical statement correction
would not repair the maintainer's return. No launcher or project tool was edited,
patched, or bypassed, and nothing was pushed.

Re-ran the prescribed scompile.py on
lean/Sheaf/SixFunctors/OpenExchangeRoosRestriction.lean: exit 0, sandbox 12.7 s
and library module 12.5 s, with no compiler errors or warnings. The Lean file
remains unchanged as the return requires. Delivery remains blocked solely by
the reproduced server preflight refusal of this authorized dependency-only repair.

## Dispatcher repair retry (2026-10-21 14:37 UTC)

Started by inspecting the saved report and running the prescribed dry run on the retained packet, before any edit. The dry run again exited 1 with the same two server preflight diagnostics quoted above: proof_deps changed without a statement correction, and a missing Statement corrected section. No push was attempted.

Compared the saved node with the current shared read-only node using JSON reads, with no git command. The mathematical statement, proof, and absent statement_change are identical. The only proof_deps changes are additions of lem-cbc-completed-open-strict-mate-identification and lem-sf-strict-roos-derived-limit-comparison, exactly as the immutable-head return requires; none is removed. Both new existing:true definition nodes and the live def-a1-integral-completed-pullback-interfaces reference remain present.

Read the unmodified deliver2.py lines 133–140: the wrapper explicitly accepts these maintainer-return dependency-only proof additions without a mathematical statement correction. Its server preflight still rejects them. This is a tool refusal of the authorized repair; no mathematical correction, removal of required dependencies, tool edit, or bypass was introduced.

Recompiled the retained main file through scompile.py: exit 0, sandbox 12.7 s, library module 12.5 s, no errors or warnings. All repair files remain in the sandbox. Delivery is blocked only by the reproduced inconsistent preflight gate.

## Dispatcher repair retry (2026-10-21 14:44 UTC)

Inspected the retained report first and ran deliver2.py --no-push on the saved
packet. Repeated the dry run to capture its full diagnostic: exit 1, with the
same two server preflight failures, namely proof_deps changed without a statement
correction and no nonempty Statement corrected section. The mathematical
statement is unchanged, so adding such a section or a fabricated statement_change
would misrepresent the required dependency-only repair.

Compared every retained node against the current read-only repository by JSON
reads, without Git. The item differs only in lean, five added definition/interface
statement dependencies, and the two comparison proof dependencies required by the
return. Neither dependency list drops a current-base dependency. Both new
existing:true definition ownership nodes are retained. Confirmed that the live
def-a1-integral-completed-pullback-interfaces owns completedRingIso and transport
in precisely the recorded module. The base item still has no lean record and
neither required comparison in proof_deps.

Read the unchanged wrapper's explicit authorization for maintainer-return
proof-dependency additions with no mathematical statement correction. Server
preflight still rejects this permitted packet. No tool was edited or bypassed,
no required dependency was removed, and no push was attempted.

Recompiled the unchanged main Lean file using scompile.py: exit 0, sandbox
10.8 s and library module 11.0 s, no errors or warnings. Delivery remains blocked
by the inconsistent server preflight gate; all repair files are retained.


## Dispatcher repair retry (2026-10-21 14:53 UTC)

Read the saved packet and ran the required initial deliver2.py --no-push before
editing. The server preflight again exited 1 with the same two diagnostics:
proof_deps changed without a statement correction, and no nonempty Statement
corrected section. Nothing was pushed. JSON comparison with the current read-only
repository confirms the statement and proof are verbatim and statement_change is
absent on both. The two proof-dependency additions are exactly the comparisons
required by the return; no current dependency is removed. The two new existing:true
definition nodes and the live integral completed-pullback interface are retained.

Read deliver2.py's unchanged dependency-only repair branch: it explicitly permits
these proof-dependency additions without changing the mathematical statement.
The server preflight refuses that authorized repair. The launcher-tool instruction
requires reporting a wrong gate refusal rather than patching or bypassing it.
No tool was edited and no fictitious statement correction was introduced.

Recompiled the unchanged main Lean module with the prescribed scompile.py:
exit 0, sandbox 10.8 s and library module 11.0 s, no errors or warnings.
The repaired packet remains ready in the sandbox; delivery is blocked solely by
the inconsistent server preflight gate.


## Dispatcher repair retry (2026-10-21 15:06 UTC)

Inspected the retained report and ran the required initial deliver2.py --no-push
on the saved packet. It exited 1 with the same two server preflight diagnostics:
proof_deps changed without a statement correction, and no nonempty Statement
corrected section. Nothing was pushed.

Compared the retained JSON packet with the current read-only repository, without
Git. The item differs only in lean, five added definition/interface statement
dependencies, and the two comparison proof dependencies required by the return.
Neither dependency list drops a current-base dependency. The statement and proof
are verbatim, and statement_change is absent on both. Both new existing:true
definition ownership nodes and the live integral completed-pullback interface
remain present.

Read the unmodified deliver2.py dependency-only repair branch: it explicitly
permits the required proof-dependency additions while retaining the mathematical
statement. Server preflight still rejects that authorized packet. The human's
launcher-tool instruction requires reporting this wrong gate refusal rather than
patching or bypassing it. No tool was edited, no required dependency was removed,
and no fictitious mathematical statement correction was introduced.

Recompiled the unchanged main Lean file with scompile.py: exit 0, sandbox 10.8 s
and library module 11.0 s, no errors or warnings. All repair files are retained.
Delivery is blocked solely by the reproduced inconsistent preflight gate.


## Dispatcher repair retry (2026-10-21 15:25 UTC)

Inspected the retained report and ran the prescribed initial deliver2.py --no-push
on the saved packet before editing. The main module and existing-declaration
probes passed the server compilation step. Server preflight exited 1 with:

> (b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

JSON comparison with the current shared read-only repository confirms that the
statement and proof remain verbatim and there is no statement_change. Only lean,
five added statement dependencies, and the two return-required proof dependencies
differ. Neither dependency list removes a base dependency. Both existing:true
definition nodes retain their requested ownership records. The live
def-a1-integral-completed-pullback-interfaces is cited as required.

Read the unchanged delivery wrapper: its dependency-only repair branch expressly
permits these proof_deps additions without a mathematical statement correction.
The server gate refuses this authorized repair. The launcher-tool instruction
requires reporting a wrong refusal, not editing or bypassing the tool. No tool
was modified, no required dependency removed, and no statement correction invented.

Independently reran the prescribed scompile.py for the unchanged main module:
exit 0; sandbox 12.3 s and library module 11.9 s; no errors or warnings.
The complete repaired packet is retained. Nothing was pushed; delivery remains
blocked solely by the inconsistent preflight gate.


## Dispatcher repair retry (2026-10-21 15:31 UTC)

Inspected the saved report and ran the required initial deliver2.py --no-push
before editing. Server compilation succeeded; server preflight exited 1 with the
same two gate diagnostics: (b) proof_deps changed without a statement correction,
and (e) no nonempty Statement corrected section. Nothing was pushed.

Compared all saved node JSON with the current shared read-only repository without
Git. Both new existing:true definition ownership nodes remain present; the live
def-a1-integral-completed-pullback-interfaces is cited. The item's statement and
proof remain verbatim, with no statement_change. Only lean, five added statement
dependencies, and the two return-required comparison proof dependencies differ.
No base dependency is removed.

Read deliver2.py's unmodified dependency-only repair branch, which explicitly
permits these proof-dependency additions without a mathematical statement change.
The server preflight still refuses them. No tool was modified or bypassed, no
required dependency was removed, and no statement correction was fabricated.

Independently recompiled the unchanged main Lean file with scompile.py: exit 0,
sandbox 12.3 s and library module 11.9 s, no errors or warnings. The complete
repaired packet is retained; the remaining blocker is the reproduced wrong
server preflight refusal of the authorized dependency-only repair.


## Dispatcher repair retry (2026-10-21 15:38 UTC)

Inspected the saved report and ran the prescribed initial deliver2.py --no-push
on the retained packet. Server compilation passed; server preflight exited 1:

> (b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

Compared every retained node with the current read-only repository using JSON
reads, without Git. Both requested existing:true definition nodes remain new;
the live def-a1-integral-completed-pullback-interfaces is cited. The item differs
only in lean, five added statement dependencies, and the two comparison proof
dependencies required by the return. No dependency is removed. Statement and
proof remain verbatim, and statement_change is absent.

Confirmed in the unmodified deliver2.py that its dependency-only repair branch
explicitly permits adding proof dependencies without changing the statement.
The server gate refuses that authorized repair. No tool was edited or bypassed,
no required dependency was removed, and no mathematical correction was fabricated.

Independently recompiled the unchanged main module through scompile.py: exit 0,
sandbox 12.3 s and library module 11.9 s, no errors or warnings. Nothing was
pushed. The repaired packet is retained; the remaining blocker is the reproduced
server preflight refusal.


## Dispatcher repair retry (2026-10-21 15:43 UTC)

Inspected the saved report and ran the prescribed initial deliver2.py --no-push
on the retained packet. Server compilation passed; server preflight exited 1:

> (b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

Compared all saved node JSON with the current read-only repository without Git.
The two requested existing:true definition nodes remain present, and the item
cites def-a1-integral-completed-pullback-interfaces. Statement and proof are
unchanged; only lean, five added statement dependencies and the two return-required
proof dependencies differ. No base dependency is removed.

Read the unmodified delivery wrapper's dependency-only repair branch. It explicitly
permits these proof_deps additions without a mathematical statement change, while
server preflight refuses them. No tool was modified or bypassed, no required
dependency removed, and no mathematical correction fabricated.

Independently recompiled the retained main module through scompile.py: exit 0,
sandbox 11.4 s and library module 11.4 s, no errors or warnings. Nothing was
pushed. The complete repaired packet is retained; the remaining blocker is the
reproduced inconsistent server preflight gate.


## Dispatcher repair retry (2026-10-21 15:52 UTC)

Inspected the saved packet and ran the prescribed initial deliver2.py --no-push.
Server compilation passed; server preflight exited 1 with the same two reasons:
(b) proof_deps changed without a statement correction, and (e) no nonempty
Statement corrected section. Nothing was pushed.

Compared every saved node with the current shared read-only repository using JSON
reads, without Git. The item differs only in lean, five added statement
dependencies, and the two comparison proof dependencies required by the return.
No base dependency is removed. The statement and proof are unchanged and neither
copy has statement_change. Both requested existing:true definition records remain
in the packet, and def-a1-integral-completed-pullback-interfaces remains cited.

Read the unmodified deliver2.py dependency-only repair branch: it expressly permits
these proof-dependency additions while preserving the mathematical statement.
Server preflight refuses that authorized packet. No required dependency was
removed, no mathematical correction fabricated, and no tool edited or bypassed.

Independently recompiled the unchanged main Lean file through scompile.py: exit 0,
sandbox 11.4 s and library module 11.4 s, with no errors or warnings. The complete
repair remains in the sandbox. Delivery is blocked solely by this wrong server
preflight refusal, as the launcher-tool instruction requires reporting.


## Dispatcher repair retry (2026-10-21 15:57 UTC)

Inspected the retained report and ran the prescribed initial deliver2.py --no-push
on the saved packet. Compilation passed, but server preflight exited 1 with the
same two diagnostics: (b) proof_deps changed without a statement correction,
and (e) no nonempty Statement corrected section. Nothing was pushed.

JSON comparison against the current read-only repository confirms that the
statement and proof are unchanged and statement_change is absent. The item
differs only in lean, five added statement dependencies, and the two comparison
proof dependencies required by the return. No base dependency was removed. Both
new existing:true definition nodes and the live integral completed-pullback
interface remain present. The unchanged delivery wrapper explicitly permits
these return-required proof-dependency additions without a statement correction;
server preflight rejects them. No tool was modified or bypassed.

Independently recompiled the unchanged main module using scompile.py: exit 0,
sandbox 12.2 s and library module 12.0 s, no errors or warnings. The complete
repaired packet remains in the sandbox. The remaining blocker is the reproduced
server gate refusal of the authorized dependency-only repair.


## Live-base repair refresh (2026-10-21 16:11 UTC)

The first prescribed dry run reproduced the proof-dependency correction gate refusal.
A fresh read of the shared live node now shows both required comparison theorems
already in proof_deps, with their uses recorded in proof steps 5 and 6. Refreshed
the packet proof verbatim from that live node, preserving those uses. The packet
now differs from this base only in lean and the five definition/interface
statement dependencies; the mathematical statement and proof dependencies are
unchanged. Both requested existing:true definition nodes and the live integral
completed-pullback interface remain present. The unchanged Lean module passed
scompile.py with exit 0 (sandbox 12.2 s, library 12.0 s), without warnings.
