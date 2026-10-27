## Worker report

The module `Sheaf.Paper.CompleteProjectionMateDescent` states
`AlgebraicGeometry.ProEtale.CompleteProjectionDescent.complete_projection_mate_descent`.
Its sole postponed proof is this named theorem. The definitions have real data.
The statement identifies the published ordinary integral compactification projection
with the reconstruction of the actual strict-system projection, records the inverse,
and states its bifunctorial naturality square.

The source read was the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-direct-image.proof.md`,
paragraphs (2) and (3). The DAG's proof explains the proper counit, open unit,
mate-pasting and reconstruction normalization used here.

Hypothesis-by-hypothesis and clause-by-clause rendering:

* Prime ell, finite E/Q_ell and its valuation ring: binders `l`, `Fact l.Prime`,
  `E`, `Field E`, `Algebra (Padic l) E`, `FiniteDimensional (Padic l) E`, and
  `Padic.coefficientExtensionIntegers l E` in `rings`. Positive exponent n+1
  is indexed by n : Nat, exactly as in the recorded tower definition.
* The coefficient sheaves and actual consecutive quotient maps: `rings`,
  `transitions`, `VaryingRing.coefficients` and `coefficientTransition`.
  These use `spEllIdeal`, not powers of a chosen uniformizer.
* The completed integral coefficient sheaf and ordinary unbounded categories:
  `Integral`, `System`, the recorded completed coefficient sheaf, and the exact
  `towerEquivalence` and `derivedTowerEquivalence`. Uncurrying preserves actual
  sections, maps and all transitions.
* Simultaneous derived reduction and total derived limit after scalar restriction:
  `reduction`, `totalLimit`, `reductionAdjunction` and the abbreviations `red`,
  `lim`, `adj`. These use `SpReductionTower` and `SpNormalizedEquivalence`;
  they are not a list of independently selected finite-level functors.
* Section-model operations and exact evaluations: `Calculus` is the existing
  `SemilinearSections.Data` on the vertical ell-power sequence site. The
  `SpCoefficientTowersAbelian` witness retains the original exact evaluations.
* The characteristic hypothesis is `p`, `Fact p.Prime`, `CharP k p`, `_hpl`.
  Prime characteristic entails p > 0. There is no `Finite k` or `Fintype k`.
* Separated finite-type k-schemes and a morphism between them: `X Y : Over
  (Spec k)`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on both
  structure morphisms, and `f : X ⟶ Y`. The supplied `Compactification f.left`
  is the actual proper/open factorization, including its equation and instances.
* F_R and F_bullet: `integralImage` is the recorded `ringedOpen` followed by
  `ringedPush`; `systemImage` is actual `VaryingRing.J` followed by `P`.
* Ordinary derived tensor and pullback: `inputTensor`, `m.integral.tensor`'s
  `ordinary.tensor`, and `ringedPull`. None is completed tensor or a completed
  pullback substituted into this ordinary projection formula.
* M and K complete with bounded-below reduction towers: `_hM`, `_hK`,
  `_hMplus`, `_hKplus`. The latter assert `∃ a, (red.obj ...).IsGE a` in
  the ordinary derived category of the whole ringed sequence site.
* H=M tensor f*K, U=F_R H, V=F_R M tensor K: `inputTensor` and the `U`, `V`
  lets in the conclusion. Completeness and bounded-below reductions for all
  three are `_hH`, `_hHplus`, `_hU`, `_hUplus`, `_hV`, `_hVplus`.
* The canonical compactification/limit comparisons for N=M,H are
  `compactificationLimit` and `_hAlphaM`, `_hAlphaH`. The map is F_R of the
  actual reduction unit, then proper image of `openLimit`, then `properLimit`.
  Those maps are the actual reduction/limit transposes of the normalized
  open scalar comparison and proper counit mate.
* The specified reconstruction counits for N=M,H are `reconstruction`,
  `hbM`, `hbH`. The map is explicitly `red.map compactificationLimit` followed
  by the actual reduction/limit counit. No further objectwise isomorphism is
  selected as the reconstruction coordinate.
* The tensor/scalar and pullback/scalar comparisons are `m.tensor`, `m.pull`.
  `TensorReductionModel` fixes their localization square on whole flat-term
  K-flat quotient complexes and their pure augmentation generators in every
  total-degree summand. `PullReductionModel` fixes the ordinary comparison by
  the actual geometric and scalar unit sections and its whole-complex
  localization square. The ordinary functors retain all quotient transitions.
  These structures present the canonical comparisons, not arbitrary maps with
  an assumed projection-square conclusion.
* System tensor pullback is `SystemTensorPull`: the recorded
  `TensorComparisonModel`, with its summand and localization squares, plus the
  ordinary adjunction unit-section formula. The proper projection
  `systemProperProjection` uses the actual `VaryingRing.adj` counit mate.
* Open scalar normalization is `DescentModels.openScalar_normalized`, the inverse mate
  of the pullback/scalar square under the actual open adjunctions.
  `systemOpenInverse` is precisely the open adjunct of unit tensor identity,
  composed with the inverse canonical tensor/pullback map. `hOpen` and
  `_hProper` say that the two system projection mates at the specified inputs
  are invertible. `systemProjection` composes proper projection, inverse open
  projection, and the normalized inverse pullback compositor, in that order.
* The source/target identifications and theta-tilde are `sourceComparison`,
  `targetComparison`, `transportedProjection`. All are whole derived-system
  morphisms and use the same reconstruction counits.
* The actual integral pi_R is the existing
  `ringedCompactificationProjection m.integral m.openIntegral c M K`.
  `RingedOpenComparisons.projection_transpose` fixes its open unit normalization;
  `ringedProperProjection` fixes its proper counit normalization.
* Equality with reconstruction is `pi = etaV.hom ≫ lim.map theta ≫ etaU.inv`.
  The preceding equalities fix etaU/etaV to the actual unit and t.hom to
  theta-tilde. The statement also records `red.map pi = theta`.
* Invertibility and its specified inverse: `e : V ≅ U`, `e.hom = pi`,
  `e.inv = etaU.hom ≫ lim.map t.inv ≫ etaV.inv`. This asserts both inverse laws
  through an actual isomorphism in the ordinary derived category.
* Naturality in M,K is the final equation for every `v : M ⟶ M'` and
  `w : K ⟶ K'`. It concerns the very same actual projection map, with
  bifunctorial source and target actions, and needs no completion hypothesis
  on the comparison objects M',K'.

Dependency declarations used (including their recorded owning modules):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and the Padic
  coefficient-extension declarations;
* `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spEllIdeal`, coefficient rings;
* `Sheaf.Paper.CompletedCondensedCoefficients`: completed integral coefficients;
* `Sheaf.Paper.SmoothPurityReductionTowerNormalized`: `SpReductionTower`,
  `spReductionGenerator`, actual strict reduction and localization comparison;
* `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `SpCoefficientTowersAbelian`, `spDerivedCoefficientTowers`;
* `Sheaf.Paper.SmoothPurityNormalizedEquivalence`: `SpNormalizedEquivalence`,
  `spCompletedReduction`, `spCompletedTotalLimit`;
* `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `SheafOfModules.strictSystemSequenceEquivalence`;
* `Sheaf.Paper.SemilinearDerivedSections`, `SemilinearDerivedCalculus`,
  `SemilinearSystemModels`: `Data`, `TensorComparisonModel`, tensor models;
* `Sheaf.AlgebraicGeometry.VaryingRingOperations`: `Modules`, `Derived`,
  `pull`, `G`, `P`, `J`, `moduleAdj`, `adj`, `jAdj`, `gComp`;
* `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`: `RingedModels`,
  `RingedOpenComparisons`, the actual ringed geometric operations;
* `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `ringedCompactificationProjection`;
* `Sheaf.Paper.ProEtaleCanonicalTensorPullback`:
  `ProEtaleTensorModel`, `proEtaleFlatRepresentatives`;
* `Sheaf.Paper.CoefficientRingedTensorHomModel`: `coefficientTotalTensor`,
  `coefficientTensorGenerator`;
* `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete` in its
  global branch (the published completed section-module realization);
* The original recorded condensed module push/pull, tensor/Hom and lower-shriek
  interfaces are imported alongside their published section-ring presentations;
* `WeilConjectures.Compactification.RefinementCategory`: `Compactification`;
  Mathlib `Over`, `Adjunction`, `mateEquiv`, `rightAdjointProjectionMap`.

The added stmt_deps are existing landed nodes owning the concrete presentations
actually used. A read-only traversal of stmt_deps/proof_deps found no path from
any of these additions back to the item. On repair, the two added theorem-node
references used only for plain definitions were replaced by their definition owners.

Edge cases checked before writing and again on reading the completed statement:
zero M or K; identity compactification and identity pullback; an identity quotient;
ramified E (ell-powers differ from uniformizer-powers); an infinite field k of
positive characteristic unequal to ell; unbounded integral complexes whose
reduction systems satisfy the stated lower bounds; and non-flat quotient ring
maps. The scalar-extension comparisons use K-flat models, not an assumption that
O -> O/ell^n is flat. Nothing detects equality of derived-system maps by evaluating
at finite levels. The inverse formula has domain U and codomain V, and its two
units are in the reverse order from the forward formula.

Searches: msearch leansearch, query “The actual compact support projection formula
for complete integral sheaves is the derived inverse limit of its strict finite
coefficient projection mates”: eight hits on ordinary presheaf limits and
profinite projections, no derived projection-mate match. msearch leanfinder, query “The compact support projection formula mate
for derived complete integral sheaves equals the derived inverse limit of its
strict coefficient tower mate”: eight unrelated condensed-category hits, no
exact match. msearch loogle “CategoryTheory.Adjunction,
CategoryTheory.MonoidalCategory”: abstract monoidal adjunction constructions, no
exact match. msearch grep “projectionFormula|projectionMate|complete.*projection”
in CategoryTheory: zero hits. Read-only rg searches of `lean/WeilConjectures` and
`lean/Sheaf` for projection/complete/projection-mate names found the reusable
ringed compactification map and normalized system models, but no theorem stating
this descent equality. The item-id search in WeilConjectures found no declaration.
The existing integral etale projection formula only gives invertibility after
completion and does not state this pro-etale actual-mate equality.

No statement correction, STATEMENT-DISPUTED marker, or dependency-record
replacement is needed. Canonical-map and representative helpers are defined in
the owning item's module, as authorized by the human's isolation update.

## Second reading by Q115

A separate self-audit reread the source, node and completed file clause by clause.
It checked the orientations of both adjunction mates, the proper/open order, the
compactification equation, the reconstruction counit and inverse formulas. It
also checked that the coefficient system uses ell-powers throughout. The initial
private import of `strictSystemSequenceEquivalence` was replaced with its owning
public import. Explicit universes were added to the total-tensor and generator
interfaces. This is a self-audit: no second agent was started, in accordance with
the dispatcher's explicit instruction. The maintainer performs the independent
review of the delivery.

The representative localization square uses `HEq` between the two definitionally
equal presentations of the same total complex. This retains equality of the
whole derived maps while avoiding repeated unfolding of signed totalization.
Additivity witnesses are instances of the existing ordinary quotient and exact
geometric pullback functors. The total-tensor elaboration heartbeat setting is
scoped to that predicate; no compile time limit is raised.

## New nodes

`def-sp-projection-reduction-presentation` defines `TensorReductionModel`, the
normalized representative predicate for the simultaneous ell-power tensor/scalar
comparison used by the item. Its module also packages the exact uncurrying,
actual reduction/limit adjunction, ordinary quotient functor, its augmentation
generators and its actual localization comparison, by composing the existing
recorded declarations. This is a definition with real data and a predicate,
not an existence theorem or a postponed construction. The source is current
blueprint paragraph (3), where reductions of tensor products are tensor products
of reductions. The representative predicate states that fact's normalization,
without proving the fact. Its chain map is one natural isomorphism of whole
strict complexes; its localization square is an equality of whole derived maps.
The main theorem binds a presentation of the canonical comparisons with these
constraints, and never assumes its own projection compatibility square.

Searches for the presentation: msearch leansearch with query “A normalized
presentation of simultaneous integral reduction on the ell power proetale sequence
site with tensor and geometric pullback comparisons fixed on quotient augmentations
and K flat complexes” returned eight unrelated scheme-normalization and ordinary
ring-tensor hits. Loogle query `"Reduction", "Tensor"` returned zero hits. Mathlib
grep `reduction.*[Tt]ensor|[Tt]ensor.*[Rr]eduction` in Algebra returned zero hits.
The same read-only DAG/Sheaf/WeilConjectures search for
`complete-projection-descent-model|TensorReductionModel|PullReductionModel|DescentModels`
found no matching presentation. The completed pullbackTensorReductionModel hits
use uniformizer powers and the completed constructible operations, so cannot be
substituted for this ordinary ell-power sequence-site presentation.
`blueprint_refs.py search 'projection.*descent'` found no matching blueprint node;
its ancestor command identified `det-sp-integral-direct-image-tower`, recorded
in the new node. The second reading covered this predicate and its constituent
normalizations as well as the theorem. The predicate form avoids generation of
large unused structure recursors, without changing the stated normalization.

## Validation

Both delivered modules compiled independently in dependency order through
`scompile.py`. The main module's sandbox check completed in 27.8 seconds and
its library check in 12.6 seconds (the wrapper's elapsed fields include slot
waiting). No warning remains. The tensor-normalization and pullback-normalization
conditions are predicates rather than structures with costly generated recursors;
all their quantified maps and equalities are retained. The theorem has the one
expected postponed proof. The original delivery passed the deliver2 dry run and was pushed at 540abd2fafa.
The repaired packet is compiled and checked again below.


## Repair of immutable head 540abd2fafaf

The current base has no Lean record for the returned item. Comparing its node
against the retained packet found changes only in `lean` and `stmt_deps`; the
source statement and all proof fields remain identical. The delivery wrapper
rebases the repaired packet onto the current live base.

H2: replaced `lem-sf-integral-compactification-system-realization` in the item's
stmt_deps with `def-pur-integral-ringed-projection-maps`, the existing:true owner
of `ringedProperProjection` and `ringedCompactificationProjection` in the same
unchanged module. Replaced `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
with `def-sfb-proetale-tensor-model`, the owner of `ProEtaleTensorModel` and
`proEtaleFlatRepresentatives` in the same unchanged tensor module. The accepted
`det-sp-normalized-equivalence` and `lem-pur-system-ringed-sequence-site` references
remain. No theorem conclusion is being used in place of these definitions.

H12: the new node `def-sp-projection-reduction-presentation` now directly cites,
in both its TeX and stmt_deps, all six missing constituent owners:
`def-sfb-proetale-tensor-model` (flat-term K-flat presentation),
`def-coef-ringed-tensor-hom-model` (total tensor and its generators),
`def-pc-kflat-complex` (K-flatness), `def-coef-ringed-sequence-site` (vertical
topology), `def-coef-semilinear-system-models` (system ring and tensor models),
and `def-sf-scalar-reduction-categories-restriction` (integral module category
and restriction). Their current recorded declarations were checked against the
published source. No new Lean construction or alternative definition was added.

Advisory on operation ownership: added `def-weil-pbc-proetale-operations` to the
item's stmt_deps for the actual ordinary ring-module pullback and its adjunction.
Its published arbitrary-ring operations supply `ordinaryPull` and the unit in
`PullReductionModel`; the ring is not assumed constant.

Advisory on reconstruction scope: removed the all-schemes reconstruction field
from `DescentModels`. Each helper now receives its actual reconstruction data
explicitly at its source and target. The main theorem binds `AX`, `AZ`, `AY`
only for `X.left`, the compactification's `c.Z`, and `Y.left`. These are the
three schemes of the supplied compactification over the field of characteristic
p unequal to ell. Thus the statement no longer requires a normalized-equivalence
existence assertion on unrelated schemes where ell may fail to be invertible.
The reduction and canonical tensor/pullback presentations are otherwise unchanged.
This is a restriction of presentation data, not a change to the item's source
statement or an extra geometric hypothesis.

Advisory on the extra conjunct: `red.map pi = theta` is stronger than the node's
explicit reconstruction conclusion, and is intentionally retained as the exact
compatibility equality proved in proof step 5. It records the same canonical
proper/open mate calculation, with no added premise. The reconstruction formula,
inverse and naturality clauses continue to render the node verbatim in Lean.

Repair self-audit: checked both owner replacements, exact agreement of new-node
TeX citations with stmt_deps, finite reconstruction scope and all map directions.
The maintainer's independent mathematical reading accepted the original clauses;
this repair preserves them while resolving H2, H12 and the scope advisory.


Repair validation: both delivered modules compiled separately through
`scompile.py Q115 lem-sp-complete-projection-mate-descent` in dependency order.
The repaired main module's library check completed in 16.2 seconds with no
errors or warnings. The wrapper also passed its sandbox check; elapsed slot
waiting is included in that wrapper's timing. All 14 new-node citations match
stmt_deps exactly, every Lean line is at most 100 characters, and the recorded
theorem signature matches the file verbatim. The only postponed proof remains
the named item theorem.
