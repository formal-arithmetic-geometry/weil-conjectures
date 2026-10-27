## Worker report

NZ states `det-sp-integral-adjunction-bijection` in
`Sheaf.Paper.IntegralAdjunctionBijection`, declaration
`AlgebraicGeometry.ProEtale.SpIntegralAdjunction.integral_adjunction_bijection`.
After the H2 ownership repair, the two postponed results are named theorems with the complete DAG proof routes in
source/blueprint docstrings. All definitions have actual data; no definition uses
`sorry`, and no arbitrary family of finite arrows is lifted to a tower arrow.

The current blueprint was read under `literature/blueprint/latest/`, specifically
`sec-smooth-purity/sk-prop-sp-integral-adjunction/` and its bijection proof.
The existing node statement is retained verbatim. No statement is disputed and no
statement correction or blueprint-unit correction is made.

Hypotheses and notation, clause by clause:

- Finite base field, its algebraic closure and characteristic: `D : FiniteFieldDatum`.
  `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p` specify the coefficient prime.
  `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]` specify the finite coefficient extension.
  The valuation ring, finite quotients and completion are the recorded upstream
  constructions, not new abstract rings. No extra `CharP` hypothesis is imposed.
- Schemes over the algebraic closure: `X.Over (Spec (.of D.k))` and similarly Y.
  Separatedness is `IsSeparated` on their structure maps. Finite type is rendered
  by `LocallyOfFiniteType` and `QuasiCompact` on those maps.
- The chosen compactification is `j : X ⟶ Z`, `[IsOpenImmersion j]`,
  `p : Z ⟶ Y`, `[IsProper p]`; `f` is the literal composite `j ≫ p`, and
  `(j ≫ p).IsOver (Spec (.of D.k))` requires the morphism to be over k.
  `d : ℕ` and `[SmoothOfRelativeDimension d (j ≫ p)]` give smoothness and the
  nonnegative pure relative dimension. Separatedness follows from the specified
  open/proper factorization. The result-type definitions `reconstructionResult`
  and `realizationResult` derive compactness of X and quasi-separatedness of Y,
  hence quasi-compactness of f, and derive `HasCompactification f` from that same
  actual factorization. These are not extra theorem hypotheses.
- `b`, `o`, `q` are the published tower base, operations and section coordinates.
  `RX`, `RY` are the actual strict derived reductions, with `NX`, `NY` their
  normalized reconstruction data. `hF`, `G`, `a`, `lv` are exactly the given
  constructible tower support, its right adjoint and its finite-level adjunction
  realizations from tower gluing. `w` is the published Tate-line coordinate data.
  These are presentations of the operations already specified by the node.
- Integral derived-complete bounded constructible categories are precisely
  `sfIntegralConstructibleCategory l E X/Y`. The coefficient-tower category is
  `SpTowerCalculus.C`, the full category of constructible strict towers with
  common cohomological and Tor bounds. Normalization is separately asserted by
  `IsSpNormalizedTower` and by equivalences with the full normalized categories.
  Natural index n always means positive exponent n+1, including n=0.

Conclusions, clause by clause (the theorem returns the nonempty package
`realizationResult`, definitionally the structure `Realization`):

- `Reconstruction.normalized` asserts that `G (red_Y K)` is normalized, with
  constructibility already enforced by the full tower category. `closed` gives
  membership of its actual total limit in the integral category.
- `limit` is `spCompletedTotalLimit` with the recorded forgetful exactness data.
  `exceptional` is literally `reduce_Y ⋙ G ⋙ inclusion_X ⋙ limit_X`.
  `right` restricts this very object and its maps to the full integral category;
  it does not choose a right adjoint by a bare existence statement.
- `rightComparison` is a natural isomorphism `red_X H ≅ G red_Y` and
  `right_normalization` identifies it with the actual reconstruction counit.
- `support` is the actual separately derived completed-ring compactification
  composite from `CompleteCompactificationLimit.image`. `support_closed` gives
  its constructibility. `imageComparison`, `image_normalization`,
  `leftComparison`, `left_normalization` pin its comparison to the canonical
  complete-compactification map and the actual reconstruction counit.
  `towerWord` is a constructed natural isomorphism between the two published
  presentations; it uses equivalence counits and derived composition maps.
- `homChain` is a real composition of equivalences: full faithfulness of red_Y,
  source transport by `leftComparison`, `a.homEquiv`, target transport by
  `rightComparison.symm`, then inverse full faithfulness of red_X. Thus it
  explicitly renders all three displayed bijections. `adjunction` and
  `hom_equiv` assert that this very chain is the integral adjunction's Hom
  equivalence; its naturality and triangles are included in `Adjunction`.
- `unit_reduction` and `counit_reduction` state the displayed equations of
  entire-tower morphisms, with both endpoint comparisons. `unit_limit` and
  `counit_limit` state their actual derived-limit formulas conjugated by the
  actual reconstruction units. `finite_unit` and `finite_counit` state their
  equality with the finite units and counits after exact finite evaluation,
  including the recorded support and exceptional evaluation comparisons.
- `purity` is the recorded `SpTowerGamma.Purity`, which pins the tower gamma to
  its orientation, tensor-adjunction mate and finite-level normalizations.
  `source_complete` asserts constructibility/completeness of the actual
  `SpTwistedPullback.source f d (2*d)` (completed pullback, Tate twist, shift).
  `sourceComparison` provides a natural whole-tower comparison to the ordered
  tensor-line convention of tower gamma. `purity_realization` explicitly says
  that the actual reconstruction unit followed by total limit of this comparison
  and the actual `SpTowerGamma.gamma` is invertible. It states this for every
  source comparison, so applies in particular to the canonical simultaneous
  pullback/twist/shift comparison supplied by the recorded reduction theorem;
  no particular arbitrary comparison is substituted for the canonical one.
  The section-preserving realization's unit and inverse functor are written in
  the formula, so its target is precisely `H(K)` in the original derived category.

Dependency declarations read and used (names are relative to the namespaces
indicated; the source imports use the complete module names):

| Node | Module / declarations |
| --- | --- |
| det-sp-integral-direct-image-tower | `Sheaf.Paper.IntegralDirectImageTower`: `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.integral_direct_image_tower` |
| det-sp-normalized-equivalence | `Sheaf.Paper.SmoothPurityNormalizedEquivalence`: `AlgebraicGeometry.ProEtale.sp_normalized_equivalence`, `SpNormalizedEquivalence`, `spCompletedReduction`, `spCompletedTotalLimit` |
| det-sp-tower-gluing | `Sheaf.Paper.SmoothPurityTowerGluing`: `AlgebraicGeometry.ProEtale.SpTowerGluing.tower_gluing`, `support`, `Levels`, `level` |
| det-sp-tower-gamma | `Sheaf.Paper.SmoothPurityTowerGamma`: `AlgebraicGeometry.ProEtale.SpTowerGamma.tower_gamma`, `Purity`, `gamma`, `factorization`, `source` |
| def-weil-finite-field-fiber | `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; the actual ring and its extension integers are used through the tower base |
| def-weil-scheme-morphism-properties | Existing Mathlib classes `IsSeparated`, `IsOpenImmersion`, `IsProper`, `LocallyOfFiniteType`, `QuasiCompact`; the node is a collection of notions, not an extra structure to recreate |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.SmoothOfRelativeDimension` (the recorded Mathlib interface) |
| def-weil-completed-integral-coefficients | `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: `WeilConjectures.integralConstantToCompletionOfUniverses`; the same completion is used by scalar reduction |
| def-weil-derived-complete-integral-detailed | `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`, `sfIntegralConstructibleCategory` |
| sk-def-sp-coefficient-towers | `Sheaf.Paper.SmoothPurityCoefficientTowers`: `AlgebraicGeometry.ProEtale.spCoefficientTowers`, with its abelian tower presentation |
| sk-def-sp-normalized-towers | `Sheaf.Paper.SmoothPurityNormalizedTowers`: `AlgebraicGeometry.ProEtale.spNormalizedConstructibleTorTowerCategory`, `IsSpNormalizedTower` |
| def-pur-integral-derived-operations | `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `WeilConjectures.IntegralOnSlice.completedTensor`; actual `integralDerivedPullback` in `SpTwistedPullback.source` |
| def-coefficient-twists-detailed | `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded integral signed Tate line and twist convention |
| lem-sp-fully-faithful-adjunction-restriction | `Mathlib.CategoryTheory.Adjunction.Restrict`: `CategoryTheory.Adjunction.restrictFullyFaithful`, its Hom and unit/counit formulas |
| lem-sp-twisted-pullback-reduction-tower | `Sheaf.Paper.TwistedPullbackReductionTower`: `WeilConjectures.SpTwistedPullback.twistedPullbackReductionTower` |
| def-sp-twisted-pullback-reduction-data | `Sheaf.Paper.TwistedPullbackReductionData`: `WeilConjectures.SpTwistedPullback.source`, `reduction` |
| def-sp-complete-compactification-limit-comparison / lem-sp-complete-compactification-limit-realization | `Sheaf.Paper.CompleteCompactificationLimitRealization`: `AlgebraicGeometry.ProEtale.CompleteCompactificationLimit.image`, `comparison`, the recorded scalar and limit presentation structures |
| lem-sp-integral-reconstruction-comparisons | supplied in this delivery; see below |

Edge cases checked before finalizing: empty schemes and zero objects do not require
points or a nonzero object; no connectedness/surjectivity/nonemptiness is added.
For f=identity and d=0, the shifted line is the coefficient unit and the Hom chain
is the usual identity adjunction after the stated comparisons. Index n=0 denotes
ell^1, never the zero quotient ell^0. Ramified E is allowed: the existing tower
coordinates and strict cofinal comparison retain ell-power versus uniformizer-power
normalizations. Integral categories are the full bounded constructible categories,
not bounded-below replacements or just cohomology groups. All naturality and
reconstruction equations are actual derived morphism equations, not levelwise-only
surrogates. The inverse in the last Hom transport and the counit transpose were
checked against Mathlib's diagrammatic composition convention.

Searches performed using the prescribed NZ/item wrappers and source searches:

- `msearch.py ... leanfinder "Integral constructible sheaves adjunction obtained by derived inverse limit of normalized coefficient towers"`: eight hits, including locally constant/condensed adjunctions and module-to-presheaf adjunctions; none states integral tower reconstruction.
- `msearch.py ... loogle "CategoryTheory.Adjunction.restrictFullyFaithful"`: six hits, including the restriction constructor, its Hom equivalence and unit/counit formulas. This is the exact abstract leaf and is used; it does not state this geometric result.
- `msearch.py ... grep "integral.*adjunction|normalized.*tower" CategoryTheory`: zero hits.
- `msearch.py ... leansearch "Reduction of integral constructible sheaves to normalized coefficient towers is fully faithful with natural compact support and exceptional reconstruction comparisons"`: eight hits, mostly condensed locally constant fully faithful functors and sheaf forgetful functors; no exact reconstruction statement.
- `rg` on `lean/WeilConjectures` for integral/adjunction found the étale rational operations, bounded constructible upper shriek and integral Verdier modules. Their categories and constructions differ from the completed small-pro-étale strict tower realization here; they are not duplicate statements.
- The node-id search on `lean/WeilConjectures` found no exact declaration. The corresponding `lean/Sheaf` search found a downstream SmoothPurityQbar source citation, not this theorem.
- Searches of Mathlib algebraic geometry and the project for the proposed full declaration names found no existing declaration. The example CompactObject module is withdrawn and points to its upstream existing declaration, as its node record says.

Validation: both delivered files compiled separately in dependency order with the
prescribed `scompile.py` against the live published build. The final compile after
removing redundant geometry hypotheses was clean (only the expected postponed
proofs remain). Delivery preflight and its own per-file compilation are run below.

## Dependency modules

The genuine prerequisite `lem-sp-integral-reconstruction-comparisons` had no Lean
record. Under the human bottom-up instruction it is stated in this delivery, in
`Sheaf.Paper.IntegralReconstructionComparisons`, declaration
`AlgebraicGeometry.ProEtale.SpIntegralAdjunction.integral_reconstruction_comparisons`.
Its copied JSON changes only `lean`, with a note explaining this missing interface.
The reconstruction data now has its own definition node and module, as requested
in the H2 return; this prerequisite module contains only its named theorem.
The existing scalar-comparison structure receives a definition-node record, with
no second Lean definition. See the repair and new-node sections below.

The definition-node-owned `Reconstruction` structure renders every clause of
the reconstruction theorem node: Noetherian X/Y;
fully faithful reduction; equivalences whose functor and inverse are exactly
reduction and total limit; normalization preservation of both tower functors;
the existing ambient adjunction restricts along these full subcategories with the
same maps; actual H and its constructibility; canonical natural b and c with their
specified compactification and counit normalization; actual reconstruction units;
and the reconstruction equality for every actual morphism. Naturality of b and c
is built into their natural-isomorphism types. The geometric and coefficient
hypotheses are exactly those described for the main item, including smooth pure
dimension d. Its theorem docstring follows all seven proof steps of its own DAG.

The item's stmt_deps cites the new reconstruction-data and scalar-comparison-data
definition nodes, the existing canonical compactification-comparison definition
and twisted-source data node. It does not cite either reconstruction or
compactification-realization theorem merely for definitions in their modules.
The reconstruction theorem remains an item proof dependency. Both theorem
statements, their proof routes and the item proof_deps are retained.

## Second reading by NZ

I reread both signatures and all package fields against the current node statements
and current blueprint proof. Checked the Hom directions, endpoint transport,
actual adjunction unit/counit normalizations, positive index convention, strict tower
categories, completeness, and the empty/identity/zero cases listed above.
The dispatcher expressly forbids starting other agents; independent review is the
maintainer's delivery review. No independent reviewer is claimed here.


## Repair of returned head aad47d6d3da7

H2 is repaired by changing definition ownership and dependency edges. The returned
sandbox's node signatures and module bodies were read alongside the current shared
base. The base still has no recorded Lean theorem for the item or reconstruction
prerequisite; its mathematical statements match the retained delivered statements.
No mathematical statement, hypothesis, conclusion, or proof route is changed.
The delivery wrapper refreshes current main and builds a fresh commit on it.

1. Created `def-sp-integral-reconstruction-comparison-data`, owning
   `Sheaf.Paper.IntegralReconstructionComparisonData`. Moved precisely `limit`,
   `reduction`, `reduce`, `support`, `exceptional`, `right`, `ordinaryConjugation`,
   `towerWord`, `Reconstruction`, and `reconstructionResult` there, keeping their
   fully qualified names and bodies. Updated their source tags to the owning
   definition node. The new module asserts no existence theorem.
2. `IntegralReconstructionComparisons` now contains only the named
   `integral_reconstruction_comparisons` theorem and its unchanged signature and
   seven-step proof docstring. It publicly imports the data module and privately
   imports the realization theorem as a genuine proof dependency.
3. Created `def-sp-complete-compactification-scalar-comparison-data`, with
   `existing: true` for the exact existing
   `AlgebraicGeometry.ProEtale.CompleteCompactificationLimit.ScalarComparison`
   in `Sheaf.Paper.CompleteCompactificationLimitRealization`. This is the requested
   definition-node ownership of the structure, not a copy and not an application
   of the theorem. Its signature is copied verbatim from `structure` to `where`.
   Its node defines the ordinary open/push scalar isomorphisms, their exact finite
   normalizations, and the derived push scalar comparison with its composition-unit
   normalization, without asserting an inhabitant. Keeping this existing structure
   retains the normalization field and all comparison formulas intact.
4. Both the item and the reconstruction theorem cite the two new definition nodes.
   Removed `lem-sp-integral-reconstruction-comparisons` and
   `lem-sp-complete-compactification-limit-realization` from the item's stmt_deps.
   The first is still a proof dependency; the second remains the reconstruction
   theorem's actual proof dependency. The item's public import of the old
   reconstruction module is replaced by a public data import and a private
   reconstruction theorem import. The new scalar definition node supplies the
   structure even though its existing source module also contains a theorem.

The reviewer accepted the mathematics, all Hom directions, every unit/counit
formula, actual gamma realization, empty/identity/zero cases and no hollow data.
Those parts are retained. I reread the relocated declarations against their
new-node statements: the data types make no existence claims; the two theorems
still make exactly those existence claims. No independent second reader is
claimed; the dispatcher's prohibition on other agents remains in force.

## New nodes

`def-sp-integral-reconstruction-comparison-data`: defines the actual functors,
the equivalence-counit conjugation and separately derived tower-word comparison,
and the type of normalized integral reconstruction data used by the two theorems.
It includes exactly the relocated package fields, their full normalizations and
reconstruction equations, and the wrapper deriving geometric instances. Source:
latest blueprint integral-adjunction-bijection proof, Normalization and Bijections.
Searches: LeanSearch for normalized integral tower reconstruction data gave eight
profinite-limit and ring-normalization hits, none this datum; LeanFinder for
canonical scalar comparisons gave eight unrelated scalar-tower and completion
hits; Mathlib category-theory grep for `ScalarComparison|reconstructionResult|
SpIntegralAdjunction` gave zero hits. Exact project/DAG searches found only the
returned helper definitions, which are moved, not duplicated. Blueprint reference
search for “integral reconstruction” returned no definition-node owner; ancestor
query identifies this item as the required origin. The node includes the actual
search records with dates. Its definition is tested by the same empty, zero,
identity and positive-index cases as its original package.

`def-sp-complete-compactification-scalar-comparison-data`: the type of normalized
ordinary open/push and derived-push scalar comparisons, with all exact finite
and composition-unit normalizations, before any existence statement. The same
searches apply; exact source search finds the existing `ScalarComparison` at
`CompleteCompactificationLimitRealization.lean`, and the only DAG record naming
it is the realization theorem's multi-declaration record. The new node records
that exact declaration with `existing: true`, thereby supplying its missing
individual definition-node owner as explicitly requested. The source is the
blueprint's coefficient-restriction comparison part of Bijections and the
canonical compactification-comparison definition. At the identity open/proper
map the fields are the ordinary identity/unit comparisons; at the first index
n=0 they use the quotient ell^1. No nonempty input, finite-level lifting principle,
or invertibility of the limit word is asserted by this definition.
