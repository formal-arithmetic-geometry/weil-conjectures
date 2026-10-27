## Worker report

This delivery states conditional exact descent of the specified finite realizations to
ordinary derived sheaves of modules over the locally finite continuous closure ring.
It proves nothing: theorem bodies are `by sorry`, and definitions have genuine data.
The mathematical statement is unchanged. The returned delivery is repaired with
definition ownership for its canonical scalar maps and a local shift instance.

Hypotheses and clauses, in order:

* `l`, `Fact l.Prime`, `FiniteFieldDatum D`, `hl`, and `a` fix the prime, geometric
  finite-field base, unequal characteristic, and scheme structure map. `IsSeparated a`,
  `LocallyOfFiniteType a`, and `QuasiCompact a` express separated finite type.
* The closure is the fixed existing `PadicAlgCl l`. The actual finite subfields index
  `GeneralAlgebraicallyClosedCoefficients.Stage` and its published `stageTransition`.
  `coefficient` is the recorded small coefficient model, not a different field diagram.
* `finiteRing` is the continuous finite coefficient sheaf. Its identification with
  the inverse-limit completion localized at a uniformizer is the existing
  residue-normalized `CoefficientPresentation`, selected by a uniqueness theorem.
  `integralMap` uses its completed-integral identification and integral inclusion.
  `closureRing` uses the native internal coefficient's ordinary section ring: its
  sections are locally finite continuous functions, equivalently locally valued in
  one finite subextension. `closureMap` fixes the actual subfield inclusion pointwise.
* `constructible` imposes boundedness by `IsGE` and `IsLE`, and for each cohomology
  sheaf a finite locally closed stratification with pro-etale locally finite free
  inverse image on every stratum. This is the full ordinary derived subcategory
  of the node, with variable finite ranks, including zero.
* `J`, its `CommShift`, and `hJ` express exactness, all derived Hom bijections,
  and precisely the finite-coefficient constructible essential image. Together they
  express the given equivalence to that full subcategory. `hlinear` expresses
  E-linearity using the existing raw localized coefficient action and the canonical
  localization-to-E equivalence, including all fractional scalars.
* `α` specifies that J is induced by ordinary derived scalar extension from the
  actual completed integral sheaf; it is natural on all integral derived arrows.
  Raw localization keeps objects and inverts the uniformizer, so this determines
  its extension on fractional arrows. `hα` retains the exact, tensor-induced shift.
* `j` is the natural finite scalar comparison. `scalarNormalized` says that its
  restriction to integral objects is exactly the specified quotient-completion
  comparison `completedScalarComparison`, composed with the balanced derived tensor
  associators `pbcReductionNormalization`. This fixes j on raw fractions too.
* `finiteIdentity` includes the identity scalar unit, fixed on pure tensors by
  multiplication and in the derived category by its computation counit.
  `finiteCoherent` is the tower equation with the source's actual associator.
  `coherent` imposes identity and tower equations after extension to the closure.
* `extended` is precisely G_E = closure extension after J_E. `gamma` is precisely
  j followed by canonical balanced multiplication into the closure coefficient.
* The existential functor rho has the specified object equality. The HEq arrow
  formula applies to every representative at every common finite field and uses
  inverse source gamma, G_F(u), and target gamma. Since rho is a functor on the
  actual quotient category, the formula includes independence of fields and
  representatives, as well as identity and composition.
* The bijection on `ColimitHom` is rho.map composed with the inverse of the
  dependency's actual normalized `homCoordinates`; it is the canonical colimit map.
* The target image equivalence is stated for every ordinary derived object M.
  The additional equivalence witness targets exactly the full subcategory
  `constructible.FullSubcategory` and agrees naturally with rho in the ambient category.
* The final shift structure makes rho triangulated and fixes each finite-stage
  shift component to the composite shift of J_E and ordinary derived tensor.
  Together with the representative-arrow formula this sends a finite-stage
  distinguished triangle, including its connecting arrow, to its derived scalar
  extension, with the specified finite-stage normalization.

Dependency declarations used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* Mathlib pro-etale site: `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `completedIntegralCommRingSheafUnrestricted` and its finite projections.
* `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`: the actual
  finite-field and algebraic-closure condensed coefficient rings.
* `Sheaf.Paper.CompletedCondensedCoefficients`: the completed, rationalized,
  and finite-subextension colimit identifications used in the proof plan.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `stageTransition`,
  `integralTransition`, `stageSystem`, `unitor`, `Pair`, `ColimitHom`,
  `homCoordinates`, `inclusion`, and its shift comparison.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib: `DerivedCategory` and its homology and shift functors.
* `Sheaf.Paper.SfScalarExtensionComposition`: the actual completed source transitions.
* `Sheaf.Paper.BoundedConstructibleTower`: `pbcModules`, `pbcExtend`,
  `pbcDerivedExtend`, `pbcComplexCounit`, and `pbcReductionNormalization`.
* `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`: only its coefficient
  helpers `abRing`, `ringSheaf`, `embedding`, `CoefficientPresentation` are used;
  the whole-category realization theorem is not assumed or invoked.
* `SheafOfModules.homLinear`: the general global-section action, restricted along
  the actual constant continuous functions. The normed-field action in
  `Sheaf.Paper.CondensedERealization` has extra normed-algebra parameters not carried
  by the raw small coefficient model; the helper here specializes the general
  sheaf-module action directly, without choosing a different linear structure.
* `Sheaf.Paper.RationalScalarBalancedLocalization`: `rationalBalancedCoefficient`,
  the actual continuous postcomposition map for a finite embedding; it is now owned
  by `def-sf-rational-coefficient-inclusion`.
* `Sheaf.Paper.CompletedIntegralScalarData`: `completedIntegralScalarCoefficientMap`,
  the transparent alias of `completedCoefficientMap` owned by its landed definition node.
* `Sheaf.Paper.SfCompletedScalarComparisonData`: `completedIntegralScalarComparison`,
  a transparent alias of `completedScalarComparison`, with the same quotient-chain-map
  normalization. Its public import reexports the canonical coefficient-map owner.
* The advisory definition owners are cited explicitly: `proEtaleModuleInverseImage`
  (`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`), `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory` (`Sheaf.Paper.SfIntegralConstructible`),
  `adicLisseForget` (`Sheaf.Paper.AdicLisseModule`),
  `CochainComplex.IsKFlatIndependentCoefficients`
  (`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`), and
  `ScalarLocalization.linear` (`Sheaf.CategoryTheory.ScalarLocalization`).
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`; the general sheaf-of-modules
  `IsFiniteLocallyFree` is imported from the upstream LocallyFree module.

Statement dependencies now cite definition owners for every coefficient helper;
the three theorem nodes identified by the return have been replaced by those owners.
No existing definition is copied. The dependency-closure audit found no path back to this item and hence no cycle.

Edge cases checked: the empty scheme admits the empty stratification and the zero
object; free rank zero is allowed; the cohomological bounds need not be nonnegative;
each cohomological degree can have its own stratification, equivalent to one common
finite refinement since the complex is bounded. Repeated adjacent fields and identity
maps are retained in both the hypotheses and every formula. No torsion-free integral
Hom hypothesis is imposed. The raw category is not idempotent-completed. Finite-field
size transport is the existing Shrink convention; the small site's object universe is
u+1 and its morphism universe u, with coefficient/module objects at u+1.

Searches: msearch leanfinder, query “A coherent finite coefficient realization cocone
descends to an exact equivalence from the common stage constructible l adic pair
category”, returned 8 unrelated local-cohomology/adic-completion results. Loogle
`"DerivedCategory", "Equivalence"` returned 0. Mathlib grep
`constructible.*colimit|colimit.*constructible|adic.*equivalence` returned 9 unrelated
algebra and categorical-tool results. Project rg searches for common-stage realization,
constructible coefficient colimits, adic equivalence, and this exact node id found the
related realization and coefficient interfaces above, but no theorem with this conditional
cocone, representative formulas, canonical Hom maps and shift normalization. The new
namespace/declaration names were also searched in dag/lean_names_upstream.json and both
Lean source trees and were absent.

Sources read: BS Lemma 6.8.2, Definitions 6.8.3/6.8.8, Proposition 6.8.14 and
Remark 6.8.15; HRS Proposition 5.2 and Lemma 7.9. The selected coefficients are
continuous coefficients throughout. There is no disputed mathematical statement.

## Second reading by Q70

The dispatcher explicitly prohibits starting another agent, so this is a separate
in-thread rereading, not a claim of an independent second worker review. The maintainer's
independent review remains required. Comparing the node clause by clause exposed these
issues in the initial draft: an abstract target omitted the ordinary module category;
arbitrary coherent J and j omitted their completion/tensor normalization; the finite
identity and tower equations and explicit finite shift component were missing. The final
file uses concrete coefficient sheaves, completion-normalized α and j, both levels of
coherence, the actual common-field Hom coordinates, and the finite-stage shift equation.
No target statement has been changed.


## New nodes

`def-sf-completed-scalar-comparison-data` owns a module publicly reexporting the
landed completed integral scalar-data owner and the published comparison constructions.
Its new `completedIntegralScalarComparison` is a transparent abbreviation of the
existing `completedScalarComparison`, not an independent copy or a new choice.
The coefficient map is reused through `completedIntegralScalarCoefficientMap` from
`def-weil-completed-integral-scalar-data`. This existing owner was found while comparing
the returned packet with current main; it already owns the residue-normalized map and
ordinary extension but does not own the derived completion comparison. The new node
records exactly the strict quotient-Roos chain map and unique derived descent of
BS 6.8.2(1), 3.4.10, 3.4.12 and 3.5.1. Its statement asserts no invertibility theorem.
LeanSearch returned only ordinary adic-completion constructions; LeanFinder returned
uniform completions and `AdicCompletion.map`; Loogle found neither project identifier;
Mathlib grep found no sheaf comparison. Project source searches located the existing
construction; the DAG ownership search found no comparison owner. The blueprint search
returned zero matches. All actual search results are included in the node record.

`def-sf-rational-coefficient-inclusion` owns the existing
`AlgebraicGeometry.Scheme.rationalBalancedCoefficient` with `existing: true`.
It is the continuous coefficient map for `RingHom.ulift i`, acting by pointwise
postcomposition, using the finite extensions' prescribed spectral topologies.
Its source is BS 6.8.2 and 6.8.14; it cites the landed general continuous coefficient-map
owner rather than assuming the balanced-localization theorem. LeanSearch returned
general postcomposition maps; LeanFinder returned unrelated p-adic continuity lemmas;
Mathlib grep had no exact map. Project source search found this exact definition and
DAG search found only theorem ownership. The blueprint search returned zero matches.
This attaches a definition owner to the published definition; no module is copied.

## Returned-delivery repair

The repair starts from returned immutable head `4017973c0e18`. Comparing the retained
node with current main found no differences outside its permitted `lean` and `stmt_deps`
fields. The statement, proof and proof dependencies remain byte-for-byte unchanged.

1. H2(1): replace `lem-sf-locally-finite-adic-constructible-realization` by the landed
   `def-sf-locally-finite-adic-realization-data`. The module still uses exactly
   `abRing`, `ringSheaf`, `embedding` and `CoefficientPresentation`; it does not
   assume the realization theorem.
2. H2(2): replace `lem-weil-finite-free-completed-scalar-comparison` by the new
   `def-sf-completed-scalar-comparison-data` and landed
   `def-weil-completed-integral-scalar-data`. Use their transparent aliases for the
   same residue-normalized map and unique quotient-chain-map comparison.
3. H2(3): replace `lem-per-rational-scalar-balanced-localization` by
   `def-sf-rational-coefficient-inclusion`. Its declaration remains the same
   continuous postcomposition definition, with no appeal to the theorem's conclusion.
4. H4/H9: change `scalarCommShift` from a global instance to an ordinary definition
   registered with `attribute [local instance]`. This is the local-instance repair
   expressly permitted by the return. All statement expressions keep the same selected
   normalized shift as the reviewed version, while importers retain their original
   `pbcLevelwiseScalarCommShift` and receive no competing global instance.
5. Advisory owners: add `def-weil-proetale-inverse-image`,
   `def-weil-derived-complete-integral-detailed`, `def-weil-pbc-adic-lisse-module`,
   `def-pc-kflat-complex` and `def-weil-linear-scalar-localization`.

Repair rereading: the main theorem's textual signature and all mathematical hypotheses,
conclusions and edge cases are unchanged. The two completed-scalar aliases unfold to
the formerly used definitions. The shift is exactly the same term, but its registration
is local. The new definition nodes describe constructions already present in the
published source; neither asserts a previously unstated comparison isomorphism.
The dispatcher still forbids another agent, so this is an in-thread rereading and the
maintainer supplies the independent review.

Validation: the repaired two-module packet compiled with scompile.py, including
separate sandbox and actual library-name checks, with no errors or warnings. The new
definition module compiled in 8.7 seconds under its library name; the main module
compiled in 36.4 seconds. The local shift definition uses `@[instance_reducible]`,
matching its intended use and avoiding the class-definition reducibility warning.
All delivered Lean lines are at most 100 characters. The dependency-closure audit found
no cycle, and both new nodes cite exactly the definition ids in their statements.
