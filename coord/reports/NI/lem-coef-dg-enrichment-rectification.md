## Worker report

NI stage-2 repair of lem-coef-dg-enrichment-rectification, 2026-10-17.
The returned head f8ca1c972bdb supplied a stage-1 split, not a Lean statement.
The sandbox contained brief files but no retained Lean delivery. This repair reads
and preserves the current shared node's mathematical statement and six proof steps.
It supplies DgEnrichmentRectification.lean, DgDerivedEnrichment.lean, their exact node
records, and this report. The prescribed delivery wrapper rebases and constructs the
single delivery commit. No direct Git command or repository mutation was used.

The main declaration is
SSet.Enhanced.Algebroid.DGRectification.dg_enrichment_rectification.
Its sole postponed proof is `by sorry`. All definition data in the supporting module
are explicit structures, existing constructions, or concrete functors; none are chosen
from a theorem whose proof is sorry. Functor-law proofs inside concrete definitions
are definitional calculations. Every declaration has its source and owning blueprint
id in its docstring. The theorem docstring follows all six existing DAG proof steps,
including the roof argument in step 5.

Clause-by-clause reading of the item and both modules:

- Small integral dg categories: `DGCat := Dg.Cat (ULift ℤ)` uses the existing strict
  enriched categories, their Hom cochain complexes, composition chain maps, units,
  associativity and unit laws. `u` bounds the object types and Hom modules. The
  canonical lift of the integer ring is the convention of the already landed
  integral-coefficients interface; there is no characteristic, connectivity or
  boundedness restriction. Cochain indices are `ℤ` and the shape is `ComplexShape.up ℤ`.
- Quasi-equivalence: `quasiEquivalences` requires `QuasiIso (F.map x y)` for all
  `x,y`, and, for every target object `y`, a source object `x` and an actual degree-zero
  cycle `c : B(Fx,y)^0` with `Dg.IsH0Iso c`. The explicit cycle equation is needed:
  the existing `IsH0Iso` records inverse and boundary data but does not itself assert
  that the input is closed. This is exactly essential surjectivity on H^0.
- The enhanced D(Z) with derived tensor is `IntegralDerivedCoefficients p`.
  Its `localization` is a simplicial map satisfying the full coherent localization
  property. Its tensor comparison is the derived tensor on K-flat representatives,
  with the ordinary unit normalization. It is not the ordinary category
  `DerivedCategory`. The original dependency `DerivedCategory` supplies precisely
  the cochain/quasi-isomorphism convention, as its node says.
- The target `Cat_D(Z)` is the existing `completeCategory.{u,u+2} unit`.
  It is the full subcomplex of actual varying-object categorical algebras satisfying
  completeness, with their coherent morphisms. Its object-space bound stays at `u`;
  only the ambient simplicial universe is enlarged to `u+2`. Thus all small dg
  categories, including the empty one, are within the asserted size convention.
- The displayed infinity-category equivalence is stated in its equivalent universal
  form `IsLocalization quasiEquivalences R.comparison`. This is the existing
  FiniteReedy definition: quasicategory target, inversion, and equivalence from its
  full coherent functor category into every quasicategory to the full subcategory
  of quasi-equivalence-inverting diagrams. It characterizes exactly the displayed
  infinity localization with this specified comparison functor.
- The construction is functorial in every dg functor: `Enrichment.comparison` is
  one simplicial map out of the enlarged nerve of the whole dg category category.
  `points` is a single coherent map on its category of marked objects. `pairs`
  marks the corresponding two points on every simplex, not only at vertices.
  `pairs_source`, `pairs_target`, `points_over`, and `pairs_over` fix the projections.
- Mapping complexes go to their classes: `homComplex` is the actual functor on
  the category `Pairs` of dg categories with two marked objects. Its arrow is
  `F.map x y` followed by the endpoint equality transport in the category of
  elements. `homDiagram` evaluates the actual image algebroid at the marked
  points: `hom_formula` states the equality on every simplex, not an unrelated
  coefficient object. `homComparison` is an equivalence edge in the coherent
  functor category from `dgNerveMap homComplex ≫ D.localization` to that diagram.
  It therefore includes arbitrary object functions, actual chain maps and all
  their coherent compositions.
- Closed degree-zero arrows: `Closed A` is the recorded `ForgetEnrichment`
  category, so its arrows are actual chain maps Z[0] to A(x,y). `closedClass`
  applies `homologyMap` at 0 and evaluates the canonical class of 1 via
  `singleObjHomologySelfIso`. `UnderlyingComparison.closed` is a functor into the
  actual underlying homotopy category, with its object assignment fixed by
  `closed_object` and `vertex_label`. `closed_class` fixes its class as exactly
  `closedClass f`; the `eqToHom` terms spell out both endpoint transports.
- The arrow is the underlying arrow of the enrichment: `closed_coefficient`
  supplies an edge representing `(closed A).map f`; `underlyingCoefficientArrow`
  of that edge is a composite of the SAME `unitComparison`, the localization of
  the actual chain map f (`localizedClosedArrow`), and the SAME Hom comparison
  (`R.homEdge`). The two `Composes` witnesses are actual 2-simplices.
  This prevents an arbitrary relabeling of H^0 morphism sets.
- H^0 of the underlying category: `UnderlyingComparison.underlying` uses
  `UnderlyingModel unit (R.algebra A)`, whose ordered-string simplices use the
  actual algebra's operations. `homology` is a bijection between its homotopy
  category Hom sets and `(Dg.hom ...).homology 0`. Together with `closed_class`
  and the functor `closed`, this preserves identities and products of classes.
  `essentiallySurjective` ensures every underlying object is represented up to
  isomorphism, including after completion.
- The inverted property is exactly `quasiEquivalences`, rather than Morita
  equivalences. No assertion lifts arbitrary ordinary natural transformations.
  Coherence is retained by the simplicial maps, coherent natural equivalence and
  localization on full functor categories. The only ordinary category used in the
  conclusion is the explicitly requested underlying homotopy category.

The presentation binders `{E}`, `p`, `unit`, `D` describe a model of the two objects
already named in the item. They are not extra restrictions on dg categories.
`D` includes the monoidal infinity-category and derived-localization hypotheses;
`unit` is the unit-section choice already required to express complete algebroids.
The conclusion holds for each such presentation, with a normalized unit comparison.

Dependency declarations read and reused (full signatures and docstrings inspected):

- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its quasi-isomorphism localization.
  These are ordinary categories; the enhanced localization here instead uses
  `IntegralDerivedCoefficients.localization` and `FiniteReedy.IsLocalization`.
- Sheaf.CategoryTheory.CompleteAlgebroid: `UnitSection`, `total`,
  `universalFamily`, `familyPower`, `pairParameter`, `IsComplete`, `completeCategory`.
  The completeCategory signature retains the two independent size parameters.
- Sheaf.CategoryTheory.IntegralDerivedCoefficients: `IntegralCochains` and
  `IntegralDerivedCoefficients`, including monoidal, localization, isLocalization,
  tensor, tensor_transport, tensor_representatives and unit_normalization.
  The current source was also read using `scompile.py --source`.
- Sheaf.CategoryTheory.DgCategoryFreeCellCalculus: `Dg.Cat`, `Dg.Fun`,
  `Dg.catCategory`, `Dg.hom`, `Dg.objects`. Their real enriched structures are reused.
- Sheaf.CategoryTheory.DgCategoryEquivalenceCellCalculus: `Dg.IsH0Iso` with its
  closed inverse and degree-minus-one boundary witnesses.
- Sheaf.CategoryTheory.AlgebroidObjectSpaceFibration: `totalProjection`,
  `UnderlyingSimplex`, `UnderlyingModel`, `underlyingCoefficientArrow`. Its full
  theorem and the ordered-domain/labels construction were read to check that the
  underlying composition belongs to the given algebra, rather than an arbitrary
  quasicategory with matching Hom sets.
- Sheaf.CategoryTheory.FiniteReedyLocalization: `largeNerve`, `IsLocalization`,
  `Composes`, `object`. The universal property is on full coherent functor categories.
- Mathlib.CategoryTheory.Elements: `CategoryOfElements.π`, `NatTrans.mapElements`.
  Mathlib.Algebra.Homology.SingleHomology: `singleObjHomologySelfIso`.
  Mathlib enriched categories, enriched functors and forget-enrichment are reused.
- Sheaf.CategoryTheory.EnrichedCompletionLocalization is the existing recorded
  proof dependency for passage to all algebroids and completion; its statement and
  docstring were read. Its result is only cited in the postponed proof description.

Source reading: Haugseng, arXiv:1312.3881v4, online HTML, Definition 5.1,
Proposition 5.2, Theorem 5.4, Definition 5.6, Corollary 5.7, Theorem 5.8 and
Example 5.11, including the unbounded case after Example 5.10. The fixed-object
rectification assembles over sets, FFB is the first inverted class, and the second
localization uses precisely weakly fully faithful essentially surjective maps.
Taking the commutative ring Z gives this item; no field or flatness assumption is
present. The source remains an online reference, not an archived literature file.

Edge cases checked before the final statement:

- Empty dg category: no point or pair is required; no nonexistent chosen basepoint.
  Essential surjectivity of its underlying comparison forces the underlying category
  to have no objects up to equivalence, as required. Empty-to-nonempty is not a
  quasi-equivalence, while empty-to-empty is.
- Zero Hom complex and zero classes: homology is the zero module; the class map
  evaluates the actual map on 1, including the zero map. No nonzero identity or
  distinct-object assumption is imposed (a zero dg object is permitted).
- Nonflat and unbounded Hom complexes: no `KFlat`, projectivity or bound is imposed
  on A; the coefficient datum uses K-flat representatives only to describe derived
  tensor, and the proof uses cofibrant replacement.
- Arbitrary object functions: the category of elements includes identifications
  and nonbijective functions. Neither the definition nor conclusion asks for a
  bijective-on-objects dg functor, except as the intermediate proof class FFB.
- Cycles differing by boundaries: `closedClass` passes through H^0; closed arrows
  are not falsely identified as chain maps. `closed` preserves actual composition
  and identities, while its target identifies homotopic edges.
- Universe bounds: dg object types and Hom modules are at u; DGCat is Type(u+1)
  with morphisms Type u; large nerves and coefficients are at u+2. The target's
  small object-space parameter is u, not u+1. No equality of unrelated universes
  is imposed and no extra smallness class restricts the input dg categories.

Searches actually run:

- `msearch.py ... leanfinder 'Localization of differential graded categories at
  quasi equivalences as derived enriched infinity categories'`: eight ordinary
  derived-localization candidates, no rectification declaration.
- `msearch.py ... loogle 'EnrichedCat, HomologicalComplex'`: zero hits, with unknown
  identifier EnrichedCat; this unsuccessful parser/name query is not treated as
  an exhaustive search.
- `msearch.py ... grep 'dgCat|quasi.?equivalence|rectification'`: zero Mathlib hits.
- `msearch.py ... leansearch 'Natural derived enrichment of dg categories preserving
  mapping cochain complexes and closed arrow cohomology classes'`: eight candidates,
  including HasDerivedCategory.standard, DerivedCategory.instCategory, ordinary
  right-derived natural transformations and HomComplex lemmas; none is the interface.
- `msearch.py ... leanfinder 'Normalized coherent dg category enrichment with mapping
  complex localization'`: eight candidates, including HasDerivedCategory,
  SSet.QCat.catEnrichedOrdinaryCategory, DerivedCategory.Q and ordinary localization
  instances; none defines this comparison or theorem.
- `msearch.py ... grep 'DGRectification|DgDerivedEnrichment|quasiEquivalences|UnderlyingComparison'`:
  zero Mathlib hits. The same rg query on WeilConjectures has no matches; on
  lean/Sheaf it only matches an import of DerivedModuleUnderlyingComparison, a
  different sheaf-module construction. Actual complete output is in the new node.
- Item-id and derived/enrichment/differential-graded searches of the upstream source
  and lean/Sheaf found the related dg cell and complete-algebroid interfaces reused
  above, but no exact item or normalized derived-enrichment definition.
- `blueprint_refs.py search 'derived enrichment'` and search for the item name:
  zero blueprint matches; ancestor is prop-coef-integral-exceptional-adjoint.
  Searching node files for the new id found none. Related fixed-object,
  fibre-assembly and completion nodes are theorems, not this definition.

No statement correction was needed. No STATEMENT-DISPUTED assertion was found.
No dependency was privately redefined or repaired. The new definition's dependency
paths were checked against the item: none reaches it, so no cycle is introduced.

Repair mapping: H2/H3 are addressed by the actual stage-2 theorem, concrete helper
module, exact lean records and unchanged item mathematics. H1 is addressed by the
required files and report sections; H11 by the detailed second reading below; H8
by source/blueprint docstrings on every declaration and the theorem's full six-step
natural-language proof. Compilation and preflight evidence is recorded below.

## Second reading by NI

This is a separate second pass by the same dispatcher-started worker, with the node,
new node and both complete Lean files open. The explicit dispatcher instruction
forbids starting other agents; no second person or agent is claimed. The maintainer's
independent delivery review is still required.

I reread the source's Theorem 5.8 and unbounded-chain Example 5.11, then checked the
node sentence by sentence against the final declarations. The dg category notion
is the existing enriched category, not merely its underlying ordinary category.
The quasi-equivalence predicate includes both mappingwise quasi-isomorphisms and
closed H^0-invertible arrows to every target object. Its cycle equation is explicit.
The derived coefficient localization and tensor are the recorded enhanced datum,
while completeCategory is the recorded target. The conclusion IsLocalization states
the full infinity localization at precisely that predicate. The Enrichment witnesses
supply one functor and its all-simplex natural Hom comparison; they are conclusions,
not added hypotheses on A. UnderlyingComparison ties its actual ordered-string
underlying category to closedClass using a functor, Hom bijections, endpoint
transports, and the coefficient triangles with the same Hom comparison. This covers
the class and underlying-arrow clauses simultaneously. Its essential surjectivity
retains every underlying object, and the full functor-category universal property
retains coherent transformations without asserting lifts of ordinary transformations.

Mismatches caught and repaired during this reading: (1) the target smallness parameter
must be u rather than u+1, even though ambient coefficients live at u+2; it is u in
the final signature. (2) a bare bijection of Hom sets would not normalize closed
arrows; closed_coefficient now ties their chain-map localization to the same
homComparison and the actual underlying algebra. (3) object equalities of a marked
pair require both endpoint transports; homComplex.map uses the category-of-elements
property explicitly and its identity/composition laws were compiled. (4) closed
functor endpoint objects need explicit transport in closed_class; both are present.
The second reading also checked that the new node states these same data, carries
only definition fields and cited notions, and introduces no deferred theorem.

## New nodes

`def-coef-dg-derived-enrichment` defines the normalized derived-enrichment datum and
its underlying H^0 comparison, including the concrete category of marked pairs and
quasi-equivalence predicate. It supplies the missing vocabulary needed to state the
item. Source: Haugseng Definition 5.1, Theorem 5.4, Definition 5.6, Theorem 5.8 and
Example 5.11. It uses the already recorded dg categories, integral derived coefficients,
complete algebroids and unit-valued ordered-string underlying categories, rather than
copying them. The searches recorded above and in mathlib_searches found no existing
node or declaration of this normalized datum; ordinary derived categories and strict
QCat enrichment do not define it. Its ancestors and source remain those of the item.
Its real data are `Enrichment` and `UnderlyingComparison`; the item's theorem asserts
their existence with the specified localization property. No new theorem node is
needed because the only existence theorem is exactly the item under repair.

Compilation evidence, 2026-10-17: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NI lem-coef-dg-enrichment-rectification lean/Sheaf/CategoryTheory/DgDerivedEnrichment.lean lean/Sheaf/CategoryTheory/DgEnrichmentRectification.lean`.
The final run exited 0 with no errors and no warnings. It compiled both delivered
files separately in dependency order, including sandbox and library checks. The
library checks reported 11.1 seconds for DgDerivedEnrichment and 2.8 seconds for
DgEnrichmentRectification. The earlier unused-simp warning was repaired by removing
`Category.id_comp` from homComplex.map_comp; no linter was disabled. The final
modules contain zero definition sorries and exactly the item's one theorem sorry.

Delivery dry-run evidence: the prescribed `deliver2.py NI
lem-coef-dg-enrichment-rectification --no-push` exited 0 and printed:
`OK (dry run): commit 3b4577e963 passes the preflight and compiles; nothing pushed`.
Its staged packet contains exactly this report, the item and new-definition node
records, and the two owned Lean modules. No preflight repair was required.
