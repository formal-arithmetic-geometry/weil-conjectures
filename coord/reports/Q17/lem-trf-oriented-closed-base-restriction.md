## Worker report

The module `Sheaf.Paper.OrientedClosedBaseRestriction` states
`AlgebraicGeometry.OrientedClosedBaseRestriction.orientedClosedBaseRestriction`.
The theorem and its named site-property helper have `sorry` proofs; all definitions have
real data. The module `Sheaf.Paper.OrientedConstructibleSetSheaf` supplies the absent
finite-set version of the existing oriented finite-stratification definition. It contains
no postponed theorem. There are no statement corrections or disputed statements.

Source checked: the actual author PDF at the URL in the item's `source`, Section 8.1
and Lemma 8.3.1, printed pp. 17–18, and the proof of Lemma 8.3.3, printed p. 19.
Section 8.1 explicitly extends the finite-rectangle definition of Theorem 7.1 to both
sets and modules. Lemma 8.3.1 identifies the actual induced morphism after integral
base change; a closed immersion is the special case here. The proof docstring retains
all twelve steps of the DAG's closed-complement argument, rather than asserting that
an ordinary product of topoi has this property.

Hypotheses and objects, matched individually:

- Schemes and scheme maps: `{X T S : Scheme.{u}}`, `(f : X ⟶ S)`, `(k : T ⟶ S)`.
- Locally Noetherian S: `[IsLocallyNoetherian S]`, exactly pqf-def-locnoeth's recorded
  Mathlib class. Quasi-compact S: `[CompactSpace S]`, without a Hausdorff condition.
- Finite presentation of f: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`. These are precisely the three parts fixed by the convention node,
  not merely local finite presentation plus quasi-compactness.
- Closed immersion k: `[IsClosedImmersion k]`.
- X_T and f_T: the existing `pullback f k` and `pullback.snd f k`. The first projection
  is `pullback.fst f k`; `comparisonBeta` uses the actual pullback condition and the
  recorded `etaleBaseChangeComp` isomorphisms, in their specified directions.
- E_T: `Sheaf (productTopology.{u,v} f k) (Type (max (u+1) v))`, using the recorded
  `ProductSite` and `productTopology`. The helper `productDatum` only packages this very
  category and topology into the existing `AdicSites.Site` structure.
- V_f and V_(f_T): the recorded `VanishingTopos f` and `VanishingTopos (pullback.snd f k)`.
  All underlying transported etale sites are the recorded `EtaleSite` and `etaleBaseChange`.

Every conclusion is in `Assertions f k`, which is a transparent conjunction of the
following clauses, with no extra assumptions:

1. The canonical r:E_T→V_f is `restriction f k`. Its site functor fixes the X and S
   entries and pulls the T entry back along k. Its structural arrows are specified by
   `Comma.map`; no arbitrary map of topoi is assumed or selected. `site_properties`
   states continuity and left exactness with a proof docstring, and `siteMorphism`
   supplies the actual sheaf inverse/direct adjunction.
2. r is the required closed embedding: `Nonempty (restriction f k).direct.FullyFaithful`
   and the displayed equivalence of `direct.essImage F` with `closedComplementObjects U F`,
   where U is exactly `(p₂ f).inverse.obj` of the associated representable of
   `k.openComplement.ι`. The existing `closedComplementObjects` says `U × F → U` is an
   isomorphism. Thus this specifies the actual inverse image of the etale closed subtopos,
   not just an abstractly equivalent source category. Full faithfulness and this precise
   essential image also determine the compatible geometric embedding and its 2-morphisms.
3. The canonical v:V_(f_T)→E_T is `comparison f k`. On triples its site functor pulls
   the X entry back by `pullback.fst f k`, pulls the S entry back by k, and fixes the T
   entry. `comparisonBeta` uses the canonical fibre-product composition comparisons and
   their equality over S. `(comparison f k).inverse.IsEquivalence` is the equivalence
   of topoi asserted by the node.
4. For every set sheaf F on E_T, `IsConstructibleSet f k F ↔
   IsConstructibleVanishingSet (pullback.snd f k) ((comparison f k).inverse.obj F)`
   is exactly identification of finite-stratification constructibility by v inverse.
5. For every set sheaf F on V_f, `IsConstructibleVanishingSet f F →
   IsConstructibleSet f k ((restriction f k).inverse.obj F)` is preservation by r inverse.
6. `∀ (Λ : Type v) [CommRing Λ] [Finite Λ]` covers every finite commutative constant ring,
   without an invertibility or nonzero assumption. `Coeff.{u,v} Λ` is the recorded
   canonical ULift, not a second coefficient ring convention.
7. `comparisonModules f k Λ` is the canonical constant-module inverse image, with scalar
   transport by `realizationRingIso.hom` on its source. Its `IsEquivalence` records the
   module equivalence. The following biconditional uses the recorded `IsConstructible`
   on E_T and recorded `IsConstructibleVanishing` on V_(f_T), so both directions of
   constructibility identification are present.
8. `restrictionModules f k Λ` is the canonical r inverse on modules, followed by
   `realizationRingIso.inv` scalar transport to the existing E_T module presentation.
   The last implication is preservation of the recorded constructibility by r inverse.
9. The main theorem concludes the conjunction `Assertions f k ∧ ∀ (Z : Scheme.{u})
   (i : Z ⟶ X) [IsClosedImmersion i], Assertions (i ≫ f) k`.
   Thus every preceding assertion, for sets and modules and both canonical maps, applies
   to Z_T=Z×_S T as required. No separate finite-presentation assumption on Z→S is added.

The set definition's clauses are explicit: `sX` and `sY` are the existing finite scheme
stratifications; both `Topology.IsConstructible` conditions are retained; `rectangleSets`
uses the existing `stratumBaseChange` and sheafified left Kan extension; every rectangle
site object has a covering sieve R, and every member V has a finite model M with an
isomorphism to its constant sheaf on the slice topology. The covering sieve need not
have finitely many members. `IsConstructibleVanishingSet` uses the existing
`vanishingNormalization` to read this same definition on the recorded vanishing site.
It does not replace either module constructibility predicate.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- The convention node fixes `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`;
  the corresponding Mathlib morphism modules supply the binders.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.condition`.
- `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites`: `ProductSite` uses its actual
  `OrientedProduct.largeTriples` and `largeTopology`; its universal theorem is
  `OrientedProduct.universalWithLargeSites`. It is publicly imported by the recorded
  constructibility module.
- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleSite`, `etaleTopology`, `etaleBaseChange`,
  `etaleBaseChangeComp`, `siteMorphism`, `p₂`, `VanishingSite`, `VanishingTopos`,
  `vanishingDatum`, `moduleMorphism`, `Coeff`.
- `Sheaf.Paper.OrientedConstructibleSheafVanishing`: `IsConstructibleVanishing`,
  `vanishingNormalization`, and, by public import of the original module,
  `ProductSite`, `productTopology`, `Modules`, `stratumBaseChange`, `IsConstructible`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, with its actual stratum schemes and immersions.
- `Sheaf.CategoryTheory.Sites.ToposComplementFactorization`: `closedComplementObjects`.
  Its already-landed node is added to stmt_deps for this precise predicate.
- Canonical coefficient transport is the existing `realizationRingIso` in
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor` and
  `SheafOfModules.restrictScalars`.
- Proof-only imports retain the recorded `constant_left_module_inverse_image`,
  `geometric_inverse_image_constant_module`, `etaleClosedComplementSets`,
  `etaleSetInverseImageCompositionUnits`, and `smallEtaleRepresentablePresheaf_isSheaf`.
  The two WeilConjectures modules absent from the older local checkout were read using
  `scompile.py --source`. The unstated proof prerequisite
  `lem-trf-oriented-closed-base-localization` has no module to import and is not needed
  to elaborate this statement. It remains a stage-3 proof dependency unchanged.

Edge cases checked before writing and again against the final signatures:

- T=S, with k the identity: both maps are the canonical identity-base-change normalizations;
  the represented open complement is initial, so its closed complement is the whole topos.
- T empty, or X empty, or Z empty: the appropriate topos is degenerate. Covering sieves and
  finite set models still make sense; no point, nonemptiness or nonzero object is selected.
- X_T empty with X nonempty: the comparison is between degenerate topoi; the added
  complementary X rectangle in the reverse-partition proof is degenerate.
- Z=X gives the same assertions again, without a new geometric assumption.
- Nonreduced closed immersions are allowed: all maps use scheme fibre products, without
  replacing them by underlying point sets or reduced subschemes.
- Empty and zero set/module values, the zero ring, and rings whose cardinality is not
  invertible on S are included; no such restrictions appear.
- Scheme universe u and coefficient universe v are independent. All set and module
  sheaves use the existing containing universe `max (u+1) v`, so no size equality has
  been added. Every variable and universe is explicitly bound; autoImplicit is disabled.

Searches made (all remote-search answers are logged in sandbox `searches.jsonl`):

- LeanFinder: "Closed base restriction equivalence of oriented etale products vanishing
  topos and constructible sheaves" returned eight unrelated sheaf restriction and gluing
  declarations. None is this theorem.
- Loogle: "GeometricMorphism, IsClosedImmersion" returned no hits, reporting the first
  identifier unknown to the service. Mathlib grep "oriented.*closed|closed.*oriented"
  under CategoryTheory returned no hits.
- LeanSearch: "oriented product of etale topoi closed base restriction equivalence
  constructible finite set sheaves" returned eight ordinary etale/sheaf declarations,
  not an oriented constructibility predicate or the theorem.
- LeanFinder: "Constructible sheaf of finite sets on an oriented product of etale topoi
  finite stratifications locally constant on rectangles" returned condensed/profinite
  sheaf constructions, not the required predicate.
- Loogle: "CategoryTheory.Sheaf, Finite" returned two module-generating-section facts.
  Mathlib grep "IsConstructible|IsFiniteLocallyConstant" under CategoryTheory found no hits.
- `rg` for the item id and `orientedClosedBaseRestriction|closedBaseRestriction` in
  WeilConjectures, lean/Sheaf and the upstream name index found only documentary references
  in OrientedConstructibleSubquotients, not a matching declaration.
- `rg` for `IsConstructibleSet|rectangleSets|IsConstructibleVanishingSet` in WeilConjectures
  and lean/Sheaf found no existing declarations. The existing module predicate was read
  in full. `def-trf-finite-locally-constant-set-sheaf` defines a different, finite-cover
  condition on one object, not finite-rectangle constructibility; it is not duplicated.
- `tools/blueprint_refs.py search 'constructible set'` returned two unrelated algebraic
  geometry blueprint units. Searching DAG statements with `rg -l` found downstream uses
  of set constructibility but no definition node for the required finite rectangles.
  `tools/blueprint_refs.py ancestor` reports `lem-trf-local-term-locality`.

Validation: both delivered Lean files compiled individually through scompile.py, in
internal dependency order, with no errors or non-sorry warnings. No global build, live
Lean edit, direct git command or shared-repository write was performed.

## New nodes

`def-trf-oriented-constructible-set-sheaf` supplies the missing finite-set rectangle
predicate, in `Sheaf.Paper.OrientedConstructibleSetSheaf`. The source is Orgogozo Section
8.1's explicit extension of Theorem 7.1 to sets, with the covering-sieve local-constancy
condition of Stacks 093Q. It shares the existing triple topology, finite scheme partitions,
stratum base-change functors, constants and vanishing normalization. All three kinds of
search plus the DAG/upstream/side searches above found no declaration of this notion.
There are no dependency repair modules. The item's natural statement, proof, and
proof-dependency list are unchanged; stmt_deps gains this node and the already-landed
closed-complement predicate node.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
