## Worker report

The module states `SSet.Enhanced.Algebroid.FixedDG.fixed_object_enriched_rectification`.
The node statement is unchanged. The only postponed theorem is this theorem. Its docstring
contains the eight-step proof of the node, including the free-path signed-reversal comparison,
localization descent, monadic comparison, restriction coherences and H^0 calculation.
All supporting definitions have actual data; structure fields package the conclusion, not
extra hypotheses. The maintainer independently reviews this delivery.

Clause-by-clause correspondence:

- A set S: `S : Type u`, for arbitrary explicitly bound u. The module treats every small
  set at once because naturality in sets is part of the conclusion. Complex modules have
  size u, the derived operad size u+2 and its category of categories size u+3. `ULift ℤ`
  only raises the coefficient ring's size; its canonical ring isomorphism with ℤ identifies
  these with all integral modules of the chosen size.
- Unbounded cochains and their quasi-isomorphisms: `IntegralCochains`, defined by the
  existing `IntegralDerivedCoefficients` module as `CochainComplex (ModuleCat (ULift ℤ)) ℤ`.
  `D.isLocalization` is the full coherent localization at `HomologicalComplex.quasiIso`.
  The public projective-chain-model dependency supplies the projective model convention.
- Strict enriched categories on exactly S: `Cat S` is Mathlib's `EnrichedCategory` on S.
  The fields `Hom`, `id`, `comp`, `id_comp`, `comp_id`, `assoc` are its full mapping,
  chain-map composition and unital associative laws. There is no skeletal or object-isomorphic
  substitute. `FixedDG.Hom` has only maps on mapping complexes and their two compatibility
  equations; its object function is identically the identity.
- FF_S: `FF S F := ∀ s t, QuasiIso (F.map s t)`. `source S` is the enlarged nerve of this
  actual ordinary category, and `Rectification.isLocalization` states its infinity localization
  at this very class, universally on full coherent functor categories.
- The lists operad and projection: `objects S` is the discrete simplicial set on S (with
  a degreewise universe lift), and the recorded `Algebroid.domain` and `projection` are the
  relative nerve of `[n] ↦ S^(n+1)` with coordinate-selection maps. Thus for a discrete set
  it is precisely the category of labelled lists in the node. `target p S` is the recorded
  `fiberCategory`, namely the full over-base functor category on inert-preserving algebras.
  It uses `IsMonoidalInert` with the consecutive-interval condition, not all base arrows.
- Derived monoidal coefficients: the binder `D : IntegralDerivedCoefficients p` names the
  existing monoidal enhancement, its coherent localization, its derived tensor computed
  on K-flat representatives and its unit normalization. `unit : UnitSection p` is the
  recorded canonical monoidal-unit section. These binders name the monoidal enhancement
  and unit already present in the natural statement; they impose no condition on S or A.
- The equivalence eta_S: `Rectification.eta` and `Rectification.equivalence`, for every S.
- Naturality under every function, including higher compatibility: `restrict f` substitutes
  indices in all strict category data and mapping maps. `algebraRestriction_formula`
  prescribes literal precomposition with `domainMap (objectMap f)` on EVERY internal-hom
  simplex and parameter. `rawDiagram`, `localizedDiagram`, `algebraDiagram` are coherent
  functors on the nerve of all small sets opposite with these object and edge values.
  `localizationTransformation` has components the localization functors.
  `etaTransformation` is one natural EQUIVALENCE between the two coherent diagrams and
  has components exactly eta_S. Its higher simplices supply compatibility for every longer
  string of functions, not just chosen binary commuting squares.
- Cofibrant enriched categories and their mapping complexes: `Cofibrant A` is the defining
  lifting property against mappingwise projective trivial fibrations. `TrivialFibration`
  requires both mappingwise quasi-isomorphisms and degreewise surjectivity. `LocallyCofibrant`
  uses the published `DgProjective` characterization of cofibrant projective complexes.
  `cofibrant_mappingComplexes` supplies this for every cofibrant A.
- Applying monoidal localization to cofibrant enriched categories: `HasCofibrantNormalization`
  fixes every active operation, including length zero, by a cocartesian tensor arrow followed
  by localization of `stringComposition`. `stringTensor` is the forward iterated tensor and
  `stringComposition` is the actual iterated strict composition with terminal unit. Its
  translation into reverse dg order is exactly the Koszul signed reversal, since Mathlib's
  enrichment uses forward tensor order and `Dg.comp` uses the cochain braiding. Composition
  and substitution coherences are those of the actual image algebra functor, not a separately
  imposed multiplication on its homotopy category.
- Fixed-object cofibrant replacement of arbitrary A: `replacement S`, `replacementMap S`,
  `replacement_trivialFibration` and `replacement_cofibrant`. No input local-cofibrancy
  or flatness assumption is made. The replacement components are mappingwise quasi-isomorphisms.
- Mapping object identified with the class of A(s,t): `homComparison` is a specified natural
  equivalence from the localized actual Hom-complex functor `localizedHom D s t` to
  `localization S ≫ eta S ≫ pairEvaluation s t`. It is a whole coherent transformation on
  the source nerve, so its naturality applies to actual mapping chain maps of all enriched
  functors. Apply it also to QA and the natural replacement component to obtain the specified
  replacement comparison L(QA(s,t)) ≃ L(A(s,t)). The normalization uses this SAME Hom edge.
- Closed degree-zero arrows and H^0: `UnderlyingComparison` uses the dependency's actual
  `UnderlyingModel` of unit-valued ordered-string simplices, with its units and composition.
  The auxiliary constant-family presentation is identified by `objectIso` and the full
  `algebra_formula` with the fixed image algebra. `closed` is a functor from the existing
  closed-arrow category, `homology` identifies its Hom sets with actual cohomology in degree
  zero, and `closed_class` sends a closed chain map to its class. `closed_coefficient` pins
  that very arrow to localization of its coefficient chain map followed by `R.homEdge`;
  it excludes an unrelated H^0 set equivalence. `homology_natural` spells out naturality
  under arbitrary identity-on-object enriched functors, including all maps on cohomology.
  Naturality after localization is retained by the full coherent localization property.

Published dependency interfaces used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `HomologicalComplex.quasiIso`; cochains and homology are the recorded cochain convention.
- `Sheaf.CategoryTheory.ProjectiveChainsMonoidalModel`: `projectiveChainsMonoidalModel`,
  its projective complex interface and `HomotopicalAlgebra.DgProjective`.
- `Sheaf.CategoryTheory.CompleteAlgebroid`: `domain`, `projection`, `domainMap`, `IsAlgebra`,
  `overFunctors`, `fiberCategory`, `UnitSection`, `totalForFamily`.
- `Sheaf.CategoryTheory.IntegralDerivedCoefficients`: `IntegralCochains`,
  `IntegralDerivedCoefficients`, `integralDerivedNerveMap`.
- `Sheaf.CategoryTheory.DgDerivedEnrichment`: the already existing `DGRectification.DGCat`,
  `Closed`, `closedClass`, `hoObject`, `hoArrow`, `localizedClosedArrow`; this module defines
  normalized derived enrichment data and does not import the rectification theorem.
- `Sheaf.CategoryTheory.AlgebroidObjectSpaceFibration`: `UnderlyingModel`, `objectPoints`,
  `pointAlgebra`, `orderedLabels`, `orderedVertex`, `underlyingCoefficientArrow`.
- `Sheaf.CategoryTheory.CatInfinityOppositeInvolution`: `catInfinityObject`, `catInfinityArrow`.
  These read the literal object and functor carried by coherent-nerve vertices and edges.
- Existing proof dependencies are imported without public reexport. The fixed-object free
  model and categorical-algebra free-monad nodes have no recorded module, so no proof import
  for those nodes is invented; stage 3 will use them when published.

Searches before writing (no exact match):

- `msearch.py leansearch`: “Localization of categories enriched in unbounded integral
  complexes with a fixed object set at mappingwise quasi-isomorphisms is equivalent
  to categorical algebras in the monoidal derived infinity category”. Eight ordinary
  derived-localization hits; none concerns fixed-object enriched rectification.

- `msearch.py leanfinder`: “Strict enriched categories on a fixed object set localized at
  mappingwise quasi-isomorphisms are equivalent to categorical algebras in the derived
  monoidal infinity category”. Eight hits, all ordinary derived localizations or fixed-target
  homotopy-category quotient facts; none states enriched rectification.
- `msearch.py loogle`: `EnrichedCategory, EnrichedFunctor`. Zero hits; the service reports
  unknown identifier EnrichedCategory. Direct source inspection finds and reuses Mathlib's
  `CategoryTheory.Enriched.Basic` definitions rather than treating that service answer as absence.
- `msearch.py grep`: `fixedObject|FixedObject|fixed.object.*enrich`, within
  `CategoryTheory/Enriched`. Zero hits. Direct ripgrep on Mathlib finds the actual general
  enrichment structures and functors, which are reused.
- Ripgrep in upstream WeilConjectures for the item id: no match. Concept searches for
  fixed objects and rectification found no matching theorem. Searches in lean/Sheaf found
  the general dg enrichment theorem (quasi-equivalences and complete object spaces),
  enriched diagram rectification (a different theorem), and simplicial fixed-object
  categories (a different enriching category); none gives this fixed-object integral lemma.
- Read Haugseng arXiv:1312.3881v4 online, Definitions 2.8--2.9 and 5.1, Proposition 5.2,
  Corollary 3.15 and Example 5.11. The source confirms the fixed-object algebra comparison;
  no source or statement correction is required.

Edge cases checked before writing: S empty gives the single empty strict enrichment and the
empty-domain algebra category, both terminal; singleton S gives associative unital dg algebra
rectification. A zero mapping complex is allowed (including zero identity); all degrees are
integers and there are no boundedness, flatness or finite-generation restrictions. The empty
function, noninjective functions and all identity functions occur in `sets`. Arity zero uses
an actual unit, arity one uses the usual unitor, and arbitrary repeated labels are allowed.
The chosen universe u is arbitrary; neither the object set nor the module size is forced to
be countable or finite. No STATEMENT-DISPUTED issue was found.

The released repair note for this item is a stage-1 proof-splitting note, not an archived
stage-2 interface defect. The current node statement and all proof fields are preserved. A final name search in `dag/lean_names_upstream.json`, upstream sources
and the published project modules found no existing declaration with the delivered name.

The statement-dependency list gains the five already-landed owning nodes of the interfaces
listed above: `def-coef-integral-derived-coefficients`, `def-coef-dg-derived-enrichment`,
`lem-coef-dgcat-free-cell-calculus`, `lem-coef-algebroid-object-space-fibration` and
`lem-coef-cat-infinity-opposite-involution`. This is the landed-node addition authorized
by brief-stage2 §5. Their dependency closures have no path back to this item. There are
no new nodes, no dependency-module repairs and no statement correction.

Validation: the prescribed scompile.py wrapper compiled both its sandbox probe and the
library-path module cleanly (no errors or warnings). Its last reported compiler durations
were 25.9 s and 28.5 s. All 32 declared helpers and the theorem are recorded in lean.declarations;
the only postponed proof is the main theorem. All lines satisfy the 100-character limit.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
