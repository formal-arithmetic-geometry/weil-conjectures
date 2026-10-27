## Worker report

Item: lem-sp-chart-normalized-model-identification. Module:
`Sheaf.AlgebraicGeometry.ChartNormalizedModelIdentification`.
Only the item's `lean` field changes. The module contains two constructed helper
isomorphisms and one theorem, `chart_normalized_model_identification`, with whole
proof `sorry`. No theorem is proved. No new nodes or dependency repairs are needed.

Source read: current blueprint main-20261015,
`sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
Charts paragraph, and the item's six detailed proof steps. The chart map is the
specified left identification; the ordinary etale comparison and tower construction
are the dependency declarations below, rather than an arbitrary isomorphism.

Hypothesis and clause correspondence:

- A finite commutative torsion ring is `R : Type (u + 1)`, `[CommRing R]`,
  `[Finite R]`. Finiteness implies additive torsion; no nonzero-ring assumption is
  introduced. Schemes have universe `u`, as in the recorded module-sheaf encoding.
- Noetherian U,V,Y are the three `IsNoetherian` binders. Mathlib's class is locally
  Noetherian plus quasi-compact, equivalent to the node's finite affine cover.
- The map e is `e : U ⟶ V` with `Etale`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`; the last two are precisely finite type. The corresponding three
  properties of f express separated finite type. The composite is `e ≫ f`.
- `ce`, `cf`, `cg` are arbitrary `Compactification e`, `Compactification f`,
  `Compactification (e ≫ f)`. No compactification is selected from mere existence.
  Their middle schemes are automatically Noetherian: the proper structure map is
  locally of finite type and quasi-compact over a Noetherian target. Thus separate
  middle-scheme assumptions would be redundant, and none is added.
- F_h is exactly `rightDerivedLowerShriekOfCompactification (ModuleCat R) c`.
  E is `(etaleLowerShriek (ModuleCat R) e inferInstance).mapDerivedCategory`.
  Both act on ordinary constant-ring module sheaves, with the established universe.
- The existential N is a simultaneous `EtaleCompactSupportNormalization R`.
  Its comparisons are explicitly required to equal
  `canonicalEtaleCompactSupportComparison R e ce`, and its sheaf comparisons equal
  `etaleCompactificationGraphMap R e ce`, for every separated etale map of
  Noetherian schemes and every compactification. Such maps are automatically of
  finite type, so the universal quantification covers exactly the maps in the node.
- The graph-extension composite and homotopy-representative formula are the
  `sheaf_normalization` and `derived_normalization` fields of N, with actual graph
  map fixed by the additional equality. Its proper/open single-base-change square,
  successive-base-change square, proper refinement, identity and unique
  counit-preserving identification with sum/evaluation are respectively N's
  `base_change`, `composition`, `refinement`, `identity`, `adjunction` fields.
  These are part of the existential conclusion, never extra hypotheses.
- `chartModelComposition` is alpha on the three specified models: compare ce to
  `(cg.ofComp cf).restrict`, apply
  `rightDerivedLowerShriekOfCompactificationCompIso`, and compare
  `cf.comp (cg.ofComp cf)` to cg. This is the normalized proper/open compositor
  of def-sf-etale-support-compositor, expressed directly for the specified models.
  Its restriction is the canonical bounded-below compositor by
  `unboundedEtaleCompactSupport_composition_plus` and
  `unboundedEtaleCompactSupport_comparison_plus`; the module imports their owner
  as a proof dependency.
- `chartNormalizedModelComparison` is exactly lambda, the composite
  `Functor.isoWhiskerRight (N.comparison e ce).symm _` followed by the preceding
  alpha. These are real constructions of isomorphisms, without any postponed data.
- The first chart conclusion equates lambda's `.hom.app (Plus.ι.obj K)` with
  `etaleAmbientLeftComparison R N e f cf cg` at that same object, for every K in
  `DerivedCategory.Plus`. Equality of every component is equality of the restricted
  natural transformations. Its inverse follows because both maps are isomorphisms.
- All three primed compactifications are independently universally quantified.
  The next two equalities are, in Lean's left-to-right composition order,
  `rho_e ≫ c'_e = c_e` and `rho_f(E K) ≫ lambda'_K = lambda_K ≫ rho_g(K)`.
  Each rho is the existing canonical pairwise compactification comparison, not a
  freely supplied natural isomorphism. They compare actual arrows in the derived
  category, rather than only their cohomology.
- The last conjunct gives the identity and cocycle equations for these actual
  pairwise comparison components on every bounded-below input. Its final clause
  identifies the pairwise comparison with the transported composite through EVERY
  common refinement t and EVERY pair of refinement maps r,s. The transports are
  `rightDerivedLowerShriekOfCompactificationPlusCompatibility`, with inverse on
  the source and hom on the target. Consequently both chart equations use the same
  rho for any common refinement, and their successive/identity pastings are governed
  by the stated cocycle/identity equations. No cartesian or density restriction on
  r,s is imposed.

Dependency declarations read and used:

- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and its category; refinement maps
  commute with the source open and target structure map and are automatically proper.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and the coefficient module:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; the underlying `DerivedCategory`
  and `DerivedCategory.Plus` are the existing ordinary module-sheaf categories.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, and its PlusCompatibility.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `etaleLowerShriek`, the sum/sheafification extension. Its exact degreewise descent
  is the recorded E, not a replacement functor.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`:
  `EtaleCompactSupportNormalization`, all nine fields, and
  `nonempty_etaleCompactSupportNormalization`. This single published structure
  supplies both normalization-definition and normalization-existence dependencies.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`, and its upstream
  LowerShriekComposition/LowerShriekCoherence modules:
  `etaleCompactSupport_refinementComparison_eq`,
  `rightDerivedLowerShriekPlusCompIso`,
  `rightDerivedLowerShriekOfCompactificationPlusRefinementIso`,
  `rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`, and their
  identity/cocycle equations. The refinement iso is oriented from coarser to finer.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `etaleAmbientLeftComparison`, whose three factors are the inverse N comparison
  at the restricted closure, proper/open tower and final pairwise comparison.
- Proof dependencies: NormalizationData's `compactSupportComparisonOnHomotopy` and
  `compactSupportDerivedComparison`; GraphSheafNormalization's
  `compactSupportGraphSheafComparison_normalization`; GraphDerivedIso's
  `canonicalEtaleCompactSupportComparison` and `canonicalEtaleCompactSupportCore`;
  GraphCoherence's `etaleCompactSupportGraph_coherence`; and
  UnboundedEtaleCompactSupportComparisons' compositor tower, refinement normalization,
  comparison coherence, and comparison/composition Plus restriction theorems.
  These modules are imported (public only when used in the exposed signatures/data).
- The finite-type-over-Noetherian dependency is a Mathlib leaf:
  `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace`, read in Noetherian.lean and
  Morphisms/QuasiCompact.lean, give the middle-scheme facts. No private definition
  of Noetherianity is introduced.

Edge cases checked: empty source and empty geometric fibres are allowed by the
sum-extension and graph constructions; no surjectivity or density assumption is
present. The identity map and identity compactification are included, with identity
rho. Equal compactifications, arbitrary nondense common refinements, and three
successive choices are included by the final equations. The zero coefficient ring
is included. No lower bound is fixed on K, so every bounded-below complex, including
zero and arbitrary shifts, is covered. No characteristic restriction is added.

Searches actually run through msearch.py (Q81, this item):

- leanfinder: `Graph normalized etale compact support agrees with restricted closure
  chart comparison and is invariant under independent compactifications`: eight
  results about smooth bump functions/compactly supported maps, no matching theorem.
- loogle: `CategoryTheory.Functor.isoWhiskerRight, CategoryTheory.Functor.whiskerLeft`:
  four results on presheaf-module pushforward/pullback associativity, no chart theorem.
- grep: `etaleAmbientLeftComparison|canonicalEtaleCompactSupportComparison|normalized.*[Cc]hart`:
  zero Mathlib matches.
- leansearch: `Derived compact support graph comparison equals etale sum extension
  and is independent of compactification`: eight results on topological compact
  support, no matching theorem.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for the graph-comparison and ambient
  chart-map names found the existing constructions, which this module reuses.
  The private equality in EtaleHorizontalSupportMate only identifies N's comparison
  with the canonical graph comparison; it does not state this node's chart and
  independent-compactification package. No existing complete theorem was found.
- grep -rn for the item's id in `lean/WeilConjectures`: no match. rg for the three
  proposed declaration names in project/upstream names: no match before this file.

No STATEMENT-DISPUTED flag and no statement correction. The theorem's docstring
contains the six proof steps, with the matching dependency names and orientations.
All variables and the universe are explicitly bound; autoImplicit is false.
The final server scompile check passed for both sandbox and library module, with
no errors or non-sorry warnings. Only prescribed wrappers compile this delivery.

## Second reading by Q81

Author's second pass (no subagent, as required by the dispatch); independent
maintainer review remains the actual independent reading. Reopened the node,
recorded dependency signatures and final file. The normalization existential is
simultaneous, fixes both graph maps, and includes all normalization fields through
its existing structure. The comparison domain is D+ via Plus.ι, and all primed
compactifications remain independent. Checked the order rho then c', rho_f then
lambda', versus lambda then rho_g. Found that identity/cocycle were initially
stated on all unbounded objects: restricted those clauses to Plus inputs to avoid
strengthening the node. Added the explicit comparison-through-any-refinement
clause; no assumption that refinement squares are cartesian. Verified the source
transport is inverse and target transport is hom against PlusCompatibility's
signature. Checked helper bodies contain no sorry and the sole theorem's whole
proof is sorry. Node's signature is extracted verbatim; all other node fields are
unchanged. No new definition nodes or dependency modules were introduced.
