## Worker report

This delivery states the ordinary unbounded etale compact-support comparison package in
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`. All new theorems have
`sorry` proofs, and all definitions have actual data assembled from existing canonical
functors, isomorphisms and adjunctions. The main theorem docstring also retains all twelve full DAG proof steps and their named dependencies.
The node's natural-language statement and all its
other fields are unchanged. No independent notion, new node or dependency repair was needed.

Sources read: Stacks [0F7H](https://stacks.math.columbia.edu/tag/0F7H),
[0F7I](https://stacks.math.columbia.edu/tag/0F7I),
[0F7J](https://stacks.math.columbia.edu/tag/0F7J),
[0F7L](https://stacks.math.columbia.edu/tag/0F7L), and the existing source signatures and
construction bodies for their proper/open tower. The source proves the unbounded torsion-ring
case by the same compactification argument as the bounded-below torsion case.

### Every hypothesis and clause

All declaration names below are in `AlgebraicGeometry.Etale` unless specified otherwise.

| Node text | Lean rendering |
| --- | --- |
| Finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]` on the asserted comparison/coherence package. Auxiliary exact-functor definitions need only `CommRing A`. |
| Small etale sites and constant-ring module sheaves | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`, the six-functor encoding recorded by def-weil-pbc-derived-categories; not a pro-etale or condensed category. |
| Ordinary unbounded derived categories | `DerivedCategoryModule A X`, definitionally `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`. No boundedness predicate occurs in the unbounded assertions. |
| All schemes Noetherian, finite affine Noetherian covers | `[IsNoetherian X]`, etc., on each theorem. `IsNoetherian` is local Noetherianity plus compactness; Mathlib's finite-affine-cover equivalence is `isNoetherian_iff_of_finite_affine_openCover`. |
| Each compact-support morphism separated, finite type | `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`, and the corresponding binders for g and h. These properties of composites, identities and cartesian pullbacks follow from the supplied maps; explicit pullback quasi-compactness witnesses are only consequences of these hypotheses. |
| Compactifications supplied | `Compactification f` for a specified candidate or `[HasCompactification f]` for the chosen candidate. Identities, composites and pullback compactifications are named wherever their compact-support functors occur. These are the node's compactifiability assumptions, not arbitrary choices of natural isomorphisms. |
| Candidate Rf!^c = Rr* Dj! | Existing `rightDerivedLowerShriekOfCompactification (ModuleCat A) c`, definitionally the exact degreewise open extension followed by the unbounded total right derived direct image. |
| Canonical proper-refinement isomorphism, identity on X | Existing `rightDerivedLowerShriekOfCompactificationIso A d c`; `unboundedEtaleCompactSupport_refinement_normalization` identifies its hom with the graph-normalized open comparison for an arbitrary refinement r, followed by ambient direct image and its canonical composition comparison. The graph comparison is the identity on the source open. No Cartesian or density hypothesis is added to r. |
| Identity/composite refinements, independence of common refinement, cocycle | `unboundedEtaleCompactSupport_comparison_coherence`: pairwise comparison c→c is `Iso.refl`, and c→d→e is c→e. With the preceding arbitrary-refinement normalization this gives identity and composite refinement laws, and comparison through any common refinement equals the same pairwise isomorphism. The upstream pairwise comparison is concretely constructed through `Compactification.inf`. |
| Compactification-independent Rf! | Existing `rightDerivedLowerShriek (ModuleCat A) f`, the chosen candidate, together with existing `rightDerivedLowerShriekIso A c` from every specified candidate. The preceding equations establish the claimed independent meaning. |
| Canonical composition alpha | `unboundedEtaleLowerShriekCompIso A f g` is an actual natural isomorphism `Rf! ⋙ Rg! ≅ R(f ≫ g)!`. Its body is the explicit `ofComp` tower used in the existing unbounded composition proof. No `Classical.choice` of an unnormalized isomorphism is used. |
| Composition independent of choices and compatible with refinements | `unboundedEtaleLowerShriekCompIso_tower` computes alpha on every compactification d of g and every compactification e of f followed by d.i. All three transports are the existing pairwise comparisons. Combined with the pairwise cocycle it gives compatibility for any refinements of the three candidates and independence of the selected compactifications. |
| Proper/open tower normalization | The same theorem uses exactly `rightDerivedLowerShriekOfCompactificationCompIso A d e`: its body is Rs* of `openImmersionLowerShriekLowerStarExchange`, followed by `rightDerivedLowerStarComp` and `mapDerivedCategoryOpenImmersionLowerShriekComp`. `e.restrict` has V = pullback e.g d.i, its proper projection q and its open j, and `d.comp e` is the required composite compactification. |
| Interchange adjunct to inverse proper open-restriction exchange | `unboundedEtaleCompactSupport_tower_adjunct`: the open-adjunction transpose of that precise interchange, composed with `unboundedEtaleProperOpenRestriction`, is the identity. The latter is exactly `exactDerivedBaseChangeMap` followed by Rq* of the inverse open unit. Since the tower interchange and open units are isomorphisms, this is precisely the claimed inverse normalization. |
| Composition identities and associativity | `unboundedEtaleLowerShriekCompIso_units` gives both unit equations using the identity compactification; `unboundedEtaleLowerShriekCompIso_assoc` gives equality of the two triple composites, including the functor associator and the scheme-morphism associativity congruence. |
| Cartesian square with arbitrary change of base v | `(sq : IsPullback v' f' f v)`; this covers the chosen fibre product and every isomorphic cartesian square. No properness, finite type, etaleness or residue-characteristic condition is imposed on v. |
| Unbounded exchange is an isomorphism | `unboundedEtaleCompactSupport_baseChange` asserts `IsIso (unboundedEtaleCompactSupportBaseChange A sq)`. An isomorphism of natural transformations gives an isomorphism at every unbounded K. |
| Chosen-compactification exchange formula | `unboundedEtaleCompactSupport_exchange_normalization`: exact proper exchange from def-kun-unbounded-exchange, followed by inverse `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`. |
| Open factor is the named beta, degreewise and inverted | `unboundedEtaleCompactSupport_open_beta` identifies the underived open map used in that descended isomorphism with `etaleLowerShriekBaseChangeMap A v j` for the canonical fibre product. Both are the inverse conjugate of the same underived exchange. The canonical pullback-square version is used for compactification ambients. |
| Exchange independent of compactification | Second conjunct of `unboundedEtaleCompactSupport_baseChange`: its formula holds for every c, using the corresponding pairwise source and target comparisons. Thus any refinement or common-refinement presentation gives the same map. |
| Identity change of base | `unboundedEtaleCompactSupport_baseChange_id` inserts the exact inverse-image identity comparisons and gives the identity transformation. |
| Composite changes of base | `unboundedEtaleCompactSupport_baseChange_comp` gives the explicit whiskered composite, with exact termwise inverse-image composition identifications at both ends. The displayed outer cartesian witness is redundant geometric data determined by the two inner squares, not an additional condition on v or w. |
| Compatibility of exchange with alpha | `unboundedEtaleCompactSupport_baseChange_composition` equates the exchange after alpha with the two exchanges followed by the base-changed alpha. Every associator is displayed. The outer square is the pasted square. |
| Restrictions of comparisons to bounded-below inputs | `unboundedEtaleCompactSupport_comparison_plus`: equality of components after the existing `rightDerivedLowerShriekOfCompactificationPlusCompatibility` maps. This compares the exact upstream maps named by lem-amb-etale-compact-comparisons. |
| Restriction of composition to bounded-below inputs | `unboundedEtaleCompactSupport_composition_plus`: equality with `rightDerivedLowerShriekPlusCompIso`, after the canonical inclusion maps and their two whiskerings. |
| Restriction of exchange to bounded-below inputs | `unboundedEtaleCompactSupport_exchange_plus`: equality with `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`, the precise compactification-relative exchange of thm-cbc-finite-torsion. Together with comparison restriction and compactification independence this also identifies the independent exchange. |

The graph-normalization family N in the refinement equation is universally quantified over
families already defined on lem-asd-etale-compact-support-normalization. Its existence for
finite A is the existing `nonempty_etaleCompactSupportNormalization`; this adds no hypothesis
on the schemes or coefficients. The helper `unboundedEtaleRefinementOpenComparison` derives
local Noetherianity and compactness of the ambient from the proper morphism d.g, using
`LocallyOfFiniteType.isLocallyNoetherian` and `QuasiCompact.compactSpace_of_compactSpace`.
Neither is silently required as a new input hypothesis.

### Recorded dependencies read and used

- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`. Uses its recorded DerivedCategoryModule and D+ encodings.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`. Uses Scheme and its morphisms.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`. Used through the finite-affine-cover meaning of IsNoetherian.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`. Uses IsSeparated and IsProper; compactification proper maps supply finite type.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`. Uses LocallyOfFiniteType and QuasiCompact together.
- `def-asd-compactifiable`: `Sheaf.AlgebraicGeometry.CompactifiableOverField`, `AlgebraicGeometry.hasCompactification_of_finiteType_over_field`. Reuses its recorded Compactification/HasCompactification definitions; no field hypothesis is imposed.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`. Uses exactly this unbounded candidate.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`, `CategoryTheory.ringedToposDerivedPushforwardComposition`. Imports its generic ringed-topos result; the existing Etale.rightDerivedLowerStarComp supplies its canonical constant-coefficient implementation inside the tower.
- `lem-cbc-extension-zero-composition`: `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`, `AlgebraicGeometry.Etale.openImmersionLowerShriekComp_coherence`. Uses its existing openImmersionLowerShriekComp through mapDerivedCategoryOpenImmersionLowerShriekComp; its coherence is a structural proof ingredient.
- `lem-amb-etale-adjoint-locality`: `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`, `AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`. Imports the recorded unbounded open/sum adjunction module; uses the existing derivedOpenImmersionLowerShriekUpperStarAdjunction for the unrestricted open instance, with no quasi-compactness assumption on this adjunction.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`. Uses pullback, its projections, IsPullback, ofIsPullback and restrict.
- `def-kun-unbounded-exchange`: `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`, `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`. Uses the exact-derived canonical adjunction mate in both displayed normalization equations.
- `def-weil-pbc-etale-shriek-base-change-map`: `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`, `AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeMap`. The open_beta equation names this exact declaration.
- `lem-amb-etale-compact-comparisons`: `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`, `AlgebraicGeometry.Etale.etaleCompactSupport_refinementComparison_eq`. Uses its recorded pairwise bounded-below and composition declarations, and identifies the actual restrictions.
- `thm-cbc-finite-torsion`: `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`, `AlgebraicGeometry.Etale.compactSupportFiniteTorsion`. Uses its precise bounded-below compactification-relative exchange, supplied by the recorded upstream module.

The full signatures/docstrings and construction bodies were read in the local source and
side project. The published `LowerShriekPlusBaseChange` source, absent in the older local
checkout, was read with `scompile.py --source`. That file gives the exact compactification-
relative exchange and the recorded formalism construction. The current published
`EtaleCompactSupportComparisons` source was also checked through that wrapper.

All recorded statement-dependency modules and every available recorded proof-dependency
module are imported directly. Mathlib proof dependencies additionally import
`DerivedCategory.DerivabilityStructureInjectives`, `DerivedCategory.KInjective`,
`Localization.Predicate`, and `Adjunction.Mates`. The only proof dependency with no
recorded declaration is `lem-amb-unbounded-proper-open-interchange`; it has no importable
module yet. No statement in this delivery depends on an unstated declaration from that
node: the canonical cartesian tower interchange already exists upstream and is used
directly. Its general coherence is the proof plan for these postponed assertions. This
omission introduces no wait or substitute notion.

### Edge cases checked before writing

- Empty schemes, empty opens and empty fibres: no Nonempty, density or surjectivity binder;
  zero objects and empty-fibre exchange remain included.
- Trivial finite rings: no Nontrivial hypothesis; finite rings of every characteristic are
  included, with no requirement that their order be invertible on a scheme.
- Arbitrary unbounded complexes: no IsGE, IsLE, constructibility, finite Tor-amplitude or
  dimension bound in the unbounded conclusions; D+ appears only in the final restriction
  equalities.
- Noncartesian proper refinements: the refinement-normalization theorem assumes only
  `r : c.Refinement d`. Its normalized comparison uses graph extension for the coarser open,
  rather than the upstream Cartesian-only refinement exchange.
- Identity refinements and identity base changes: common-refinement reflexivity and the
  explicit identity base-change equation cover them. Both left and right composition units
  have a specified normalization.
- Successive arbitrary base changes: v and w have no morphism-property instances; only the
  compact-support edges are quasi-compact/compactifiable, as given in the node or inherited
  by base change.
- Universe sizes: `Scheme.{u}`, small etale site, `ModuleCat.{u+1} A` with A in `Type (u+1)`
  use the recorded coefficient convention. All universes and variables are explicit, with
  `set_option autoImplicit false`. No universe equality or extra finiteness is imposed.

### Searches and reuse decisions

- `msearch.py`, LeanFinder, query `Unbounded etale compact support comparison composition
  coherence base change`: 8 hits, all etale morphism/ring etaleness facts and unrelated
  cotangent comparisons, no match for the requested coherence package.
- `msearch.py`, Loogle, query `"shriek"`: 0 hits.
- `msearch.py`, grep, query `lowerShriek|properSupport|compactSupport`, Mathlib subdirectory
  `AlgebraicGeometry`: 0 hits.
- `rg` in upstream `WeilConjectures/SixFunctors` and side `lean/Sheaf`, queries
  `rightDerivedLowerShriek|CompactSupportFormalism|lowerShriekCompIso|compactification`:
  found the candidates, unbounded common-refinement isomorphisms, unbounded tower map and
  exchange, and the bounded-below formalism and coherence. Their exact bodies are reused.
  The unbounded composition result only gives `Nonempty` with an explicit tower construction;
  that very construction is assembled here, without selecting arbitrary data from its proof.
- `rg` for `derivedFormalism|unboundedFormalism|mapDerived.*Formalism` in upstream/side:
  no unbounded compact-support formalism; only the existing graph-normalization family.
- `rg` for the item id in upstream and for the new declaration names in upstream and side:
  no previous declaration of this complete unbounded coherence package and no name collision.
- Read current server source with `scompile.py --source` for the two modules named above,
  so stale local files did not cause replacement definitions or a blocked delivery.

No STATEMENT-DISPUTED flag, statement correction, new node, or dependency module.

### Validation

Single-file compilation uses only the authorized `scompile.py Q28` wrapper, with the ordinary
60-second file limit. The sandbox and library-shaped versions compiled cleanly, including
all bounded-below equality statements; expected sorry warnings alone are permitted. The
required `deliver2.py --no-push` check is the final validation. No push or second-reading
section is authored by this worker.

New declarations recorded: `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleCompactSupportBaseChange`, `unboundedEtaleCompactSupport_comparison_coherence`, `unboundedEtaleRefinementOpenComparison`, `unboundedEtaleCompactSupport_refinement_normalization`, `unboundedEtaleLowerShriekCompIso_tower`, `unboundedEtaleLowerShriekCongr`, `unboundedEtaleLowerShriekId`, `unboundedEtaleLowerShriekCompIso_assoc`, `unboundedEtaleLowerShriekCompIso_units`, `unboundedEtaleUpperStarCompIso`, `unboundedEtaleUpperStarIdIso`, `unboundedEtaleCompactSupportExchange`, `unboundedEtaleCompactSupport_baseChange`, `unboundedEtaleCompactSupport_baseChange_id`, `unboundedEtaleProperOpenRestriction`, `unboundedEtaleCompactSupport_tower_adjunct`, `unboundedEtaleCompactSupport_exchange_normalization`, `unboundedEtaleCompactSupport_baseChange_comp`, `unboundedEtaleCompactSupport_baseChange_composition`, `unboundedEtaleCompactSupport_comparison_plus`, `unboundedEtaleCompactSupport_composition_plus`, `unboundedEtaleCompactSupport_exchange_plus`, `unboundedEtaleCompactSupport_open_beta`.

## Second reading by Q28

I independently read the sandbox node and all 24 declarations, then the source in
`more-etale.tex`: section-derived-lower-shriek-compactification (0F7H),
lemma-shriek-well-defined (0F7I), lemma-shriek-composition (0F7J),
lemma-pseudo-functor (0F7K), lemma-base-change-shriek (0F7L), and
lemma-shriek-proper-and-open (0F7B), including its unbounded torsion-ring case (b).
The source's ambient quasi-compact and quasi-separated hypotheses follow from the node's
Noetherian hypothesis. Its finite-type/separated hypotheses and compactification data
are retained. The finite coefficient ring is a torsion ring, including the zero ring.
The node is unchanged and has no statement_change to audit.

My object/hypothesis/conclusion checklist follows. Declaration names in this table are
in `AlgebraicGeometry.Etale` unless explicitly qualified.

| Item of the node | Lean rendering and second-reader verdict |
| --- | --- |
| Finite commutative ring A | `A : Type (u + 1)`, `[CommRing A] [Finite A]` on all assertions that need finite coefficients. Exact transport helpers valid for all commutative rings add no restriction. PASS. |
| Small etale sites, constant-ring module sheaves | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`; opened `DerivedCategories` and upstream `Coefficients`, whose `DerivedCategoryModule` is exactly its ordinary unbounded derived category. PASS. |
| All schemes Noetherian, finite affine Noetherian covers | `[IsNoetherian X]`, etc.; opened Mathlib `Noetherian`, especially the class and `isNoetherian_iff_of_finite_affine_openCover`. The proper ambients inherit local Noetherianity and compactness; no ambient hypothesis is added. PASS. |
| Compact-support edges separated and finite type | `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`, similarly g and h. Opened their Mathlib classes. Pullback edges inherit these properties; the explicit quasi-compactness witnesses only expose consequences. No hypothesis on the base-change edges v or w. PASS. |
| Each needed compactification | `Compactification f` or `[HasCompactification f]`, also for composites. Opened upstream `Compactification.Defs`: an open immersion i, proper g, and `f = i ≫ g`, with no density requirement. Equal-morphism/identity instances merely let the same chosen-candidate API typecheck. PASS. |
| Candidate Rr* Dj! | Existing `rightDerivedLowerShriekOfCompactification (ModuleCat A) c`; opened its body in `LowerShriek`. It is degreewise exact open extension followed by total unbounded right derived direct image. PASS. |
| Canonical proper-refinement map, identity on X | `unboundedEtaleCompactSupport_refinement_normalization`, for every `r : c.Refinement d`, identifies the actual pairwise comparison with the graph-normalized open comparison followed by proper direct-image composition. Opened `EtaleCompactSupportNormalization`, including `sheaf_normalization`, `derived_normalization`, and `nonempty_etaleCompactSupportNormalization`. The universally quantified N is an existing normalized family, available for every finite A, not an arbitrary map or added geometric hypothesis. PASS. |
| Refinement identity/composition; common-refinement independence and cocycle | `unboundedEtaleCompactSupport_comparison_coherence`: pairwise reflexivity and transitivity, together with the preceding normalization for every refinement, give each of these laws. Opened `LowerShriekIndependenceUnbounded`: the pairwise maps really use `Compactification.inf` and its two comparisons. PASS. |
| Compactification-independent Rf! | Existing `rightDerivedLowerShriek` and `rightDerivedLowerShriekIso A c` from each candidate, with the asserted cocycle. This is selection of a model with specified comparisons, not a limit over a large category. PASS. |
| Canonical composition alpha | `unboundedEtaleLowerShriekCompIso` is an actual natural isomorphism. Its body is the same explicit `ofComp` tower as `nonempty_iso_rightDerivedLowerShriek_comp`, read in `LowerShriekComposition`; it never selects an unspecified isomorphism from Nonempty. PASS. |
| Independence of tower choices and compatibility with refinements | `unboundedEtaleLowerShriekCompIso_tower` computes alpha on every d and e, conjugated by all three existing pairwise comparisons. Together with their cocycle this gives independence and refinement compatibility. PASS. |
| Proper/open tower normalization | The same equation uses existing `rightDerivedLowerShriekOfCompactificationCompIso A d e`; opened its body: the proper/open interchange, proper direct-image composition, and derived open-extension composition, with the required directions. `e.restrict` supplies the actual fibre-product V, q and j. PASS. |
| Interchange adjunct inverse to proper open-restriction exchange | `unboundedEtaleCompactSupport_tower_adjunct` composes the open-adjunction transpose of that exact interchange with `unboundedEtaleProperOpenRestriction` to give identity. The latter is `exactDerivedBaseChangeMap` followed by Rq* of the inverse open unit. The existing interchange is invertible, and the open adjunction unit is invertible, so this specifies its inverse adjunct. PASS. |
| Composition identities and associativity | `unboundedEtaleLowerShriekCompIso_units` gives both units with the identity compactification; `_assoc` compares both triple composites with the functor associator and morphism-equality congruence included. PASS. |
| Cartesian square and arbitrary base change | `sq : IsPullback v' f' f v`, for general X', covers the canonical fibre product and every isomorphic cartesian square. Opened the compactification base-change source; `c.ofIsPullback sq` uses the specified square. PASS. |
| Exchange isomorphism on every unbounded K | `unboundedEtaleCompactSupport_baseChange` asserts `IsIso` of a natural transformation between the ordinary unbounded functors. No boundedness, constructibility, Tor-amplitude or dimension restriction. PASS. |
| Canonical proper exchange and inverse degreewise open comparison | `unboundedEtaleCompactSupport_exchange_normalization` displays exactly these factors and their associators. Opened `ExactUnboundedExchange`: the proper factor is the canonical exact-derived adjunction mate. Opened upstream `LowerShriekBaseChange`: the transported exchange has the same two factors. PASS. |
| Named open beta and its orientation | `unboundedEtaleCompactSupport_open_beta` identifies the underived map with `etaleLowerShriekBaseChangeMap A v j`. Opened that definition and the open-exchange definitions: both use the inverse conjugate of the underived exchange of the same square. Its inverse is the factor in C. PASS. |
| Exchange independent of compactification/refinement | The second conjunct of `_baseChange` quantifies over every c and conjugates the c-relative exchange by the source and base-changed target comparisons. Combined with refinement normalization and cocycle, this covers every common refinement. PASS. |
| Identity and composite changes of base | `_baseChange_id` supplies the identity equation; `_baseChange_comp` supplies the explicit pasted equation, with termwise inverse-image composition isomorphisms at both ends. The separately supplied outer cartesian witness follows from the two inner squares, so excludes no case. PASS. |
| Compatibility of C with alpha | `_baseChange_composition` compares alpha then C with the two C maps then base-changed alpha. Whiskerings, associators, orientations and the outer pasted square agree with the node. PASS. |
| Restriction of comparisons to D+ | `_comparison_plus` is equality of the actual named bounded-below and unbounded components after `rightDerivedLowerShriekOfCompactificationPlusCompatibility`. PASS. |
| Restriction of composition to D+ | `_composition_plus` compares actual `rightDerivedLowerShriekPlusCompIso` components with alpha after the two canonical inclusion compatibilities. PASS. |
| Restriction of exchange to D+ | `_exchange_plus` compares the actual compactification-relative `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap` with C after the inverse-image and shriek inclusion compatibilities. Opened its current published definition using `scompile.py --source`; it is the exchange named by thm-cbc-finite-torsion. Independence supplies the independent version as well. PASS. |

Dependency review: I opened the recorded definition/statement modules, not just their names:
`DerivedCategories`, Mathlib scheme/Noetherian/proper/finite-type/pullback definitions,
`CompactifiableOverField`, upstream `LowerShriek`, `RingedToposDerivedPushforwardComposition`,
`Etale.OpenImmersionLowerShriekCoherence`, `EtaleAmbientAdjointLocality`,
`ExactUnboundedExchange`, `EtaleLowerShriekBaseChangeMap`,
`EtaleCompactSupportComparisons`, and `CompactSupportFiniteTorsion`.
The compactifiability dependency records an additional existence theorem over fields, but its
module imports the general upstream Compactification/HasCompactification used here; no field
assumption is imported into this statement. The ringed-topos comparison is a proof ingredient;
the canonical constant-coefficient implementation is the existing `rightDerivedLowerStarComp`.
I also read the upstream unbounded independence, composition, open/proper interchange, and
compactification-relative exchange bodies. Current published `LowerShriekPlusBaseChange` and
`EtaleCompactSupportComparisons` were read through `scompile.py --source`, so the missing local
copy of the first module did not prompt a duplicate. Every recorded proof-dependency module is
imported. The unstated general noncartesian interchange node remains a proof dependency;
this statement uses existing canonical tower data and graph normalization, so no object needed
for typing awaits that node. No new definition node or dependency module is needed.

Edge cases: empty schemes/opens/fibres and zero complexes are included; there is no Nonempty,
density, surjectivity, Nontrivial or invertible-characteristic hypothesis. The zero finite ring
is allowed (positive annihilator 1). The unbounded assertions impose no lower or upper bound;
the final three assertions quantify over every D+ object. There is no degree n parameter or
index-set parameter whose zero/empty case could be omitted. Identity refinements and both
composition units are included. Successive arbitrary base changes are included without a
morphism-property hypothesis on either base-change map. `universe u` and every object/morphism
binder are explicit with autoImplicit false; schemes in Scheme.{u} and coefficients/module
objects in the established u+1 encoding introduce no extra site-universe equality.

Independent H4 searches used different queries from the first worker:

- LeanFinder: `unbounded derived etale compactification independence natural isomorphism coherence`:
  eight hits (local cohomology functor composition, standard etale algebra equivalences, Dold-Kan,
  and complex embeddings), none the required etale shriek statement.
- Loogle: `"rightDerivedLowerShriek"`: zero hits.
- LeanSearch: `Canonical unbounded compactly supported pushforward composition and base change
  coherence on etale sheaves`: service returned Internal Server Error, recorded as unavailable;
  LeanFinder, Loogle and grep supplied the independent working searches.
- Mathlib grep: `lowerShriek|compactSupport` in AlgebraicGeometry: zero hits. Broader
  `compactification|LowerShriek|proper.*open` finds unrelated topological compactifications.
- Independent rg over upstream WeilConjectures and project lean/Sheaf for
  `compact.*[Cc]omparison|[Uu]nbounded.*[Ss]hriek|[Ss]hriek.*[Uu]nbounded`,
  `exactCompactSupportExchange`, `unboundedFormalism`, `derivedFormalism`, and the new
  `unboundedEtale` names: found the reused candidate/pairwise/tower/exchange implementations
  and the existing bounded-below formalism, but no existing complete unbounded coherence
  package or collision. The exactCompactSupportExchange helper is only for the canonical
  fibre product; the delivery's square-parametrized helper genuinely generalizes that interface.

Mismatches and repairs: no mathematical, hypothesis, object, quantifier, or conclusion mismatch
was found. I repaired three broken TeX commands in the full proof docstring (steps 1, 3 and 5):
line wrapping had split `\\xrightarrow` and `\\sim` inside their command names. The line breaks
now occur between complete commands, preserving all twelve proof steps and the 100-character
limit. Every theorem still has exactly a sorry proof. All nine definitions have real data;
the congruence definition's equality elimination is construction data, not a proved theorem.
No local notation/instance or private notion occurs. Every declaration has a source/blueprint
docstring. The node's lean.statement is verbatim the principal theorem signature; all 24
listed declarations occur in the file, and the fifteen postponed theorems render clauses of
this same node.

Validation: the authorized single-file scompile wrapper compiled both its sandbox and
library-shaped forms cleanly (30.3 s and 31.3 s), without additional warnings. Final delivery
preflight recompiles the edited docstrings; the required dry run must print OK before push.

Final dry run: `deliver2.py Q28 lem-amb-unbounded-compact-support-comparisons --no-push`
printed `OK (dry run): commit 95a374310e passes the preflight and compiles; nothing pushed`.
The edited file therefore also passed compilation and server preflight before delivery.
