## Worker report

The module `Sheaf.AlgebraicGeometry.ProperOpenSiteTransport` states
`AlgebraicGeometry.ProEtale.properOpen_site_transport`, with exactly the site's
finite proper/open transport equality and invertibility on bounded-below etale
origins. The node changes only in `lean`. No statement correction or dependency
repair is needed, and no new DAG node is added.

Hypothesis and clause correspondence:

- A finite commutative ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  No nonzero, characteristic, or invertibility condition is imposed.
- All four schemes are explicit `Scheme.{u}` parameters `U' Z' U Z`.
  Their four `IsNoetherian` instances mean exactly finite affine covers by
  spectra of Noetherian rings: Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` records that equivalence.
- The four arrows are `j' : U' ⟶ Z'`, `j : U ⟶ Z`, `r : U' ⟶ U`,
  and `q : Z' ⟶ Z`. The two open-immersion instances and two `IsFinite`
  instances are exactly the geometric hypotheses. `QuasiCompact` and
  `QuasiSeparated` are explicitly bound for each of the four arrows.
- `sq : OpenImmersionSquare r j' j q` is the recorded chosen Cartesian
  square, including its specified pullback identification and both projection
  equations. Its inherited equation is `r ≫ j = j' ≫ q`; `sq.w.symm`
  supplies the opposite orientation required by the comparison formulas.
- Ordinary bounded-below constant-coefficient categories are represented by
  `DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`
  and its pro-etale counterpart with `Scheme.ProEt.topology T`. These are
  the existing fixed-coefficient presentations, not completed categories.
  The recorded `finiteCoefficientRealization` and
  `finiteCoefficientRealization_isEquivalence_ring` identify the latter
  with modules over the continuous-function coefficient ring sheaf. No
  coefficient identification is chosen independently of constant sections.
- `N` ranges over all objects of the displayed etale `DerivedCategory.Plus`.
  There is no constructibility, bounded-above, or termwise lower-bound binder.
- `C_T` is `(comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus`.
  Its sheaf functor is the module inverse image in the recorded
  `Scheme.proEtaleSiteComparisonModules` adjunction.
- `b_u` is exactly the component of `fixedComparisonDirectImageMatePlus Λ u`.
  That declaration is the right-derived base-change of the actual counit
  mate, with the recorded counit equation. It is not a chosen endpoint iso.
  The corresponding pullback comparison is the recorded
  `fixedComparisonPullbackPlus`, the termwise version of the canonical
  comparison in `SupportComparisonPullbackCoherence`.
- `e_j` is `properOpenSiteExtensionIso Λ j` (reused by the maintainer fix): apply
  `mapDerivedCategoryPlusNatIso` to the recorded
  `openImmersionLowerShriekComparisonUpperStarIso` and insert the two
  canonical termwise-composition comparisons. Thus its direction is
  `C_Z j_e! ⟶ j_p! C_U`, as required. This is the fixed-scalar part of the
  transport in `FiniteConstantCoefficientTransport`, with no scalar change.
- `γ^e` is `properOpenTransportEtale Λ j' j r q sq.w.symm`.
  Its sheaf map is the first, support-normalized witness in the recorded
  `Etale.properOpenInterchangeCoherence`. That witness is uniquely determined:
  its composite with the canonical inclusion into the common ordinary direct
  image is specified, and that inclusion is monic. Descend it termwise and
  conjugate by `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` for the
  finite maps r and q. These isos are fixed by the universal derived unit.
  On an injective representative J this gives exactly the proper-support
  identification followed by `q_*` of the resolution `j'_!J ⟶ I` in 0F7B.
  Thus this construction retains the dependency's resolution normalization.
  It avoids extracting the second witness through the dependency's very
  large existential predicate, which caused kernel timeouts in scratch.
- `properOpenTransportPullSquare` is the square pullback comparison assembled
  from `upperStarComp`, the commutativity equation, and termwise localization.
  `properOpenTransportExchange` is explicitly the r-adjunction unit followed
  by this comparison and the q-adjunction counit. It is the ordinary ambient
  exchange of the node in the fixed-coefficient presentation.
- `properOpenTransportOpenUnit` is the actual open-extension sheaf unit iso
  descended termwise; it is distinct from the pullback/direct-image unit.
  `properOpenTransportDelta` is exchange on `j'_!K` followed by `Rr_*` of the
  inverse open unit. The auxiliary theorem `isIso_properOpenTransportDelta`
  states the open base-change isomorphism expressly used in the node's
  defining transpose, for the node's square and coefficients and every
  pro-etale bounded-below K. Its docstring gives the injective-restriction
  and identity-on-sections proof. This exposes the prerequisite already
  included in the node's definition, rather than adding an arbitrary map.
- `γ^p_K` is `properOpenTransportProEtale ... K`: the inverse delta is sent
  through the inverse Hom bijection of the recorded derived open adjunction.
  Thus its open transpose is definitionally the specified inverse, and it
  is constructed before the site-transport equality is asserted.
- The first parenthesized composite in the theorem is exactly `S_N`:
  `e_j` at `Rr_e,*N`, then `j_p!` applied to `b_r,N`. The second
  parenthesized composite on the right is exactly `T_N`: `b_q` at
  `j'_e!N`, then `Rq_p,*` applied to `e_j',N`.
- Lean composition runs left to right: the first conjunct is
  `S_N ≫ γ^p_(C N) = C_Z.map γ^e_N ≫ T_N`, exactly the node's displayed
  equation. The second conjunct is `IsIso (γ^p_(C N))` for the same named
  pro-etale morphism, not existence of an unrelated isomorphism.

Dependency declarations read and used (their recorded modules are imported):

| Dependency | Module and declaration/interface |
| --- | --- |
| def-weil-pbc-derived-categories | `WeilConjectures.AlgebraicGeometry.DerivedCategories`; `Etale.DerivedCategoryModule`, `DerivedCategory.Plus` |
| def-weil-pbc-proetale-modules | `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`; `FiniteCoefficientModules`, `finiteCoefficientRealization`, its ring equivalence |
| def-weil-pbc-site-comparison-morphism | `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`; `Scheme.proEtaleSiteComparisonModules` |
| lem-weil-pbc-comparison-pullback | `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`; `supportSiteComparisonCoefficientPullbackIso`, `supportSiteComparison_pullback_coherent` |
| lem-weil-pbc-comparison-direct-image-canonical-mate | `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`; `fixedComparisonDirectImageMatePlus`, `fixedComparisonPullbackPlus` |
| lem-cbc-proetale-extension-zero-comparison | `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`; `openImmersionLowerShriekComparisonUpperStarIso`, `openImmersionLowerShriekComparison_coherence` |
| def-cbc-finite-constant-coefficient-transport | `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`; `StrictTower.H`, `hR`, `hJ` retain the same constant-section normalization when changing scalars |
| def-cbc-open-immersion-square | `Sheaf.AlgebraicGeometry.OpenImmersionSquare`; `AlgebraicGeometry.OpenImmersionSquare` |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Scheme` |
| def-weil-pbc-noetherian-ring | `Mathlib.RingTheory.Noetherian.Defs`; `IsNoetherianRing`; scheme condition through `Mathlib.AlgebraicGeometry.Noetherian` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite`; `AlgebraicGeometry.IsFinite` |
| lem-cbc-proper-open-interchange-coherence | `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`; `Etale.properOpenInterchangeCoherence` with its support and derived-unit normalizations |
| def-weil-pbc-proetale-operations | `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`; constant-section coefficient identification and ordinary operations; their fixed-ring forms are `ProEtale.upperStar`, `lowerStar` and `derivedUpperStarLowerStarAdjunctionPlus` |
| def-weil-pbc-ambient-ringed-exchange | `Sheaf.Paper.PbcActualRingedExchange` reexports `Scheme.proEtaleAmbientRingedExchange`; its ordinary unit/square/counit formula is specialized here to the fixed-ring presentation |
| lem-cbc-proetale-extension-zero | `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`; `proEtale_extension_by_zero`, existing exact `openImmersionLowerShriek` and its derived open adjunction |

All stated proof-dependency modules are imported, using non-public imports for
proof-only interfaces. The module also imports finite-direct-image exactness,
`RightDerivedFunctor.PlusExact`, open-extension full faithfulness, and the
existing derived open adjunction for its constructions. The current server
source of the missing local `WeilConjectures.AlgebraicGeometry.DerivedCategories`
was read through `scompile.py --source`, as were the live open-adjunction and
full-faithfulness modules. No local-checkout absence was treated as a blocker.

Edge cases checked before and during writing: empty open subschemes and empty
schemes (empty open-subsite restriction and zero extensions), identity opens
and identity finite maps (canonical identity and composition comparisons),
the zero ring and zero complex (all functors and units still exist), arbitrary
cohomological shifts of bounded-below objects (no fixed bound appears), and
finite coefficient rings in arbitrary characteristic (no residue-characteristic
restriction). No nonempty-scheme or nonzero-ring assumption is present. The
chosen Cartesian identification is retained, rather than replaced by an
arbitrary isomorphism of the two endpoints. No statement fault or
`STATEMENT-DISPUTED` flag was found.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “The canonical proper open interchange j shriek
  R r star to R q star j prime shriek commutes with comparison from the etale
  site to the proetale site”. Eight results, including generic site-functor
  comparison and scheme restriction lemmas; none states this compatibility.
- `msearch.py ... loogle`: `SheafOfModules.pushforward, CategoryTheory.mateEquiv`.
  Zero results.
- `msearch.py ... grep`: `properOpen|shriek|[Pp]ro[Ee]tale` in Mathlib
  `CategoryTheory`. Zero results.
- `msearch.py ... leansearch`: “etale proetale comparison respects canonical
  derived proper open interchange”. Eight results about proper restriction,
  etale rings and etale loci; none states the transport equation.
- `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `properOpen`, proper/open and site transport names; and the prescribed
  `grep -rn` of the item id in upstream. No exact statement or name collision.
  `ProEtaleProperOpenComparison` handles the refinement square with identity
  left proper map and defines its arrow by transport; it does not give this
  arbitrary finite Cartesian square or identify the independently specified
  open-transpose pro-etale map. It was therefore not rebound as an exact match.

Validation: the complete module compiled through `scompile.py` in both sandbox
and library layouts (20.1 s and 22.1 s). There were no errors or unexpected
warnings. All universes and variables are explicitly bound (`autoImplicit false`).
The two postponed proofs are `isIso_properOpenTransportDelta` and
`properOpen_site_transport`, both with the node reference and complete proof
plans. All definitions have actual data. Scratch probes are removed before
delivery. The prescribed delivery dry run and final push follow this report.

## Second reading by Q141

Independent maintainer second reading, 2026-10-17, of immutable delivery
368b7043b2d4f7b25919f509ef102e3f64e495e7. This section replaces the
worker placeholder; the reviewer did not write the original delivery.

I read packet.md, check-brief2.md, the snapshot item and all fifteen statement
dependencies, the delivered module and its docstrings, and the recorded declaration
interfaces in the read-only Q141 clone. Missing current sources were obtained with
scompile.py --source. I read Stacks more-etale.tex, lemma-shriek-proper-and-open
(Tag 0F7B), including its resolution-map construction; proetale.tex,
section-comparison (099R), lemma-jshriek-comparison (09AF), and
lemma-open-immersion; and sites-cohomology.tex,
lemma-restrict-direct-image-open (0D6G).

Hypothesis and conclusion audit:

- The finite commutative coefficient ring is exactly Λ : Type (u + 1), CommRing Λ,
  Finite Λ. There is no nonzero, field, characteristic or invertibility assumption.
- The four Scheme.{u} parameters and four IsNoetherian instances represent the
  stated schemes and finite Noetherian affine-cover condition. Mathlib
  isNoetherian_iff_of_finite_affine_openCover verifies that identification.
- The directions of j', j, r and q agree with the node; the first two have
  IsOpenImmersion, the latter two IsFinite, and all four have explicit qcqs
  hypotheses. Finite maps supply properness for the etale interchange.
- OpenImmersionSquare r j' j q contains the chosen pullback isomorphism and its
  two projection equations through ChosenCartesianSquare. The use of sq.w.symm
  has the required orientation. No merely commutative square replaces it.
- N ranges over every bounded-below etale derived module object. The fixed-ring
  sheaf presentation uses the actual small etale and weakly etale/pro-etale
  sites. finiteCoefficientEtaleRealization and finiteCoefficientRealization,
  with their recorded equivalence statements, identify these with the node's
  ringed-module categories by constant scalar sections. There is no completion,
  constructibility restriction, fixed lower bound, or replacement site.
- C is the recorded comparison inverse image descended termwise. b is
  fixedComparisonDirectImageMatePlus, whose counit equation specifies the mate.
  e is now the existing properOpenSiteExtensionIso, the termwise descent of
  openImmersionLowerShriekComparisonUpperStarIso. The directions agree with
  the two displayed comparison composites S and T.
- The etale gamma uses the support-normalized sheaf witness of
  properOpenInterchangeCoherence. Its equality inside the common ordinary
  direct image determines that witness uniquely, since the extension inclusion
  is monic and direct image preserves monomorphisms. Finite exact direct image
  and the universal derived-unit comparisons identify its termwise descent
  with the specified K-injective-resolution normalization of 0F7B.
- The pro-etale gamma is constructed before the transport assertion. Its delta
  is ordinary unit/square/counit exchange followed by direct image of inverse
  open-extension unit. Its inverse is transposed using the actual derived
  open adjunction. The named invertibility theorem is the open-base-change
  prerequisite already stated in the node's definition; it is not an arbitrary
  morphism or an existence-only choice. Restriction preserves injectives
  because exact open extension is its left adjoint, so the identity on sections
  proves the prerequisite on bounded-below complexes.
- The first conjunct is exactly S_N followed by gamma_p equals C(gamma_e)
  followed by T_N, using Lean's left-to-right composition. The second conjunct
  is IsIso of this same gamma_p at C(N). Neither conclusion is missing.

The eight proof-docstring steps match the node: open-unit normalization;
etale delta; proper-support normalization; exchange transport; naturality
calculation for T; transpose of the conjugated etale map; adjunction injectivity;
and cancellation to obtain invertibility. The auxiliary theorem also has its
source, blueprint reference and an injective-restriction proof plan. It is a
same-notion construction prerequisite, permitted by the missing-helper rule.
All definitions have actual data. The choice of the normalized etale witness
is determined by its stated monic normalization; it is not a hollow choice.
Exactly two theorem proofs remain sorry, with no local proof added.

Independent duplicate searches used rg for properOpen, proper/open, shriek
comparison, transport/interchange, and all new declaration names in Mathlib,
upstream WeilConjectures and Q141 lean/Sheaf. The general transport theorem was
not already present. However, the delivered properOpenTransportExtension was
an exact duplicate of properOpenSiteExtensionIso in
Sheaf.Paper.ProEtaleProperOpenComparison (lines 36–46). H4 is repaired by
importing that module, deleting the duplicate, and using the existing helper
at every occurrence. The older module's main theorem concerns the identity-left
refinement case and does not replace this item. No dependency statement repair
or source-based statement correction was needed. The item JSON changes only
lean: its declaration inventory, verbatim signature and explanatory note.

Edge cases: empty schemes and empty opens, identity opens and finite maps,
zero ring, zero complex, all characteristics, and arbitrary shifts with some
lower cohomological bound remain included. All variables are bound with
autoImplicit false. Scheme universe u and coefficient/module universe u+1
follow the recorded small-site convention without identifying site object and
morphism universes or introducing any test-object quantifier restriction.

Validation of the immutable module reproduced the recorded per-file scompile
success in sandbox and library layouts (19.3 s and 18.9 s). The installed
scompile.py now runs the overlay on the server, rather than locally; its output
confirmed success with no errors or unexpected warnings. The replacement
module also passed the same wrapper in both layouts (16.4 s and 19.0 s),
with exit 0 and no errors or unexpected warnings. No lake build, project-clone edit, Git mutation,
claim, delivery or live Lean write was performed by the reviewer.

Findings fixed: H4 duplicate helper and H11 placeholder second reading.
The complete replacement files under fixes/ retain the mathematical statement.
