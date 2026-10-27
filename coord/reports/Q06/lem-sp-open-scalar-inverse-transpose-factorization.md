## Worker report

The item module is `Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization`.
Its theorem is
`AlgebraicGeometry.ProEtale.OpenInverseTranspose.openScalarInverseTransposeFactorization`.
It states the three requested equations, including the composite-counit equation for
both coefficient rings and every target object. The node's statement and proof are
unchanged. One definition node supplies the missing intrinsic presentation of the
canonical refinement comparison. No exceptional scalar mate is assumed or used.
All theorem proofs in this delivery are `sorry`; definitions have explicit data.

Hypothesis-by-hypothesis correspondence:

* `ℓ p`, `Fact ℓ.Prime`, `k`, `Field k`, `CharP k p`, `_hp`, `_hℓ` give exactly the
  positive-characteristic field and distinct prime. `A B`, `CommRing`, `Finite`,
  `φ : A →+* B`, `n`, `_hN`, `_hA`, `_hB` give the unital finite ring map and common
  annihilating positive prime power. Neither coefficient ring is required nonzero.
* `U X Y : Scheme.{u}`, their `Over (Spec (.of k))`, structural `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` instances spell out separated finite type over k.
  The analogous instances for `c.Z` and `d.Z`, and the four `IsOver` instances on
  the compactification legs, retain the specified separated finite-type middle
  schemes and k-morphisms. The explicit instance binders are compatible with the
  recorded `compactificationOverField` setting.
* `f`, its `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and `j`,
  its `IsOpenImmersion`, `QuasiCompact`, `IsOver`, are exactly the stated maps.
  `j ≫ f` is g in Lean's order. `c : Compactification f` and
  `d : Compactification (j ≫ f)` are arbitrary, independently chosen compactifications.
* The category is the existing `spFiniteConstructibleTorCategory T R`, the full
  subcategory of `Scheme.proEtaleDerivedCategory T R` with bounded intrinsically
  constructible cohomology and `HasFiniteProEtaleTorAmplitude`. This is the intrinsic
  tensor-against-all-degree-zero-modules condition, not an etale-origin predicate
  substituted for finite Tor amplitude. No private constructibility or Tor notion
  is introduced. The fixed-module presentations use `ULift.{u+1,u} R` only through
  the already published realization equivalence; site universes stay u+1/u.
* `support R c hF` is the full-subcategory restriction of the actual
  `reductionCompactSupport R c.i c.g`. `hFA`, `hGA`, `hFB`, `hGB` expose the
  preservation witnesses necessary to restrict these stipulated functors. They do
  not replace support by arbitrary functors. `GA`, `GB` and `adjA`, `adjB` are
  the stipulated right adjoints on the finite-Tor categories; right adjoint
  uniqueness means this quantifies over presentations of the actual adjoints.
* `extension` and `restriction` restrict the already defined
  `sfIntrinsicDerivedOpen` and `sfIntrinsicDerivedPullback`. `hJA`, `hUA`, `hJB`,
  `hUB` are their restriction witnesses. `openAdjunction` uses
  `exceptionalOpenAdjunction` and Mathlib `restrictFullyFaithful`, preserving the
  actual localized open unit and counit. In particular v is not supplied as a map.
* `composition` first changes d to `c.precomp j` by the canonically normalized
  comparison, then uses the existing `sfIntrinsicDerivedOpenComp` and the functor
  associator. Full faithful cancellation along the target inclusion yields the
  restricted compositor. `compositeAdjunction` is `Adjunction.comp` transported by
  this compositor; hence G_g is U G_f with the adjunction-preserving identification
  required in the statement, not a second independent right adjoint.
* `scalarExtensionFunctor φ T` is the recorded ordinary derived extension of
  coefficients. `hSU` exposes preservation on U needed to apply the B compositor.
  `reductionDirectImageComparison φ c.i c.g` and its d version are precisely b_f
  and b_g; `reductionOpenScalarIso φ j` is the specified b_j, with the identity
  proper normalization supplied by the recorded reduction-comparison construction.
  `hbf`, `hbg` provide `IsIso` witnesses for these very maps, already stipulated
  invertible in the node. No arbitrary comparison or extra invertibility of an
  exceptional mate is assumed.
* `K : spFiniteConstructibleTorCategory Y A`, `GA.obj K` and
  `(restriction A j hUA).obj (GA.obj K)` are K, M and L. L is an arbitrary intrinsic
  finite-Tor object arising as the indicated restriction; the theorem never asks
  for an etale-origin witness for K, M or L.

Clause-by-clause correspondence (Lean `≫` is left-to-right composition):

1. The first and second conjuncts quantify over every H for A and B respectively.
   They equate the actual transported composite counit to the component of
   `composition`, followed by `support.map` of `openAdjunction.counit`, followed
   by `adjA.counit` or `adjB.counit`. Removing the explicit canonical change of
   coordinates yields exactly epsilon_g = epsilon_f after F_f(v).
2. The third conjunct is TY(composition_A) followed by b_f(J_A L) followed by
   F_f,B(b_j(L)), equal to b_g(L) followed by composition_B at TU L. This is
   exactly the coefficient-composition equation with both boundary identifications
   written explicitly. The open comparison is the actual fixed tensor comparison.
3. The final conjunct starts with the inverse of the actual b_g(L), then
   TY(epsilon_g). Its other side starts with the B compositor and then
   F_f,B(b_j(L) inverse), F_f,B(TX(v_M)), inverse b_f(M), TY(epsilon_f).
   Thus both sides have source F_g,B(TU L) and target TY K. Every ambient morphism
   obtained from a full-subcategory morphism is explicitly projected by `.hom`.
   This retains precisely the equation and orientation of the node.
4. Arbitrary c,d are quantified, and the change of compactification is uniquely
   normalized by the specified etale common-refinement comparison on every origin.
   Consequently these equations apply with the canonical comparison through any
   common refinement: common refinements do not provide an arbitrary extra map.
   The coefficient-compatibility theorem used in the proof already states its
   refinement and composition coherence. No smoothness or B/A flatness binder
   occurs in the statement.

Dependency declarations read and used:

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` (standing
  geometry); the actual theorem spells out its `Over` interfaces.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary derived categories.
* `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, and the intrinsic predicate
  `Scheme.IsConstructibleProEtaleModuleSheaf` used by the category.
* `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `HasFixedCoefficientProEtaleTorAmplitude` and the intrinsic
  `Scheme.HasFiniteProEtaleTorAmplitude` used by that category.
* `Sheaf.Paper.SmoothPurityNormalizedTowers`:
  `ProEtale.spFiniteConstructibleTor`, `spFiniteConstructibleTorCategory`.
* `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`: the recorded `AdjunctionTransfer`
  finite-Tor adjunction interface; the theorem works directly in intrinsic coordinates.
* `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `ProEtale.scalarExtensionFunctor`.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.OrdinaryDerivedChangeOfRings` (ordinary rather than completed scalar change).
* `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
* `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`,
  `Compactification.precomp` and the existing compactification objects.
* `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`:
  `CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible`.
* `Sheaf.Paper.MateOpenRestriction`: `CondensedRing.mateOpenImmersion`.
* `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `comp_counit_app`;
  `Mathlib.CategoryTheory.Adjunction.Restrict`: `restrictFullyFaithful`.
* `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`:
  `Scheme.exceptionalOpenAdjunction`; `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`:
  `sfIntrinsicDerivedOpen`, `sfIntrinsicDerivedPullback`, `sfIntrinsicDerivedOpenComp`.
* `Sheaf.SecSmoothPurity.ReductionDirectImageComparison`:
  `reductionCompactSupport`, `reductionDirectImageComparison`, `reductionOpenScalarIso`;
  `Sheaf.SecSmoothPurity.ReductionDirectImage`: `reductionDirectImage_isIso`.
* `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`:
  `CoefficientCompatibility.etaleCoefficientMap`, `proEtaleCoefficientMap`,
  `siteCompositor`, `siteRefinement`, composition/refinement equations. They use the
  normalized transported intrinsic map, not an unrelated comparison.
* `Sheaf.Paper.EtaleCtfChartDomain`: the proof's finite-Tor origin/domain theorem.
* New module imports `Sheaf.Paper.EtaleProEtaleCoefficientTransport`:
  `CoefficientCompatibility.supportPresentation`, and its imported
  `sfIntrinsicDerivedEquivalence`; `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`; `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`:
  `Etale.rightDerivedLowerShriekOfCompactificationIso` (existing common-refinement
  comparison); `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`:
  `Scheme.finiteRing_constructibleDerived_origin` (proof of the unique descent).

Edge cases checked before finalizing: j = identity gives the identity-normalized
open adjunction/compositor and ordinary inverse naturality. U empty and zero objects
cause no nonempty or nonzero premise. n = 0 forces the zero rings and is allowed;
there is no `Nontrivial` assumption. A=B and identity coefficient map retain the
normalizations. The nonflat map Z/ell^2 -> Z/ell is allowed: scalar extension is
derived and no flatness binder was added. Different compactifications and arbitrary
common refinements are included, not just the restricted compactification. Both
counits are at every H, rather than only the chosen K. The source is genuinely the
finite-Tor full category, rather than only objects presented by a selected antecedent.

Searches made: msearch LeanFinder for the inverse scalar comparison/composite counit
factorization returned ordinary scheme-open adjunction results, no exact declaration.
msearch Loogle `CategoryTheory.Adjunction.comp, CategoryTheory.NatTrans.naturality`
returned no hits; grep `comp_counit_app|inverseTranspose|inverse_transpose` in
CategoryTheory/Adjunction found the generic composite-counit and mates API. Source rg
for the item id and inverse-transpose/open composition in both WeilConjectures and
Sheaf found downstream OpenExceptionalScalarLocality and related expansion modules,
but no existing theorem of the requested statement. Those downstream modules are
not imported. The additional LeanSearch/LeanFinder/Mathlib grep queries and their
actual response records are in the new node. DAG/source searches found the fixed
etale-origin comparison, read below; `blueprint_refs.py search 'intrinsic refinement'`
returned no matches. No false or untypable item clause was found; no statement correction.

## New nodes

`def-sp-intrinsic-ctf-refinement-comparison` records the intrinsic finite-Tor
presentation of the canonical refinement comparison needed to form the compositor.
The source is the current blueprint Locality paragraph together with Stacks 0F7I,
0F7J and 099R. DAG grep and blueprint search, and rg in WeilConjectures and Sheaf,
found the existing `def-pur-origin-compactification-comparison`, whose declaration
`rightDerivedLowerShriekOfCompactificationEtaleOriginIso` acts on fixed-module
bounded-below etale-origin objects. That interface does not act on the intrinsic
Dctf category and uses its older fixed-presentation site comparison. We retain that
node as a dependency and do not redefine the fixed etale comparison. The new module
supplies the absent intrinsic presentation normalized by the specifically recorded
`supportPresentation` and proper-mate/open `compactSupportSiteComparison`.

`site` is the actual comparison followed by realization. `supportSite` composes the
recorded support presentation and canonical site comparison. `refinementModel`
conjugates the existing etale common-refinement comparison by these two prescribed
isomorphisms. `IsCanonicalRefinement` pins every component for every origin and every
identification with an intrinsic input. `canonicalRefinement_existsUnique` is a named
postponed theorem whose exact uniqueness assertion is included in this node's own
statement; its docstring contains the full descent/naturality/independence proof.
`refinement` takes data only from this equality-unique characterization. This is
not a choice of arbitrary isomorphism from a mere existence assertion. The earlier
fixed comparison is thus represented in the required coordinates with the specified
normalization, not replaced by a new abstract compact-support operation.

The msearch LeanSearch query for canonical intrinsic finite-Tor comparison returned
unrelated etale base-change and truncation results; LeanFinder returned standard
etale-presentation and approximation lemmas; grep
`canonicalRefinement|IsCanonicalRefinement|refinementModel` in Mathlib CategoryTheory
returned zero. Project rg found only the old fixed-origin construction and its users,
not an intrinsic normalized comparison interface. These real response records are
preserved in `mathlib_searches`; no search results were fabricated.

## Validation

Every delivered file is compiled separately, in dependency order, by scompile.py
against the live published build. Both modules compiled cleanly with the expected
sorry notices only before the final explicit return type/documentation adjustment.
The required dry run performs the final per-file compilation and maintainer preflight.

## Second reading by Q06

No second reading by a worker: the dispatcher starts a single worker and prohibits
sub-agents; the maintainer's independent delivery review is the independent reading.
