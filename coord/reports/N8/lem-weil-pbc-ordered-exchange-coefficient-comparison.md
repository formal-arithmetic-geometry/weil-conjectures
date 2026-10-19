## Worker report

This delivery states the strict coefficient comparison for the raw ordered completed
exchange. The main module is `Sheaf.Paper.OrderedExchangeCoefficientComparison`;
its namespace is `AlgebraicGeometry.Scheme.OrderedExchange`. All postponed proofs
are named theorems with source references and natural-language proofs. The
constructions retain ordinary tensor formulas, universal derived comparison maps,
and completion units, rather than choosing unspecified comparison isomorphisms.

Hypotheses and objects:

- `universe t`, `{A : Type (t + 1)} [CommRing A]`, and
  `(d : AdicCoefficientDatum A)` retain the size convention and the commutative
  Noetherian adic datum. Its inherited `CompleteCoefficientDatum` fields contain
  finite generation of the ideal, additive torsion of the first quotient and
  perfectness of every positive quotient; `quotientFinite` gives finiteness.
- `{X' X Y' Y : Scheme.{t}}`, the four explicitly bound arrows, and
  `sq : ChosenCartesianSquare g' f' f g` give the specified cartesian square.
  No properness instance is present in the unconditional comparison.
- `K : d.derived X` and `hK : d.TowerComplete X K` mean arbitrary complete
  completed-coefficient input. No boundedness, constructibility, finite-origin
  or smoothness assumption is introduced. The final natural-transformation
  equality is on `AComplete d X`, the full subcategory with this predicate.
- The completed coefficient sheaf, finite sheaves and maps are the recorded
  `d.completedRing`, `d.finiteRing`, `d.projection`, and `exchangeScalar`.
  The constant coefficient category `D`, strict tower category `TD`, and
  scalar restriction `res` use the same existing sheaf and derived categories.
  Indices `n : ℕ` represent positive powers `I^(n+1)` throughout.

Clause-by-clause correspondence:

1. `chi` is the recorded ambient restriction/direct-image isomorphism
   `proEtaleRingRestrictionDerivedDirectImage`. `alpha` is the corresponding
   normalized ambient pullback comparison, not a replacement of the ambient
   coefficient category. `restriction_complete` asserts equivalence only on
   the full complete subcategories and identifies the actual restriction
   functor by a natural isomorphism after inclusion. `phi_existsUnique` and
   `phi` give the completed pullback comparison with its completion-unit
   equation. `completedHom_normalization` equates the induced completed Hom
   bijections, using ordinary adjunction transpose after the specified units.
   Equality of these bijections also identifies their units, counits and
   adjunction conjugates of the canonical direct-image identity and composition
   comparisons, as explained in that theorem's proof docstring.
2. `ordinaryRho_existsUnique` fixes the strict scalar balancing map on every
   sheafified pure tensor. `rho_existsUnique` fixes its derived extension by
   both universal reduction counits on flat-term K-flat representatives.
   Consequently `rho` compares actual derived strict diagrams, including all
   their transition maps. `rho_unit` asserts both the strict augmentation
   equation and the completion-unit equation after derived limit.
   `beta` and `delta` are precisely `exchangeCornerB` and `exchangeCornerD`
   followed by the images of this `rho`. `rhoM` is reduction at the ambient
   `M`, followed by `alpha_g` and pullback of `chi_f`; `rhoPull` uses the
   strict scalar/pullback comparison followed by the image of `rho`.
   The first three conjuncts of `coefficientComparison` assert the raw
   `v^a` formula, the specified `H^a/H^0` equation, and the strict-mate equation.
   `H` in the adapter is the counit-tensor projection map followed by the
   inverse reduction/pullback comparison. Its invertibility uses the existing
   perfect quotient hypothesis. The unconditional raw map is the existing
   `d.completedExchange`; it is not defined by witnesses. In the final
   quantified proper case the equation identifies it with
   `d.completedBaseChangeMap sq K hK W` for every witness family `W`.
   Existing `towerV'`, `exchangeRealizationH` and `exchangeRealizationHPrime`
   supply the same towers and morphism used by the normalization dependency.
3. `ordinaryLambda_existsUnique` fixes the ordinary limit/scalar comparison by
   all projections. `lambda_existsUnique` fixes its derived comparison by
   universal right-derived units, and quantifies over arbitrary complexes
   of completed-coefficient towers. `lambda` therefore has no finite-reduction
   hypothesis. Its proof uses K-injective strict towers and preservation of
   K-injectives by restriction, justified by flat scalar extension.
   `iotaS` is `phi_g` followed by completed pullback of `chi_f`, evaluated at
   the complete direct image; `iotaT` is `chi_f'` followed by direct image of
   `phi_g'`. `sourceReconstruction` is the recorded completed reduction/pullback
   reconstruction. The constant source reconstruction from
   `completion(pull(...))` to `rlim(reduction(pull(...)))` is definitionally
   the identity in the adapter; thus its prescribed normalization has RHS
   `iotaS.hom` directly. `reconstruction` gives the other constant reconstruction
   to `rlim(towerPull(reduction(...)))`. The next four conjuncts of the main
   theorem state both reconstruction equations, the source `s^a/s^0` equation,
   and the target `c^a/t^0` equation. The adapter's `S` is exactly limit of `H`
   after the identity source reconstruction; `T` is pushforward of pullback
   reconstruction followed by the adjunction-normalized direct-image/limit map.
   `rawNormalized` and `constantNormalized` are actual natural transformations
   on the full complete category, with the displayed routes as their components.
   Their equality in `coefficientComparison` is the final raw exchange equation.
   `normalized_naturality` explicitly quantifies over every morphism between
   complete inputs. No identity-square or pasting law for exchange is asserted.

Recorded dependency declarations used (and source signatures/docstrings read):

| Node | Module and declarations |
| --- | --- |
| def-pc-sheaf-restrict-scalars | Mathlib `Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars` |
| def-weil-pbc-adic-coefficient-datum | `Sheaf.Paper.AdicCoefficientDatum`, `AdicCoefficientDatum`, `completedReductionTower`, its universal counit and ordinary quotient construction |
| def-weil-pbc-adjunction-conjugate | Mathlib `CategoryTheory.Adjunction.Mates`, `conjugateEquiv`, `conjugateIsoEquiv` |
| def-weil-pbc-ambient-ringed-exchange | `Sheaf.Paper.PbcActualRingedExchange`, `pbcActualCompletedAmbientExchange`, underlying `integralExchange` |
| def-weil-pbc-cartesian-square | `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, `ChosenCartesianSquare` |
| def-weil-pbc-completed-base-change-map | `Sheaf.Paper.CompletedBaseChangeMap`, `completedExchange`, `completedBaseChangeMap`, `towerH`, `towerH'`, `towerV'` |
| def-weil-pbc-completed-pullback | `Sheaf.Paper.PbcActualStrictPullback`, `pbcActualStrictCompletedPull`, underlying `completedPull`, `ordinaryToCompleted` |
| def-weil-pbc-proetale-operations | `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, `proEtaleConstantRingDerivedPullback` and underlying canonical ringed derived adjunctions |
| def-weil-pbc-projection-formula-map | `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`, `proEtaleProjectionFormulaMate`; the existing strict realization is its counit-tensor form |
| def-weil-pbc-strict-tower-operations | `Sheaf.Paper.StrictTowerOperations`, `StrictTowerRingedSquare.exchangeTowerMate` |
| def-weil-size-convention | foundational universe convention; no Lean record |
| lem-sp-completed-pullback-adjunction | `Sheaf.Paper.CompletedPullbackAdjunction`, `ConstantCompletion.completedPullbackAdjunction` |
| lem-sp-completion-mate-comparison | `Sheaf.Paper.CompletionMateComparison`, `AdicSites.completionMateComparison`, `Site.reduction`, `projectionComparison`, `comparisonS`, `comparisonT`; original-site adapter supplied here |
| lem-weil-pbc-constant-completion-equivalence | `Sheaf.Paper.ConstantCompletionEquivalence`, `ConstantCompletion.equivalence`, flatness, completion and quotient comparisons |
| lem-weil-pbc-diagram-site-realization | `Sheaf.CategoryTheory.DiagramSiteRealization`, `exists_diagramSite_realization` |
| lem-weil-pbc-profinite-coefficient-inverse-image | `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`, `proEtale_profinite_coefficient_inverse_image` |
| lem-weil-pbc-ringed-topoi-derived-tensor-pullback | `Sheaf.Paper.PbcActualScalarPullback`, `pbcActualScalarDerivedPullIso_exists` and underlying normalized ordinary/derived scalar pullback comparisons |
| lem-weil-pbc-strict-tower-exchange-mate-normalization | `Sheaf.Paper.StrictTowerExchangeMateNormalization`, `strictTowerExchangeMateNormalization`, `exchangeScalar`, `exchangeCornerB`, `exchangeCornerD`, `exchangeConstantSquare`, `exchangeRealizationH`, `exchangeRealizationHPrime` |
| prop-weil-pbc-direct-image-limits | `Sheaf.Paper.CompletedDirectImageLimits`, `directImageRlimIso`, `reductionTowerPullbackIso`, `towerProjection` |
| prop-weil-pbc-koszul-reconstruction | `Sheaf.Paper.KoszulReconstruction`, `koszulReconstruction` |
| prop-weil-pbc-rlim-functoriality | `Sheaf.Paper.CompletedRlimFunctor`, `completedRlim_computation`, `completedRlim` |

All Scheme declarations in the table have namespace
`AlgebraicGeometry.Scheme` (including the `AdicCoefficientDatum` namespace where
appropriate); `AdicSites` and `ConstantCompletion` have namespace `CategoryTheory`.

Edge cases checked before and while writing: the zero object; the zero ring;
`I = ⊤` (all quotients zero and the complete category zero); `I = ⊥` when the
finite/torsion datum is satisfied; empty schemes; identity arrows; arbitrary
cartesian squares with nonproper `f`; and complete inputs produced by direct
image or completed pullback. No nonzero coefficient assumption is used.
Identity transitions of strict towers remain part of the actual diagram.
The only witness-dependent clause quantifies over every supplied witness family.

Searches for an existing statement:

- `msearch.py leanfinder`: "restriction of scalars identifies derived strict
  quotient towers and ordered completed exchange" returned ordinary algebraic
  scalar restriction and unrelated statements, no match.
- `msearch.py loogle`: "CategoryTheory.conjugateEquiv,
  CategoryTheory.Adjunction" returned the standard conjugate/mate API,
  including composition and identity lemmas, but no coefficient comparison.
- `msearch.py leansearch`: "canonical restriction of scalars comparison of
  strict derived reduction towers and completed exchange" returned ordinary
  restriction-of-scalars results, no combined strict derived statement.
- `msearch.py grep`: "ordered.*exchange|completed.*exchange" in Mathlib's
  `CategoryTheory` returned no match.
- `rg` on the upstream `WeilConjectures` sources for the item's id returned
  none; searches for ordered exchange and coefficient comparison returned
  unrelated declarations. `rg` on `lean/Sheaf` found the recorded completion,
  strict tower and normalization modules used above; none states this item.
- Read the current main-20261015 completed-exchange-coherence proof source,
  second paragraph, and the item's complete fourteen-step strict coefficient
  supplement. The main theorem docstring retains that proof outline in full.

A final full-name search for `OrderedExchange` and `OrderedExchangeInterface` in
Mathlib/upstream declaration records and both project source trees found no
conflicting declaration.

No statement correction and no disputed mathematical assertion is recorded.

## Dependency modules

`lem-sp-completion-mate-comparison`: its existing `AdicSites.Site` fixes
`objects : Type u` with `SmallCategory objects`; it cannot directly be instantiated
with the pro-etale site whose objects lie in `Type (t+1)` and morphisms in `Type t`.
The dependency module `Sheaf.Paper.ProEtaleConstantReductionTower` retains the
original generic full theorem through a direct abbreviation in
`CategoryTheory.AdicSites.OrderedExchangeInterface`, and publicly imports the old
module. It adds the same ordinary strict quotient diagram and its derived universal
counit directly on the original site, together with the completion unit,
ordinary tensor/pullback normalization, perfect projection, reconstruction and
specified `H`, `S`, `T` comparisons. Quotient transitions and their tensor formulas
are retained before localization. All chosen derived data are fixed by universal
properties, and all chosen ordinary comparison maps by uniqueness and explicit
section formulas. No arbitrary tower lift or equality of site universes is used.
Only this dependency's `lean` record changes.

## Second reading by N8

Independent maintainer second reading of immutable delivery
4494e804e677267e52506ab2a7c915dd1fe7bdda, performed on 2026-10-17. This section
records the external reader's actual audit; it does not attribute a review to
the original worker.

Read the item, all 21 statement dependencies, both delivered modules, their
docstrings, the recorded declarations and the source places. In particular read
the second paragraph of main-20261015 completed-exchange-coherence and Stacks
proetale.tex, lemma-naive-completion (099M) and
lemma-pushforward-Noetherian-case (099N), plus sites-cohomology.tex,
lemma-Rf-commutes-with-Rlim (0A07) and remark-compatible-with-diagram (0E48).
These are ingredients; none is incorrectly treated as stating the combined lemma.

Hypothesis and conclusion audit:

- `AdicCoefficientDatum A` supplies the commutative Noetherian ring, finitely
  generated ideal, additive torsion and finite perfect positive quotients.
  `ChosenCartesianSquare` retains the chosen fibre-product identification and
  both projection equations. `d.TowerComplete` uses the actual quotient unit.
  No properness, boundedness, constructibility or etale-origin assumption occurs
  in the unconditional clauses.
- Clause (1): `chi` and `alpha` reuse the normalized ambient scalar comparisons.
  `restriction_complete` is only an equivalence of complete subcategories.
  `phi_existsUnique` fixes the completion-unit equation and
  `completedHom_normalization` asserts compatibility of the induced Hom
  bijections. This determines the units, counits and their adjunction conjugates.
- Clause (2): `ordinaryRho` is fixed on sheafified pure tensors; `rho` is fixed
  on K-flat models with flat terms by the universal reduction counits.
  `rho_unit` includes strict augmentation and completion-unit compatibility.
  `beta`, `delta`, `rhoM` and `rhoPull` use the published strict scalar maps.
  The first three main conjuncts give the raw realization, the H equation and
  the strict mate equation, all in derived strict-tower categories.
  The final witnessed clause quantifies over every witness family and alone
  requires properness; its formula reuses `completedBaseChangeMap`.
- Clause (3): `lambda` quantifies over arbitrary tower complexes and is fixed by
  ordinary limit projections and universal derived units. The four remaining
  objectwise conjuncts give both reconstruction equations and both s/t
  equations. The target reconstruction on the completed side is definitionally
  identity; the source constant reconstruction is definitionally identity.
  `sourceA` is limit of `towerH`, already on the pulled reduction source;
  `exchangeRealizationH` includes the inverse pullback/reduction identification.
  These directions give exactly the written ordered composite.
  `rawNormalized = constantNormalized` is an equality of actual natural
  transformations on the full complete category; `normalized_naturality`
  allows every morphism. No identity-square or pasting theorem is asserted.

The dependency repair retains site objects in universe t+1 and morphisms in t.
It constructs one strict quotient diagram, its universal left derivation and
augmentation directly on that site. Tensor formulas determine the transitions;
`ReductionPullNormalized` determines the derived pullback comparison.
`projection` is the counit mate, `directLimitIso` the adjunction conjugate,
and `H`, `S`, `T` have the prescribed normalizations. Choices from uniqueness or
universal properties determine their data. No hollow or arbitrary map is used.
The original generic theorem remains available without a universe restriction.

Findings repaired by the maintainer: H1/H11, the original second-reading section
was a placeholder, now replaced by this actual reading; H4, the generic
`completionMateComparison` repeated the already available theorem with a fresh
sorry, now replaced by a direct abbreviation of that theorem. The original-site
constructions, all mathematical hypotheses and conclusions are unchanged.
The merge tool refits the dependency's primary signature from `theorem` to
`abbrev`; its full declaration name and declared type remain unchanged.

Edge cases checked: zero objects and coefficient ring, empty schemes, unit and
zero ideals when the datum holds, the empty generating list for the zero ideal,
positive quotient indexing n+1 at n=0, identity transitions and arrows,
nonproper squares, and complete inputs obtained by pushforward or completed
pullback. Explicit universe and variable binders retain the original pro-etale
site; the condensed module-object framework is not substituted for it.

Independent `rg` searches in Mathlib's category and module-sheaf directories,
both upstream WeilConjectures trees and the side Sheaf tree found the generic
mate theorem used by the fixed alias, but no existing combined ordered scalar
comparison. The worker's service-search results are recorded above.
Both original primary `lean.statement` fields are verbatim signatures, all lines
are at most 100 characters, and all newly stated theorem bodies are `sorry`.
Structural identity naturality fields in explicit functor/isomorphism
constructions are ordinary construction data, not proofs of the target theorem.
The helper choices are pinned by stated uniqueness or universal properties.
No source-based statement correction is made in this delivery. The inherited
Rlim correction resolves every cochain complex, as required by 079P; its uses
in completed pullback and completed base change retain precisely that functor.

Compiler evidence, independent maintainer reproduction:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py N8
lem-weil-pbc-ordered-exchange-coefficient-comparison` was run with both immutable
module paths in dependency order, and again with the fixed adapter plus the
immutable item. Both runs exited 0 without errors or warnings. In the original
run the adapter library check took 37.4 seconds and the item library check
51.6 seconds. In the fixed run they took 36.7 and 40.7 seconds respectively;
all preliminary, private-overlay and sandbox checks passed as well. Every Lean
invocation retained the 60-second limit. The installed wrapper currently uses
server private overlays and confirmation; no separate direct ssh was invoked.
This verifies elaboration of stage-2 statements, not their postponed proofs.
No global build, repository mutation, live Lean edit, claim or delivery was
performed.
