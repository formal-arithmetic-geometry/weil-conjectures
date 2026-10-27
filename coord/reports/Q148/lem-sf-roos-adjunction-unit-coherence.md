## Worker report

The module `Sheaf.SixFunctors.RoosAdjunctionUnitCoherence` states
`CategoryTheory.RoosAdjunctionUnit.roosAdjunctionUnitCoherence`, with its entire
proof postponed. `Coherence` bundles its output comparisons and all their
characterizing equations. It is a structure of conclusions, not an assumed
comparison package. The theorem has no hypothesis supplying its desired
coherence, a cone filler, an arbitrary map or an arbitrary isomorphism.

Hypotheses and objects, matched to the node:

- The two small ringed sites are `C`, `J`, `R` and `D`, `K`, `S`. The module
  categories are exactly the recorded `ringedSiteModules`, hence Mathlib's
  `SheafOfModules`, with coefficient universes `max uC vC r` and `max uD vD s`.
  `HasSheafify` and `WEqualsLocallyBijective` express the usual small-site
  sheafification infrastructure, as in both recorded comparison dependencies.
  `_hR` and `_hS` state sectionwise commutativity of the ring sheaves, whose
  recorded interface uses `RingCat`.
- Exact countable products are the two `HasExactLimitsOfShape (Discrete ℕ)`
  instances. Both functors have `Additive`, `PreservesFiniteLimits` and
  `PreservesFiniteColimits`, expressing additive exactness.
- `a : F ⊣ G` is the specified adjunction; `[IsIso a.unit]` is precisely the
  invertible unit. `_hphiF` and `_hphiG` require invertibility of the canonical
  `piComparison`, whose projections are `F.map (Pi.π ...)` and `G.map ...`.
- Towers use the existing functor categories `ℕᵒᵖ ⥤ A`. Level `n : ℕ`
  represents the node's positive level `n+1`, including its first level.
  `towerComplex`, `towerDerived` and `towerFactors` are transparent expressions
  for Mathlib postcomposition, its standard exact localization, and its standard
  factorization. They construct no second tower category or derived category.
- `HasDerivedCategory` chooses the ordinary unbounded localizations in the
  stated morphism universes. `LA`, `LB`, `etaA`, `etaB`, `_hLA`, `_hLB`
  specify total right derived inverse limit with its universal units, exactly
  as in `exactProductFunctorStrictLimit`. The two localization universes are
  independent. The ordinary and tower derived adjunctions are the specified
  localization of the given adjunction, never an arbitrary adjunction.

Conclusions, clause by clause:

- `Coherence.product_unit` is the node's first displayed equality in Lean's
  left-to-right composition convention: `u_product ≫ G(phiF) ≫ phiG = Pi.map u`.
- The Roos complex is the recorded `roosF`, whose actual objects are
  `Cone(1-s)[-1]` and whose actual maps come from strict squares.
  `coordinates` is `roosχ`, followed by swapping the two factors and negating
  the second. Thus its factors in degree `p+1` are `P^(p+1)` and `P^p`, and
  the differential is exactly `(dx,(1-s)x-dy)`. No alternative cone is defined.
- `kappaF_coordinates` and `kappaG_coordinates` pin the maps to the positive
  canonical product comparison on both of these signed factors. The binary
  product comparison is Mathlib's `Functor.biprodComparison`. Both kappas are
  natural isomorphisms on strict tower complexes.
- `thetaA` and `thetaB` are natural isomorphisms from the derived limit of a
  representative to its actual Roos model. `normalizationA` and
  `normalizationB` pin their K-injective normalization to `Q.map (roosι I)`
  for every K-injective tower with injective terms. In these signed coordinates
  `roosι` is `(iota,0)`, as required by the recorded normalized comparisons.
- `lambdaF_normalization` and `lambdaG_normalization` are exactly
  `lambda = theta_target inverse * kappa * F(theta_source)`, with Mathlib's
  actual localization factorization isomorphisms inserted. Consequently the
  lambdas are precisely the comparisons of
  `lem-cbc-exact-product-functor-strict-limit`. The same theta for each category
  is shared by both lambdas. No independent normalization or cone filler enters.
- `chain_unit` is the second displayed equality as an equality of actual chain
  maps. The right side is `roosF.map` of the degreewise tower adjunction unit.
- `towerUnit_hom` pins the invertible tower unit to the localized specified
  adjunction. `derived_unit` is the third displayed equality for every object
  of `D(Tow(A))`, using `LA.map (towerUnit.inv.app M)`. Since all its factors
  are natural, this objectwise assertion is the stated natural equality.
- `augmentation` quantifies over every complex `P`, every compatible family
  `gamma`, and every strict tower complex `X`. It supplies actual maps `b`
  and `bGF`. Their two coordinate equations say exactly `(gamma,0)` and
  `(GF(gamma),0)`. The next equality compares the chain composite with
  `u_P ≫ bGF`. The following coordinate equation writes that composite as
  `(gamma_n ≫ u_(X_n),0)`, so it includes the requested source unit and the
  zero second coordinate explicitly. Its final equality applies the same
  normalized lambdas to the actual map `Q(b) ≫ thetaA.inv`, giving the
  augmented derived equality. These are the actual augmented maps identified
  by the recorded Roos theorem, not merely maps to an abstract limit object.
- The node's final identity-in-unit-coordinates observation is rendered by the
  product and chain equalities: composing each target projection with the
  corresponding inverse unit cancels its unit; both signed summands and the
  displayed augmented coordinates satisfy the same cancellation. This is a
  consequence of the stated equalities and the assumed invertibility, with no
  additional assertion or convention omitted.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the transparent Mathlib module-sheaf category, including its full docstring.
- `Mathlib.CategoryTheory.Functor.OfSequence`, `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`: natural-number opposite towers, read with their
  transition and naturality signatures; no alternative tower representation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory` and `DerivedCategory.Q`: ordinary unbounded localization.
- `Sheaf.SixFunctors.OpenTensorNormalizationData`,
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`: the landed
  dependency is imported and retained. The item-local universe-general helper
  has the same localization body, with the explicit `rfl` identification
  `exactDerivedAdjunctionUniverses_commonUniverses` at common universes.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`,
  `CategoryTheory.exactProductFunctorStrictLimit`: full existential signature,
  both signed-coordinate comparison clauses, its K-injective normalization,
  both lambda squares and its actual augmentation clause read. It is imported
  as a proof dependency; the conclusion records the same specified comparison.
- `Sheaf.CategoryTheory.StrictRoosComparison`,
  `CategoryTheory.strictRoosComparison`: full signature and proof docstring,
  including every-resolution normalization and actual augmentation read.
- `Sheaf.CategoryTheory.StrictRoosModel`, `roosF`, `roosP`, `roosχ`,
  `roosι` and their coordinate/map formulas: the existing cone, not a private
  copy. Its already-landed owning node `def-weil-strict-roos-model` is added
  to `stmt_deps` because the Lean directly names this existing model.

Edge cases checked: the first positive tower level is retained by reindexing;
all integer cochain degrees occur, including zero and negative degrees (every
integer is `p+1`); zero objects, zero augmentations, nonzero augmentations,
constant towers and identity adjunctions are included. The countable family is
always indexed by ℕ as in the node, so no nonemptiness assumption was introduced.
No boundedness, chosen resolution, extra commutation hypothesis, equality of the
site universes, or equality of the coefficient universes is imposed. In the
identity adjunction case all canonical comparisons and their unit coordinates
are identities, and the augmentation equations retain their zero coordinate.

Searches for existing statements:

- `msearch.py leanfinder`, query "Adjunction unit commutes with product comparison
  and signed Roos derived inverse limit comparison": eight hits, headed by
  `Adjunction.derived'_unit`, `Adjunction.derived_unit`, `derivedη_fac_app`
  and `derivedε_fac_app`. These normalize derived adjunctions but do not state
  the signed Roos, total-limit and augmentation assertions.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.unit,
  CategoryTheory.Limits.piComparison`: zero hits.
- `msearch.py grep`, query `Roos|derivedLimit.*unit|unit.*derivedLimit`,
  subdirectory `CategoryTheory`: zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for Roos/unit variants and the exact item id:
  related open-restriction and Koszul-unit modules, but no existing statement
  with these general exact-adjunction comparisons and all augmentations.
  Existing Roos model and comparison modules were read and reused.

The mathematical node statement is unchanged. There is no disputed statement,
new independent definition node, dependency-record change or postponed auxiliary
theorem. The only `sorry` is the entire main theorem proof. The common-universe
identification is an abbreviation for the actual reflexivity term requested by the
return, rather than a postponed mathematical lemma.

## Repair of return L (immutable head 2cceb9abd6bd)

H13/H4: removed the sandbox copy of
`dag/nodes/sec-six-functors/def-weil-exact-derived-adjunction.json` and removed
`Sheaf.CategoryTheory.ExactDerivedAdjunctionUniverses`. The live Q22 `lean`
record is therefore unchanged byte for byte, keeps `existing: true`, and still
names `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` in
`Sheaf.SixFunctors.OpenTensorNormalizationData`. That owning module is unchanged.
No existing user or citer loses its declaration or dependency binding.

The universe-general localization is now the listed helper
`CategoryTheory.RoosAdjunctionUnit.exactDerivedAdjunctionUniverses` in this
item's module, as the return explicitly permits. Its actual construction still
uses `Adjunction.mapHomologicalComplex`, followed by `Adjunction.localization`
with the standard `mapDerivedCategoryFactors` on each side. The separately listed
`exactDerivedAdjunctionUniverses_commonUniverses` is the `rfl` identification
with the landed construction when object, morphism and localization universes
coincide. This is a real reflexivity witness, with no `sorry`, extra assumption
or arbitrary choice. Both helpers carry this item's blueprint id. The theorem,
`Coherence` fields, independent universes and all previously accepted clauses
are preserved.

The initial saved-packet dry run passed (34ba761f491); the content repair above
is nevertheless necessary to satisfy the independent return. Validation of the
repaired packet is recorded below after the prescribed server compile and dry run.

## Self-check by Q148

Re-read the node and repaired file together after moving the helpers. The two
sites, commutative ring sheaves, exact countable products, additive exact F and G,
specified invertible-unit adjunction, and positive canonical product comparisons
still match their binders one for one. The unbounded derived-category and tower
universes remain independent. The theorem signature matches `lean.statement`
verbatim. Its only postponed proof is `roosAdjunctionUnitCoherence`.

The first product equality is `product_unit`; the second, of actual signed Roos
chain maps, is `chain_unit`; the localized cancellation equality is
`derived_unit`. `towerUnit_hom` still fixes the localized adjunction unit.
`kappaF_coordinates`, `kappaG_coordinates`, `normalizationA`, `normalizationB`,
and both `lambda*_normalization` fields retain their specified positive signed
comparisons and common K-injective normalization. `augmentation` retains both
actual chain maps, their zero second coordinates, the source unit, and the
normalized derived equality. No hypothesis or conclusion was changed by this
repair, including the identity adjunction and first positive tower level.

Checked the current base node against the sandbox: only the item's `lean` and
the already accepted additional `def-weil-strict-roos-model` statement dependency
differ. There is no dependency node file or separate generalized-adjunction
module in the packet. The two new item helpers are both in `lean.declarations`
and have source/blueprint docstrings. All variables/universes are explicitly
bound, all Lean lines have at most 100 characters, and there is exactly one
`sorry`. No second reader was started, as the dispatch explicitly forbids other
agents; the maintainer's independent reading remains the delivery review.

Validation: the repaired file passed `scompile.py` in both sandbox and library
module modes (36.5 s and 22.7 s), with no warnings or errors. The repaired packet
passed `deliver2.py --no-push`: `OK (dry run)`, commit `77fac7ce87f`; preflight
and per-file compilation passed. Its staged list contained exactly the item
node, item module and this report, with no dependency-record replacement.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
