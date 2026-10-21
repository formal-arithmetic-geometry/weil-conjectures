## Worker report

The module `Sheaf.Paper.RegularQuotientCompletionUnit` states
`CategoryTheory.regularQuotientCompletionUnit_criterion`, with its proof postponed by
`sorry`. Three accompanying definitions construct the item's specified strict quotient
augmentation, shifted Roos cone, and zero-component unit. Their data contain no `sorry`.
The natural-language statement and proof are unchanged. The statement dependencies gain
three already landed definition nodes: `def-pur-principal-koszul-quotient-towers`,
`def-weil-strict-roos-model`, and
`def-weil-pbc-locally-derived-ringed-ideal-complete`.

Hypothesis and clause correspondence:

- The small site is `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`;
  its commutative ring sheaf is `R : Sheaf J CommRingCat.{u}`. There is no terminal
  object or enough-points hypothesis. Global sections are compatible families, not
  sections at an assumed terminal object.
- The module category is the recorded `ringedSiteModules` abbreviation for Mathlib's
  `SheafOfModules`, applied to the underlying ring sheaf of `R`.
- Exact countable products are
  `[HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules ...)]`. The small-site
  module category already has countable products; exactness is the substantive assumption.
- The global element `a` is a section of `SheafOfModules.unit` of that ring sheaf.
  `_ha : Mono (globalSectionMultiplication R a)` says multiplication is injective
  as a map of sheaves. It does not impose invertibility or any nonzero-ring assumption.
- `P` is an unbounded integer-indexed cochain complex of these module sheaves, and
  `_hP : CochainComplex.IsKFlatIndependentCoefficients P` is the recorded K-flat predicate.
  No termwise flatness or boundedness is assumed.
- `reductionTensorTower R P a` is the existing quotient tower with its quotient
  transitions. At index `n : ℕ` it is `(O/a^(n+1))[0] ⊗ P`, the symmetric model
  of the statement's `P ⊗ O/a^(n+1)`; tensor is the existing sheafified tensor.
  A degree-zero factor makes this the ordinary termwise tensor, with no extra terms.
- `regularQuotientAugmentation` is the composite `koszulStrictAugmentation ≫
  koszulTensorTowerComparison`. By the existing
  `koszulRepresentativeAugmentation_quotient` each component is precisely
  `koszulRepresentativeQuotient R P a n`, the prescribed quotient map.
- `regularQuotientCompletion` is `roosF.obj` on the degreewise-rearranged quotient tower.
  `roosF` is exactly `Cone(1-s)[-1]`, with products in complexes computed degreewise.
- `regularQuotientCompletionUnit` uses the existing `roosAugment` constructor on that
  strict augmentation. Its compatibility argument is the existing naturality equality,
  composed with `Category.id_comp`. The existing `roosAugment_χ` gives coordinates
  `(0, Pi.lift q)`, so the shifted-product component is exactly zero. There is no
  existential or arbitrary lift in this definition.
- Local derived `(a)`-completeness is rendered by the existing
  `IsLocallyDerivedRingedIdealComplete R (SheafOfModules.unit ...)`
  `(globalSectionMultiplication R a)`. The unit module maps monomorphically onto the
  principal ideal sheaf by `_ha`. Sectionwise its image consists exactly of `a*y`;
  regularity makes these preimages unique, so local preimages glue. The predicate
  quantifies over EVERY slice and EVERY section in that image, using the actual
  sheafified sectionwise localization, slice restriction, and derived internal Hom.
  Thus it does not test only the global generator.
- The first conjunct asserts this completeness for `Q.obj (regularQuotientCompletion ...)`.
- The second conjunct is completeness of `Q.obj P` iff invertibility of
  `Q.map (regularQuotientCompletionUnit ...)`, with this very chain map.
- The third conjunct equates invertibility of the same map with existence of the
  prescribed Roos triangle. Its existential `_hU : HasProduct ...` expresses existence
  of the derived product, rather than adding a product hypothesis to the theorem.
  The maps `p, δ` and `IsDerivedLimitTriangle` give the triangle with middle map `1-s`;
  `∀ n, p ≫ Pi.π _ n = Q.map (koszulRepresentativeQuotient ... n)` fixes every
  quotient component. The two iff clauses jointly give all three equivalences.
- The `HasDerivedCategory.{w}` binders on the site and all slices specify localization
  sizes required by the recorded definitions, with an arbitrary explicit universe `w`.
  No identification with the coefficient universe or bound on complex degrees is added.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the recorded generic Hom
  construction and its public upstream `derivedInternalHom`, used through the local
  completeness predicate at small-site universes. The slice predicate uses this
  existing upstream small-site presentation, rather than a second Hom construction.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the canonical
  sheafified tensor instances (in particular `SheafOfModules.cochainModulesMonoidal`).
- `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`: `reductionTensorTower`,
  `koszulTowerComplex`, `koszulStrictAugmentation`, `koszulTensorTowerComparison`,
  `globalSectionMultiplication`, `koszulRepresentativeQuotient`, and the existing
  augmentation-quotient equation.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosAugment`, `roosAugment_χ`.
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`:
  `IsLocallyDerivedRingedIdealComplete` with its actual slice/localization definitions.

The stated proof-dependency modules are imported privately, including the regular Koszul
reconstruction, normalized strict Roos comparison, ringed strict-tower homotopy-limit
interface, and the original general ringed-site reflector module. The reflector node's recorded
scheme-specialization module publicly imports that same generic theorem; the smaller
original module is sufficient here, since this item has no scheme or adic datum.
The triangulated-category structures are inherited from the recorded derived category.
The theorem's docstring follows all five DAG proof steps, including normalization of the
actual zero-component map and the separate converse from a prescribed Roos triangle.

Edge cases checked: if `a` is a unit, all positive quotients and the completion vanish;
local completeness then forces `P` to be zero, and the unit and triangle criteria agree.
For `P=0` all three conditions hold. The zero ring is allowed, including `a=0` there;
`a=0` in a nonzero ring fails precisely the injectivity hypothesis. An empty site is
allowed and its module category is trivial. The tower starts at exponent one, so no
unintended `O/a^0=0` term is inserted. No characteristic, field, noetherianity,
termwise flatness, or boundedness restrictions occur.

Searches actually run:

- `msearch.py`, LeanFinder: "regular global section ringed site quotient tensor tower
  shifted Roos cone canonical completion unit locally derived complete". Eight unrelated
  results (module presentations, condensed modules, sheaf global-sections cones, affine
  transition limits, local cohomology); none states the criterion.
- `msearch.py`, Loogle: `"completion", "IsIso"`. Zero hits.
- `msearch.py`, Mathlib grep: `regularQuotient|quotientCompletion|roosAugment|IsLocallyDerived`.
  Only two unrelated uniform-space separation-quotient-completion headings.
- `rg` in `lean/WeilConjectures` for the item id and for
  `regularQuotient|quotientCompletion|roosAugment|IsLocallyDerived`: no exact statement.
- `rg` in `lean/Sheaf` for regular quotient/completion/local-completeness terminology:
  found the canonical principal tower, strict Roos model, local predicate, and the
  regular Koszul reconstruction theorem, which are reused. Scheme/adic reconstruction
  theorems require a scheme and an adic coefficient datum and do not state this general
  small-ringed-site result.
- Exact proposed declaration names were searched in Mathlib, `WeilConjectures`, and
  `Sheaf` before writing: no existing declarations.
- DAG definition records were read for the principal tower, strict Roos model and local
  completeness. These already landed notions are cited; no new node is introduced.

Sources read: Stacks `algebraization.tex`, definition-derived-complete (0999),
lemma-derived-completion-koszul (0A0E), and the surrounding completion discussion;
`sites-cohomology.tex`, lemma-derived-limit-is-ok (0941). The five-step DAG proof and
its maintainer source review were also read. No statement correction or disputed
statement is needed.

Validation: `scompile.py ND lem-pur-regular-quotient-completion-unit` compiled the
complete delivered file cleanly as both sandbox and library module (31.5 s and 37.4 s),
within the unchanged 60-second per-file limit. Explicit universe arguments and the
existing transparency setting resolved the initial slow elaboration. There are no
warnings and exactly one postponed proof, the named main theorem. The delivery dry run
passed both server preflight and per-file compilation. Only `lean` and the three added
landed `stmt_deps` differ in the item node.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
