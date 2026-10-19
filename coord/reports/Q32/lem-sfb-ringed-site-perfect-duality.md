## Worker report

The module `Sheaf/CategoryTheory/RingedSitePerfectDuality.lean` states
`CategoryTheory.ringedSitePerfectDuality` for a small ringed site.  It uses the
recorded `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` notion for the input
and its derived internal Hom dual, `derivedInternalHomOfUniverses` for
`R𝓗om`, and the canonical K-flat derived tensor
`SheafOfModules.wfSiteDerivedTensor`.  The proof is `sorry`, as required for
stage 2.

The Lean binders render the node clause by clause.  `C`, `J`, and the four
sheafification/local-bijectivity instance binders express a small site and its
localized sites.  `R : Sheaf J CommRingCat` is the commutative coefficient
sheaf.  The `HasDerivedCategory` instance and `P` bind the unbounded derived
category object, and `hP` is the node's local perfectness hypothesis.  The
existential `D` is definitionally identified with
`derivedInternalHomOfUniverses (op P, O[0])`, and the following
`IsPerfectOnRingedSiteOfUniverses R D` is perfectness of `P^∨`.  The morphism
`b : P ⟶ R𝓗om(D,O[0])` with `IsIso b` is the canonical bidual assertion.  The
last `Nonempty` is a natural isomorphism of functors in the arbitrary second
argument: its left side is `D ⊗ᴸ -` via `wfSiteDerivedTensor`, and its right side
is `R𝓗om(P,-)` via the curried derived internal Hom.  Thus the arbitrary
`N` clause is represented by every component of this natural isomorphism.

Dependency declarations used:

- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`,
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.Paper.WeilTensorProduct`,
  `SheafOfModules.wfSiteDerivedTensor`; this is the K-flat total-tensor
  localization described by the node's `def-pc-kflat-complex` and
  `def-pc-tensor-complex-sheaves` dependencies.
- `def-weil-size-convention` is rendered by the explicit universe parameters
  `c`, `v`, `w`; no independent smaller test universe is introduced.

Edge cases checked against the source proof and statement are the zero complex,
zero coefficient terms, the empty site, arbitrary unbounded `N`, local bounds
that vary from slice to slice, degree zero and shifted complexes, and the sign
in odd degrees (including characteristic two).  No nonemptiness or global
boundedness hypothesis was added.

Searches for an existing exact declaration were made with:

- `msearch.py ... leanfinder "perfect complex duality on a small ringed site
  derived dual bidual tensor internal Hom"`: only generic derived-category linearity,
  Ext, and condensed closed-category declarations; no exact match.
- `msearch.py ... loogle "DerivedCategory, IsPerfectOnRingedSiteOfUniverses,
  derivedInternalHom"`: no hits; the project-specific name is not in Loogle.
- `msearch.py ... grep "perfect.*dual|dual.*perfect|derivedInternalHom"
  Mathlib/Algebra/Homology`: no exact ringed-site theorem.
- `rg` over `WeilConjectures/` and `lean/Sheaf`: found scheme-specific perfect
  RHom/tensor results and finite-projective local calculations, but no declaration
  for this arbitrary small ringed-site statement.

No `STATEMENT-DISPUTED` issue or node correction was found.

## Earlier second reading (a previous round; superseded)

I reopened the reviewed DAG statement and this module.  The site, coefficient
sheaf, derived-category, and perfectness hypotheses are all present; the dual
uses the unit complex `SheafOfModules.unit` in degree zero.  The first
conclusion identifies the dual exactly, the second asserts its local strict
perfectness, the third gives an isomorphism-valued bidual morphism, and the
fourth is a natural isomorphism in the arbitrary target object.  The tensor
functor is the recorded K-flat total-tensor localization, and the Hom functor
is the recorded K-injective localization.  The module contains one theorem
with a `sorry` proof and no local notation, private declarations, or auto-bound
variables.  Compilation through `scompile.py` succeeded with no errors or
warnings.

## Second reading by Q32

I read the item node, its ten proof steps, Stacks `sites-cohomology.tex`
`lemma-dual-perfect-complex` (08JJ), and the declarations actually used by the
statement. I also read the source constructions `lemma-dual` (08JD/08JE),
`lemma-internal-hom-evaluate` (0A97), `lemma-internal-hom-composition` (0A98),
and the local definition of perfectness (08G5). These places assume a ringed
site with commutative coefficients, not a field, Noetherian site, terminal
object, enough points, or a uniform global bound.

The previous report's claim that an existential isomorphism-valued morphism
asserted canonical biduality was incorrect. The same fault affected the final
arbitrary natural isomorphism. Both have been replaced by `IsIso` of explicitly
constructed canonical maps. This is a Lean repair; the item's mathematical
statement, source and proof are unchanged.

The complete object/hypothesis/conclusion list, matched with the final Lean:

| Node item | Final Lean and verdict |
|---|---|
| A site small in the module universe | `C : Type c`, `Category.{v} C`, `J : GrothendieckTopology C`; the module/coefficient universe is `max c v r`. Correct, with independent object, arrow and coefficient sizes. |
| Commutative coefficient sheaf O | `R : Sheaf J CommRingCat.{max c v r}`. Forgetting to `RingCat` gives precisely Mathlib's module-sheaf coefficient, rather than a constant coefficient or a scheme specialization. Correct. |
| Module sheaves and their abelian derived category | `SheafOfModules` is the recorded `ringedSiteModules` abbreviation, definitionally. `HasSheafify` and `WEqualsLocallyBijective` supply its abelian/sheafification infrastructure, also on slices; `HasDerivedCategory.{w}` supplies the chosen localization sizes. These are the constructions available on a site small in the chosen module universe. Correct. |
| Arbitrary P in the unbounded D(O) | The `P : DerivedCategory (SheafOfModules ...)` binder is unrestricted apart from `hP`. There is no bounded-derived-category binder. Correct. |
| P locally represented by bounded finite-free summands | `hP : IsPerfectOnRingedSiteOfUniverses R P`. I opened this definition: it existentially chooses a representative, and for every object a covering sieve and an actual quasi-isomorphism from a bounded local complex. `StrictPerfectCoefficientPackageOnSite` supplies independent finite ranks and degreewise inclusion/retraction maps. Bounds/ranks vary by cover member and the splittings need not be chain maps. Correct. |
| K-flat total tensor and K-injective internal Hom | The existential `M : RingedSiteDualityModel J R` is a normalized presentation of the existing `CoefficientClosedStructure` and `CoefficientTensorModels`, with `derivedInternalHomOfUniverses` as its actual Hom bifunctor. `models.comparison` is natural total-tensor localization on K-flat complexes, and `models.uncurry_model` uses the actual sheafification unit, tensor generators, Hom projections, fixed K-injective augmentation and localization factorization. The three additional model fields pin scalar multiplication, reassociation and Koszul interchange. This is a presentation choice in the conclusion, not an additional existence hypothesis on P or R. Correct. |
| The coefficient object is O[0] | `ringedSiteDualityUnitComplex` is `HomologicalComplex.single ... (.up ℤ) 0` of `SheafOfModules.unit`; `ringedSiteDualityUnit` is its image under Q. The model's `unit_model` identifies its monoidal unit with exactly this object by scalar multiplication. Correct. |
| Dual P^vee is RHom(P,O) | The first conclusion uses `(derivedInternalHomOfUniverses J R).obj (op P, ringedSiteDualityUnit J R)` directly. No independently chosen dual object or identification is needed. Correct. |
| The dual is perfect | The first conjunct is `IsPerfectOnRingedSiteOfUniverses R` of that exact dual object. Correct. |
| The canonical bidual map is an isomorphism | The second conjunct is `IsIso (ringedSiteBidual M.closed M.symmetric O P)`. This definition transposes evaluation after the normalized symmetry. `ringedSiteBidual_normalization` identifies it under the actual augmentation comparisons with signed ordinary evaluation, without a flatness assumption on E or its ordinary dual. Correct; repairs the arbitrary existential b. |
| Every arbitrary N, naturally | The final conjunct is `IsIso (ringedSiteDualEvaluationLeftNatTrans ... P)`. This is an actual natural transformation of functors on the entire unbounded derived category. Its components are defined by transposing composite evaluation and composing the normalized symmetry. `IsIso` in the functor category means these very components have natural inverses. Correct; repairs the arbitrary `Nonempty (F ≅ G)`. |
| Tensor order dual tensor N | `ringedSiteDualEvaluationLeft` explicitly precedes the 08JE comparison by `s.braiding (H(P,O)) N`. Its source is exactly dual tensor N. Correct. |

The additional prerequisite `lem-sfb-ringed-site-duality-maps` already existed
in the DAG (created in the stage-1 split) but had no Lean record. I supplied
its own module and node binding under the human's "nothing waits" rule. I did
not weaken its statement or replace it by the perfect-only special case. Its
map definitions do not assume perfectness or assert their invertibility.

I read that dependency against its full source statement:

- `ringedSiteBidual` and `ringedSiteDualEvaluation` are actual transposes, not
  unspecified morphisms. Evaluation agrees with composition after Hom-unit
  identification by the closed adjunction formula.
- `ringedSiteBidual_naturality`, `ringedSiteDualEvaluation_naturality`, and
  `ringedSiteDualEvaluation_source_naturality` state the three required
  naturality equations. The natural transformations use those named theorems.
- `ringedSiteHomAugmentation`, `ringedSiteHomComplexMap`, and
  `ringedSiteOrdinaryHomComparison` use the fixed replacement and recorded
  Hom-complex functor. The comparison iso is built with `asIso` from a named
  invertibility theorem; it is not an arbitrary Hom representative iso.
- `RingedSiteBidualFormula` uses the actual Hom-product projections on all
  localized sections and the sign `(-1)^(i*q)`. The ordinary map is selected
  from an existence-and-uniqueness statement with that formula, so its data
  is determined. The named normalization theorem asserts the exact comparison
  square for both ordinary-to-derived augmentations, with no flatness premise.
- `RingedSiteEvaluationFormula` gives the unsigned formula `phi(x) • y`, on
  actual sheafified tensor summands, together with zero in every other Hom
  component. Its map is again selected only from the uniquely characterizing
  statement. Its normalization theorem has exactly K-flatness of F and D and
  the two augmentation quasi-isomorphism hypotheses required by the node.
- `ringedSiteDualityMaps_restriction` uses actual termwise `overFunctor`
  restriction and its derived localization factorization; it states tensor,
  Hom and coefficient comparisons, their evaluation compatibility, and the
  two explicit commutative squares for the same previously defined maps.
  Slice object size is `max c v`, arrow size is `v`, and its derived size `w'`
  is independent of the base's `w`.

No new DAG definition node is introduced. The added structure and formula
predicates are helper declarations of the existing canonical-map node. They
reuse the recorded closed-model, Hom and total-tensor definitions; there is no
second module-sheaf category, perfectness predicate, derived tensor, or RHom.
Every postponed theorem is a standalone named theorem with whole proof
`sorry`, the matching canonical-map/item blueprint tag, source and proof plan.
The data definitions contain no `sorry`; the ordinary-map selections come from
unique characterizations. No file-local notation, private declaration, local
instance, unbound universe, or statement-local `let` is used. The existing
short proof docstring was expanded to follow all ten current node proof steps,
and all already stated proof-dependency modules are imported.

Edge cases: the zero complex and zero ring are admitted; finite-free rank zero
is allowed. An empty site introduces no object or covering nonemptiness
requirement. The perfectness predicate imposes only local integer bounds, so
locally varying bounds and arbitrary unbounded N remain covered. The ordinary
unit is in degree zero of a Z-indexed complex. All integer degrees and odd
signs are retained, including characteristic two. There is no restriction on
characteristic or on site/coefficient/derived universe equality. `w'` for a
slice is separate from `w`. Thus zero objects, empty geometric specializations,
zero degrees and all coefficient characteristics covered by the node remain
in scope.

Independent searches used different words from the first report:

- `msearch.py ... leanfinder "derived sheaves of modules tensor Hom canonical
  evaluation bidual perfect complexes"`: underived condensed closed structures
  and generic closed categories only; no exact arbitrary ringed-site theorem.
- `msearch.py ... leansearch "canonical derived bidual evaluation for perfect
  complexes of sheaves on ringed sites"`: ordinary linear dual/reflexivity and
  perfect-pairing results only.
- `msearch.py ... loogle '"bidual"'`: no hits.
- `msearch.py ... grep 'toIhomIhomUnit|ihomUnitTensorToIhom'
  Mathlib/Algebra/Homology`: no hits.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for bidual, derived evaluation and perfect dual found ordinary sheaf biduality,
  coefficient-module perfect duality, scheme-specific perfect tensor-Hom
  statements and etale-specific statements. I opened those signatures; none
  takes this arbitrary ringed site and the recorded local-perfectness predicate.
- Searching the DAG and project for tensor-Hom models found
  `def-coef-ringed-tensor-hom-model`. I opened its exact node and source module
  (also confirmed by `scompile.py --source`) and reused it. Its coefficient
  and site sizes are independent. The older scheme model is a specialization.
- The final helper names were searched throughout Mathlib, upstream and project
  sources; none duplicates an existing declaration.

Mismatches repaired: (1) arbitrary bidual morphism instead of canonical b;
(2) arbitrary natural iso instead of canonical evaluation; (3) the proof did
not import all its stated dependencies or carry all ten proof steps;
(4) independent larger coefficient sizes were not retained by the old tensor
interface. The final module uses the existing normalized general model and
`max c v r`, rather than restricting coefficients to `max c v`.
The item gains the already existing normalized-model dependency and the
canonical-map prerequisite supplied here. There is no statement correction,
unit change or unresolved statement dispute.

I also read the sole current citer,
`det-thm-sf-ctf-stability-internal-hom`, especially steps 6 and 10: it uses
perfectness of the coefficient dual and the tensor-Hom formula for arbitrary
ambient N on the pro-etale site. Both uses hold with the repaired canonical
statement and independent site/coefficient universes. No citer changes.

## Dependency modules

`lem-sfb-ringed-site-duality-maps`: the base had no usable recorded declaration.
`Sheaf.CategoryTheory.RingedSiteDualityMaps` supplies the exact general canonical
maps, normalized existing closed-model presentation, both naturalities,
ordinary representative normalizations and exact slice restriction, as detailed
above. It leaves the node's mathematical statement and all dependency fields
unchanged. All its declarations are recorded in `lean.declarations`.

The restriction compile exposed the difference between the ring sheaf obtained
by forgetting commutativity before restriction and the one obtained afterward.
`ringedSiteDualityRestrictionCoefficient_eq` states their actual equality
(the sections and restriction maps coincide), and termwise restriction composes
`overFunctor` with `restrictScalars (eqToHom ...)`. This is the canonical
coefficient transport and adds no ring map or universe hypothesis. Its equality
proof is a named theorem of the same canonical-map node. No live source or
shared-library file was edited.

Validation: both delivered modules compiled separately, in dependency order,
through `scompile.py` with the standard 60-second per-file limit. The final
`deliver2.py --no-push` run compiled them cleanly with no warnings and printed
`OK (dry run): commit 1b372bdf40 passes the preflight and compiles`.
The delivered `lean.statement` fields quote the main signatures verbatim.
