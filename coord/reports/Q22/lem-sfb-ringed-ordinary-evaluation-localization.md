## Worker report

The module `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization` states
`CategoryTheory.ringedOrdinaryEvaluation_localization`. Its sole postponed theorem
is this item itself; all six supporting definitions have explicit data or Prop formulas.
The node changes only in `lean`; no new node, dependency repair or statement correction
is needed. The nine-step natural-language proof is included in the theorem docstring.

Hypothesis and clause correspondence:

- The site is `{C : Type c} [Category.{v} C] (J : GrothendieckTopology C)`.
  `R : Sheaf J CommRingCat.{max c v u}` is the commutative coefficient sheaf.
  Module universe `max c v u` contains both site sizes and an independent coefficient
  bound `u`. `HasSheafify` and `WEqualsLocallyBijective` expose sheafification and
  its local equivalences in that universe. These are the recorded small-site interfaces,
  not geometric restrictions. The derived Hom universe is independently `w` through
  `HasDerivedCategory.{w}`. Objects and arrows of the site need not have equal universes.
- Module sheaves are the dependency's `RingedTensorModules J R`, transparently the
  recorded `ringedSiteModules` and Mathlib `SheafOfModules`. Complexes `E,F` are arbitrary
  integer cochain complexes. `DerivedCategory.Q` is their unbounded localization.
- The complex O is exactly `ringedTensorUnitComplex J R`, the single complex on the
  coefficient module in degree zero. D is written explicitly as `homComplex E O`.
  Ordinary tensor is the recorded `coefficientTotalTensor J R`.
- `S : CoefficientClosedStructure (derivedInternalHomOfUniverses J R)` and
  `T : CoefficientTensorModels J R S` are the fixed closed structure and its canonical
  K-flat/uncurrying model. `β` and `coh : RingedDerivedTensorCoherence J R S T β`
  retain the source's specified symmetric monoidal coherence and coefficient-unit
  identification. These express the fixed canonical model in the node, not an
  unrelated arbitrary monoidal structure.
- The existential `aEF` is a chain map from `Tot(F tensor Hom(E,O))` to `homComplex E F`.
  It precedes all flatness and augmentation hypotheses. The first conjunct is
  `RingedOrdinaryEvaluationFormula E F aEF`. The second says EVERY chain map satisfying
  this formula equals `aEF`, independent of any derived comparison property.
- The formula quantifies over all integer p,q,n,a,b, equations p+q=n and a+n=b,
  all objects U, and all sections y,phi,x. `coefficientTensorGenerator` is the actual
  sheafification unit followed by the total-coproduct inclusion, not an arbitrary
  tensor map. `ringedOrdinaryHomValue` uses `coefficientHomComponent` and
  `coefficientHomSectionApply`, namely evaluation at the identity object in C/U.
  Thus all Hom-product projections and all local pure-tensor generators are tested.
- If a+q=0, `ringedOrdinaryDualValue` evaluates phi(x) in O^0 and applies the actual
  `singleObjXSelf.hom` to obtain its coefficient. The result acts on y by `•`.
  `hp : p=b` and `eqToHom (congrArg F.X hp)` merely transport equal degrees. Given
  hn, hb and a+q=0, p=b follows in integer arithmetic, so quantification over hp
  excludes no supported case. If a+q is nonzero the second conjunct requires zero.
  There is no Koszul scalar in either branch. The scalar is written on the left
  because these are modules over a commutative coefficient sheaf.
- `ringedDualTensorHom S coh.unitIso A B` is theta: `S.transpose` of the recorded
  associator, `1 tensor S.evaluation A QO`, the inverse coefficient-unit identification,
  and the recorded right unitor. Inserting the coefficient-unit identification types
  exactly the node's convention identifying O and the monoidal unit.
- The conditional clause assumes only `hF : IsKFlatIndependentCoefficients F` and
  `hD : IsKFlatIndependentCoefficients (homComplex E O)`. No flat-term hypotheses,
  K-flatness of E, or K-injectivity of F are present.
- The other two assumptions are `QuasiIso (ringedHomAugmentationMap E O)` and
  `QuasiIso (ringedHomAugmentationMap E F)`. This map is precisely ordinary Hom
  applied to `coefficientHomAugmentation`, the fixed functorial K-injective augmentation.
- `ringedOrdinaryHomComparison E G` is Q of that actual augmentation-Hom map followed
  by `(coefficientHomResolutionIso E G).inv`. The theorem asserts `IsIso` for each
  of the two canonical morphisms. This specifies the gamma isomorphisms without
  choosing any substitute identification with derived Hom.
- The final equality, written in Lean's left-to-right composition order, is
  `mu.hom ≫ (1 tensor gamma_O) ≫ theta = Q.map aEF ≫ gamma_F`.
  `mu` is exactly `T.iso J R S F D hF hD`, valid on K-flat pairs without flat terms.
  The node's reference to the flat-term descent lemma supplies the provenance of
  the tensor, while its already-assumed canonical model supplies this K-flat-pair
  comparison, exactly as the stage-1 review of this node explains.

Dependency declarations used/read:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `def-weil-size-convention` is metatheoretic and supplies no declaration.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, quasi-isomorphism localization.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex` and
  `homComplexFunctor`; `HomComplexComponents` supplies the actual projections.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  total tensor is used through its recorded `coefficientTotalTensor` presentation.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  `CoefficientTensorModels`, `CoefficientTensorModels.iso`,
  `coefficientTotalTensor`, `coefficientTensorGenerator`, evaluation and transpose.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `RingedTensorModules`, `ringedTensorUnitComplex`, `RingedDerivedTensorCoherence`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` (proof-only import).
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`: `coefficientHomComponent`,
  `coefficientHomResolution`, `coefficientHomResolutionIso`.
- Existing `Sheaf.Paper.CoefficientTensorCurryNormalization` supplies
  `coefficientHomAugmentation`; its public dependency `CoefficientCochainTensorCurry`
  supplies `coefficientHomSectionApply`. Both are used directly without a duplicate.
- Proof-only imports retain `def-pur-sheaf-tensor-product` through
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `def-weil-presheaf-modules-sheafification` through
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, and
  `lem-pc-kflat-resolution` through
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
  Internal sheaf Hom is the existing `SheafOfModules.homObj` in the imported
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.

Sources read: local Stacks `sites-cohomology.tex`, lemma-internal-hom-composition
(lines 8998 onward), lemma-dual/equation-eval (9114 onward), and the main-20261015
blueprint's `sk-thm-sf-ctf-stability-internal-hom.md`. Its second displayed
isomorphism is the ancestor application; this auxiliary node's representative
proof is the explicit nine-step proof recorded by stage 1, not a claim that the
blueprint contains those proof paragraphs.

Edge cases checked before and after writing:

- Zero E, zero F and the zero coefficient ring: the scalar and zero branches agree,
  and the formula still characterizes the zero map; no nonzero assumption is present.
- Degree zero reproduces ordinary module scalar evaluation. Odd p or q adds no
  sign. The a+q+1=0 adjacent unsupported component contributes to the differential
  through d_D, as documented in step 2; it is not dropped from the formula.
- Arbitrarily unbounded E and F are admitted. Products and coproducts are the actual
  recorded constructions, with no boundedness or finite-support hypothesis.
- All U and all projections are tested; we never assume every section of a sheaf
  tensor is globally pure. The sheafification universal property detects equality.
- A site with no objects gives a vacuous local formula in a trivial module category;
  uniqueness remains the actual chain-map uniqueness assertion.
- Independent site object, site arrow, coefficient and derived-morphism universes
  are retained; no equality of site universes or small native-only tensor API is used.

Searches for an existing whole statement:

- `msearch.py ... leanfinder`: "Unsigned ordinary cochain evaluation F tensor
  Hom(E,O) to Hom(E,F) and localization by fixed K-injective augmentations".
  Eight hits, including `CochainComplex.cm5b.I`, `IsKInjective`, and cohomology-class
  maps into derived Hom; none states this sheaf-internal evaluation square.
- `msearch.py ... loogle`: `"ihomUnitTensorToIhom"`: zero hits.
- `msearch.py ... grep`: `ihomUnitTensorToIhom|dualTensorHom|ordinaryEvaluation`
  in Mathlib CategoryTheory: zero hits.
- `msearch.py ... leansearch`: "The unsigned chain map F tensor Hom(E,O) to
  Hom(E,F) agrees with derived evaluation through fixed K-injective augmentations".
  Eight hits: `Functor.rightDerived_map_eq`, `HomologicalComplex.tensorHom`,
  module evaluation and related injective-resolution results; no whole-statement match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for those names, evaluation and
  localization: found scheme-only ordinary evaluation files, module dual-tensor
  maps, categorical `ihomUnitTensorToIhom` (opposite factor convention), and coefficient
  tensor-currying helpers. The latter helpers were reused; the whole statement is absent.
- ID search in `lean/WeilConjectures` and `lean/Sheaf`: no occurrence of this node.
  DAG search finds the item and its proof consumer `lem-sfb-ringed-site-duality-maps`.
  No new notion independent of the statement is introduced by the six formula/map helpers.

Validation: prescribed `scompile.py` checked the sandbox and actual library module paths.
The first pass found two elaboration ambiguities, repaired by explicit Hom-functor
universes/coefficient and explicit tensor-left instance selection. The second pass compiled
with one line-width warning, now corrected. Final clean compile and delivery preflight
are recorded below when complete. No mathematical node fault or disputed statement.

## Second reading by Q22

A second pass in this same worker (no independent agent was started, as instructed)
compared the complete node and module. The ordinary existence is outside the conditional
hypotheses, and uniqueness tests the ordinary formula alone. All supported components
are covered because p+q=n, a+n=b and a+q=0 imply p=b; the other branch explicitly
vanishes. The coefficient is extracted by the actual single-complex identification,
and the canonical fixed augmentation is used in each gamma. The square's direction
is mu then 1 tensor gamma then theta, versus Q(a) then gamma, as required. The tensor
model and coherence parameters specify exactly the fixed data assumed in the source.
The only changes found necessary were elaboration annotations and one line wrap;
no hypotheses, clauses, sources or DAG dependencies changed. Independent mathematical
review remains the maintainer's delivery review, as stated in the dispatcher brief.

Final validation: `deliver2.py Q22 lem-sfb-ringed-ordinary-evaluation-localization
--no-push` printed `OK (dry run): commit c1c464cc6f6 passes the preflight and compiles;
nothing pushed`. Both sandbox and library-path per-file compiles are clean with no
remaining warning. A local JSON comparison confirms that `lean` is the only changed
node field, and the 205-line module has no line over 100 characters and one `sorry`.
