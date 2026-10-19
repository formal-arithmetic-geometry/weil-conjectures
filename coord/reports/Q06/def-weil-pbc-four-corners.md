## Worker report

`Sheaf.Paper.ProperBaseChangeFourCorners` defines
`AlgebraicGeometry.Scheme.properBaseChangeFourCorners` and its canonical coefficient
and reduction/pullback comparisons. The node's statement and dependencies are unchanged.
Only this module and the item's lean record are delivered. Every theorem has proof
`sorry`; definitions supply actual data, and choices of comparisons retain determining
universal properties or unique normalization formulas.

Hypotheses and clauses, in the order of the node:

- `A : Type (t+1)` with `[CommRing A]` and
  `d : ProEtaleAdicCoefficientDatum A` reuse the published completed-coefficient datum.
  Its inherited `noetherian`, `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`,
  and `quotientFinite` express exactly the five coefficient conditions. `r`,
  `a : Fin r → A`, and `ha : Ideal.span (Set.range a) = d.ideal` specify the generators.
- The positive level represented by `n : ℕ` is `n+1`. `fourCornerRingTower` has objects
  `A ⧸ d.ideal^(n+1)` and the actual consecutive quotient factors. No positive level
  is omitted. `adicLisseRingSystem T d.ideal` is the existing constant quotient tower;
  `adicDatumRing T d` is its actual inverse limit, with `adicDatumProjection T d n`.
  This finite constant presentation is the recorded equivalent presentation of the
  continuous-component-function coefficient sheaves, through
  `adicDatumFiniteCoefficientIso` and its quotient naturality. There is no identification
  of the completed sheaf with the constant sheaf of A.
- `fourCornerDerived T R` transparently abbreviates the standard unbounded derived
  category of the existing `proEtaleRingModules T R`. The small site's object universe
  is t+1 and its morphism universe is t; coefficients and modules have universe t+1.
- `X' X Y' Y : Scheme.{t}`, with `g', f', f, g` of the displayed sources and targets,
  give the square. `_sq : ChosenCartesianSquare g' f' f g` retains its chosen pullback
  isomorphism and both projection equations; `[IsProper f]` retains properness.
- `fourCornerCoefficientTowerNaturality` identifies all arrows of the strict coefficient
  diagrams, including identities and nonconsecutive quotient arrows. The resulting
  identity-on-objects `fourCornerCoefficientTowerIso` transports the specified
  `proEtaleProfiniteComparison` to `adicDatumRing`. `fourCornerFiniteIso` is the specified
  `proEtaleConstantComparison` on the actual quotient ring. Both are obtained by `asIso`
  of the recorded maps, whose invertibility the dependency states.
- `fourCornerProjectionComm` is precisely pi_(U,n) c_u = c_(u,n) u^-1 pi_(V,n).
  `fourCornerFiniteTransitionComm` covers every quotient b to a, including equality.
  `fourCornerCoefficientCoherence` states the identity and composition laws for both
  the integral and finite identifications, using the dependency's inverse-image mates.
  These helpers apply to every scheme arrow, hence to each arrow of the square.
- `fourCornerPullback` and `fourCornerPushforward` specialize the recorded ordinary,
  uncompleted operations to these integral identifications. Their finite versions
  specialize those same operations at the quotient coefficient sheaves. Pullback is
  exact termwise descent; pushforward is derived using K-injectives in all module
  sheaves. No constructibility or boundedness restriction is imposed.
- `K : fourCornerDerived X (adicDatumRing X d)` is arbitrary except for derived
  completeness. `C` and `eC : DerivedCategory.Q.obj C ≅ K` expose a representative;
  `_hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC` is invertibility
  of the published signed Koszul completion unit. C has no flatness or boundedness
  hypothesis. The definition of completeness descends through representatives.
- `adicDatumReduction T d n` is the existing quotient-coefficient derived extension
  of scalars along the actual projection. Thus K_n is its value at K, E is ordinary
  `fourCornerPullback g' d` applied to K, and E_n is finite pullback of K_n. Each
  reduction retains its finite quotient scalar action.
- `fourCornerRestrictionPushforward_exists` uniquely specifies identity on underlying
  direct-image sections; the projection compatibility proves linearity.
  `fourCornerOrdinaryComparison` is its conjugate under the published, normalized
  scalar-extension and module-pullback adjunctions. This is the balanced tensor
  comparison, not an arbitrary natural isomorphism. `fourCornerOrdinaryComplexComparison`
  applies it in every degree with the naturality equation as its chain-map law.
- `fourCornerReductionPullback_exists` fixes the derived comparison uniquely by its
  normalization square on every K-flat complex with flat terms. The square uses the
  existing universal `adicDatumComplexCounit` and exact-pullback localization factors.
  The dependency `proEtaleCanonicalTensorPullback` supplies preservation of flat
  K-flat representatives. Consequently both scalar extensions in this square have
  the ordinary tensor computation specified by the node. On a quotient transition,
  both maps apply pullback to the module element and the quotient to its scalar;
  the proof docstring records this pure-tensor equality and its localization.
  `fourCornerEReductionIso` evaluates this specified comparison at K, in the direction
  E tensor^L P_n to E_n, in the finite coefficient derived category.
- The result is the ordered tuple A_n, B_n, C_n, D_n, all in the quotient-coefficient
  derived category on Y'. Its entries are, verbatim in mathematical order: finite
  g-pullback of reduction of integral f-pushforward; finite g-pullback of finite
  f-pushforward of K_n; reduction of integral f'-pushforward of E; finite f'-pushforward
  of E_n. No completed pullback occurs.

Dependency source declarations read:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`, with
  `isoPullback`, `hom_fst`, `hom_snd` and inherited commutativity.
- `Sheaf.Paper.AdicCoefficientDatum` and its publicly available completed-coefficient
  interface `Sheaf.Paper.AdicCoefficientDatumCompleted`: `ProEtaleAdicCoefficientDatum`,
  `adicDatumFiniteCoefficientIso`, `adicDatumFiniteCoefficientIso_natural`, `adicDatumRing`,
  `adicDatumModules`, `adicDatumProjection`, `adicDatumExtension`, `adicDatumReduction`,
  `adicDatumOrdinaryAdjunction`, and `adicDatumComplexCounit`. The published finite
  constant presentation supplies the same coefficients through its normalized comparison.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`, `completedIntrinsicCompletionMap`, and
  `completedIntrinsicCompletion_descends`; the completion is the specified Koszul fiber.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` publicly retains
  `ProEtaleOperations`: `proEtaleRingModules`, `proEtaleRingModulePullback`,
  `proEtaleRingModuleDirectImage`, `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedDirectImage`, and `proEtaleRingDerivedPullbackFactors`.
  `ProEtaleOperationsCanonicalAdjunction` supplies `proEtaleRingModuleAdjunction`
  with its tensor-unit normalization.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtale_profinite_coefficient_inverse_image`, `proEtaleConstantComparison`,
  `proEtaleProfiniteComparison`, `proEtaleRingInverseImageId`, and
  `proEtaleRingInverseImageComp`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`; the existing adic scalar
  extension and its universal counit are selected from this exact derived pair.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: `proEtaleCanonicalTensorPullback`,
  its ordinary tensor normalization, and preservation of flat K-flat representatives
  at the actual small-site universes. This also reexports the arbitrary-site theorem.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`, including flat terms,
  the quasi-isomorphism and degreewise epimorphic augmentation. This is a proof import.

Edge cases checked: n=0 is exponent one; zero rings and empty schemes are admitted;
I=0, I=A and r=0 are admitted; the empty Koszul product is the unit in degree zero.
There is no assumption that A is I-adically complete, no regular-sequence assumption,
no characteristic restriction, and no boundedness assumption on K or its representative.
Identity arrows, equal quotient indices, nonconsecutive transitions and composition
are included. The K-flat hypotheses normalize the canonical comparison only and do
not restrict the input K.

Searches rerun with msearch.py:

- LeanFinder, "Four finite level derived coefficient corners in a proper cartesian
  square with pullback pushforward and reduction modulo an ideal": eight unrelated
  adic-completion, quotient and ramification hits; none states these four corners.
- Loogle, "SheafOfModules.pullback, CategoryTheory.Functor.mapDerivedCategory": zero hits.
- Mathlib grep, "fourCorners|FourCorners|properBaseChangeFourCorners": zero hits.
- rg of the same names and the node id in upstream WeilConjectures and shared lean/Sheaf:
  zero hits. The upstream name table also contains no four-corner declaration.
  Prior logged LeanSearch for the four-corner statement returned Internal Server Error;
  that result is unavailable, not evidence of absence.

No statement correction, new nodes, dependency replacements or disputed statement.
The module reuses the currently published dependencies; the earlier dependency copies
are retained only in scratchpad as historical work, outside the delivery.

Source checks: the blueprint node's four displayed formulas and its coefficient and
representative clauses were read in full. Stacks
[07A4](https://stacks.math.columbia.edu/tag/07A4) gives the canonical bifunctorial
ordinary derived pullback/tensor comparison, and
[0G7E](https://stacks.math.columbia.edu/tag/0G7E) preserves flat K-flat representatives.
The contextual completion lemma
[099N](https://stacks.math.columbia.edu/tag/099N) and proper base-change theorem
[09C9](https://stacks.math.columbia.edu/tag/09C9) were also opened. The four-corner
assembly is the blueprint's own definition; those contextual results do not replace
ordinary pullback in its formula for E.

## Second reading by Q06

I independently read the sandbox node and the complete Lean module, and opened the
signatures and constructions of all eight recorded statement dependencies. The
natural-language statement is unchanged. The four corner definitions were already
correct and have not been rewritten.

Source reading: the blueprint's `def-weil-pbc-four-corners.md` defines the four
objects and explicitly uses ordinary E. I read `proetale.tex`, the introductory
paragraphs of Section `section-derived-completion-noetherian`,
`lemma-naive-completion`, `lemma-pushforward-Noetherian-case` (099N), and
`theorem-proper-base-change` (09C9). I also read `sites-cohomology.tex`,
`lemma-pullback-K-flat` (0G7E) and `lemma-pullback-tensor-product` (07A4), including
their proofs. These sources were available in the local literature checkout;
the four tag pages were checked as well. The source theorem 09C9 has an additional
bounded-below/etale-origin condition for its isomorphism conclusion. This node
only defines four objects, so that theorem-specific condition is not an input to
this definition. No claim of proper base-change invertibility is made here.

The following is my object/hypothesis/conclusion checklist, with its Lean rendering
and verdict for each entry:

1. A is commutative Noetherian; I has a finite generating tuple; A/I is additive
   torsion; every positive quotient is finite and perfect over A.
   `A : Type (t + 1)`, `[CommRing A]`, `d : ProEtaleAdicCoefficientDatum A`,
   `r : ℕ`, `a : Fin r → A`, and `ha : Ideal.span (Set.range a) = d.ideal`.
   I opened `CompleteCoefficientDatum` and the extending
   `ProEtaleAdicCoefficientDatum`: their fields are `noetherian`,
   `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`, and `quotientFinite`.
   The tuple supplies the generators used by completion, with no regularity
   assumption. Verdict: exact.
2. Positive levels P_n=A/I^n, constant finite coefficient sheaves, actual inverse
   limit A_T and its projections. `fourCornerRingTower` and
   `adicLisseRingSystem T d.ideal` use exponent `n + 1`; `adicDatumRing T d` is
   the limit, and `adicDatumProjection T d n` its projection. I opened
   `AdicCoefficientDatumCompleted`, its finite coefficient isomorphism and
   quotient naturality, and `AdicCoefficients.coefficientRing`. The constant
   presentation is connected to continuous component functions by the normalized
   sheafification comparison; it does not identify A_T with constant A.
   Verdict: equivalent presentation with all coefficient maps retained.
3. Ambient category D(Mod(A_T)) and quotient-coefficient derived categories.
   `fourCornerDerived T R` abbreviates `DerivedCategory (proEtaleRingModules T R)`;
   the module definition uses the given ring sheaf, not constant A. I checked the
   standard localization instances. Verdict: exact unbounded categories.
4. Schemes X', X, Y', Y, arrows g', f', f, g, chosen Cartesian square and proper f.
   The four `Scheme.{t}` binders and corresponding morphisms have exactly the
   displayed sources and targets. `ChosenCartesianSquare` includes commutativity,
   `isoPullback`, `hom_fst`, `hom_snd`; `[IsProper f]` supplies properness.
   Verdict: exact, with no properties of the other arrows assumed.
5. Specified finite and integral inverse-image ring isomorphisms for every arrow.
   `fourCornerFiniteIso` is `asIso` of the actual constant comparison;
   `fourCornerCoefficientIso` is the actual profinite comparison transported by
   `fourCornerCoefficientTowerIso`. I opened `ProfiniteCoefficientInverseImage`:
   its map is the universal limit comparison followed by the fixed constant
   comparisons, not an arbitrary limit isomorphism. All helpers take arbitrary
   scheme morphisms, so cover each square arrow. Verdict: exact canonical maps.
6. Compatibility with projections, quotient transitions, identities and composition.
   `fourCornerProjectionComm`, `fourCornerFiniteTransitionComm`, and
   `fourCornerCoefficientCoherence` state precisely these equalities, with the
   dependency's canonical identity/composition inverse-image mates. Diagram
   naturality covers every arrow of the inverse sequence. Verdict: exact.
7. Ordinary ringed-coefficient pullback/direct image at integral and finite levels.
   `fourCornerPullback`, `fourCornerPushforward`, `fourCornerFinitePullback`,
   `fourCornerFinitePushforward` specialize `ProEtaleOperations` at the preceding
   isomorphisms. I opened their definitions: pullback is sheafified scalar extension
   of inverse image and exact termwise descent; direct image is sectionwise
   base change with the adjoint scalar action and unbounded right derivation in
   all module sheaves. Verdict: exact ordinary, uncompleted operations.
8. K is derived I-complete. `K`, `C`, `eC`, `_hK` use
   `IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC`. I opened its actual
   signed Koszul mapping-fiber unit and representative-descent theorem. The extra
   representative C and its realization expose that definition; neither is
   required to be bounded or flat. Verdict: exact representation of completeness.
9. Every tensor with P_n is derived extension along the actual projection, valued
   over P_n. `adicDatumReduction` is `adicDatumExtension` at that projection.
   I opened the universal derived pair, its ordinary object/morphism specifications,
   the cochain counit and its K-flat invertibility. Verdict: quotient actions are
   retained, rather than reducing only in the integral category.
10. K_n, E, E_n. Respectively `(adicDatumReduction X d n).obj K`,
    `(fourCornerPullback g' d).obj K`, and finite g'-pullback of the first term.
    Verdict: exact, particularly ordinary E rather than completed E.
11. Canonical ordinary tensor comparison and finite-linear derived identification
    E tensor P_n to E_n. `fourCornerOrdinaryComparison` is the adjunction conjugate
    of the uniquely sectionwise-identity restriction/direct-image comparison.
    I checked both adjunctions' tensor-unit normalizations.
    `fourCornerOrdinaryComplexComparison` uses that same map termwise;
    `fourCornerReductionPullback_exists` uniquely fixes the derived isomorphism
    on every flat-term K-flat complex using the actual scalar-extension counits
    and exact pullback localization comparisons. `fourCornerEReductionIso` is
    its value at K in the finite coefficient category. Verdict: canonical with
    the required direction and coefficient action, not a bare Nonempty choice.
12. K-flat representative computation and preservation under pullback.
    `fourCornerReductionPullback_exists` quantifies over every P with
    `CochainComplex.IsKFlat` and `SheafOfModules.IsFlatOnSite` in each degree.
    I opened `proEtaleCanonicalTensorPullback`, including its preservation clause,
    and `exists_isKFlatResolutionIndependentCoefficients`, including flat terms,
    quasi-isomorphism, and degreewise epi. Those conditions normalize the comparison
    and are not additional hypotheses on K. Verdict: exact representative computation.
13. Quotient transitions commute with the reduction/pullback comparison.
    This was previously explained only in the proof docstring. I added
    `fourCornerRestrictionPullback_exists` and `fourCornerRestrictionPullback`:
    the integral/finite restriction-pullback isomorphism is uniquely specified by
    the normalized finite pullback unit, the fixed restriction/direct-image
    comparison, and integral adjunction transposition.
    `fourCornerOrdinaryComparisonUnderlying` restricts the already finite-linear
    comparison and uses that identification. The added theorem
    `fourCornerOrdinaryComparison_transition` states the commuting square with
    the actual `adicDatumOrdinaryTransition` at arbitrary a ≤ b. Its two sides
    apply the same quotient to the scalar of a pulled-back pure tensor.
    Degreewise equality and localization, with the existing normalization theorem,
    give the node's equality of induced derived comparisons. Verdict: repaired
    the missing formal transition equation, without changing the finite-linear map.
14. A_n = finite g-pullback of reduction of integral Rf_*K.
    The first tuple component is exactly finite pullback g applied to
    `adicDatumReduction Y d n` of `fourCornerPushforward f d` of K.
    Verdict: exact order of operations and coefficient categories.
15. B_n = finite g-pullback of finite Rf_*K_n.
    The second tuple component first reduces K on X, then applies
    `fourCornerFinitePushforward f d n`, then `fourCornerFinitePullback g d n`.
    Verdict: exact, with finite coefficients in both operations.
16. C_n = reduction of integral Rf'_*E; D_n = finite Rf'_*E_n.
    The third component applies integral g'-pullback, integral f'-pushforward,
    then reduction on Y'. The fourth reduces on X, applies finite g'-pullback,
    then finite f'-pushforward. The result type is four objects of the same
    quotient-coefficient derived category on Y'. Verdict: both clauses exact.

Edge cases: n=0 denotes the first positive quotient, and all positive n occur.
Zero rings, zero complexes and empty schemes are allowed. r=0 and I=0 are allowed;
I=A is allowed when the datum's stated conditions hold. The empty Koszul tensor
is the degree-zero unit. No Nontrivial, nonempty-space, characteristic,
regular-sequence, coefficient-completeness, constructibility, or boundedness
assumption was added. Equal quotient levels and nonconsecutive transitions occur
in the new equation. Identity arrows and composed arrows occur in coefficient
coherence. All universes are bound: schemes have universe t; the small site has
object universe t+1 and morphism universe t; coefficients/modules have universe
t+1. No equality of the two site universes is imposed. The derived-category size
is the standard localization already used by the dependencies.

Independent searches (different queries from the author):

- LeanFinder: "Canonical reduction of coefficients commuting with inverse image
  in four derived proper base change objects" returned eight Over/pullback and
  morphism-property declarations; none defines these four derived objects.
- Loogle: `"baseChange", "tensor"` returned twelve ordinary module tensor/base-change
  declarations, including `TensorProduct.AlgebraTensorModule.distribBaseChange`;
  none is the ringed-site coefficient comparison or four-object assembly.
- LeanSearch: "Four finite coefficient derived objects in proper base change after
  derived reduction modulo ideal powers" returned Internal Server Error. Recorded
  as unavailable, not a successful negative search.
- `rg -i 'four.?corners|finite.?level.?corners|def-weil-pbc-four-corners'` across
  Mathlib, upstream WeilConjectures and shared Sheaf found only an unrelated affine
  coefficient-intersection comment. Additional searches for pullback/changeOfRings
  and pullback/restrictScalars found the existing etale restriction comparison;
  its site and constant coefficients differ from the present completed pro-etale
  tower. Searching the 51-module pro-etale framework found no four-corner assembly.
  The existing coefficient, derived, adjunction and restriction declarations are
  reused; the new restriction/pullback helper is the projection-specific canonical
  comparison needed to state this node's transition equation.

Other repair: the docstring for `fourCornerChangeComplex` incorrectly called scalar
extension "exact"; it is now correctly described as additive. Scalar extension
need not be exact. Its definition and the derived scalar extension are unchanged.
All new helpers belong to this node and appear in `lean.declarations`, with source,
blueprint and complete proof docstrings for postponed theorems. No independent
notion, new DAG node, dependency module or statement correction was needed. The
main `lean.statement` remains verbatim equal to the existing definition signature.
There are no hollow definitions: each chosen comparison is uniquely characterized
by explicit normalization, and all postponed proofs remain named `sorry` theorems.

Validation: `scompile.py Q06 def-weil-pbc-four-corners` compiled the revised module
cleanly against current server sources, with no errors or warnings. The delivered
module took 9.0 seconds under the standard 60-second, nice-19, two-thread limit.
The local overlay's stale dependency artifacts were handled by the wrapper's server
confirmation; no library source, tool or resource limit was changed. All 27
module declarations are listed in the node, every line is at most 100 characters,
and the main signature was checked verbatim against `lean.statement`.
