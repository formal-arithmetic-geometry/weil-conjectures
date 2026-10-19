## Worker report

Item: `lem-pur-coefficient-system-derived-comparison`. Module:
`Sheaf.Paper.CoefficientSystemDerivedComparison`; primary declaration:
`SheafOfModules.coefficientSystemDerivedComparison`.

The theorem has `sorry` as its entire proof. It asserts existence of the ordinary
geometric lifts and their universal derived images, together with every comparison
and the bounded-below descent conclusion. Its helper structures package those
conclusions; none is a new hypothesis. No functor, comparison, adjunction or
normalization hypothesis has been supplied by the caller in place of its construction.
There are no new nodes and no dependency modules in this delivery. The item's
statement and proof are unchanged. Two already-landed nodes are added to stmt_deps
because their declarations occur in the signature's expanded definitions:
`lem-pur-coefficient-evaluation-derived-left-adjoint` and
`def-weil-pbc-algebraic-inverse-image`.

Source checked: the local Zheng PDF, section 4, Construction 4.1 on printed page 21;
the paragraph immediately before Lemma 4.10 and equation (4.10.1) on printed page 23;
the following discussion on printed page 24. Zheng uses n>=0 and Lambda_n=O/(ell^(n+1));
the Lean dependency already uses precisely this indexing. The node's positive index
is therefore represented by n+1, including its smallest exponent 1.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Two topoi presented by small sites | `C`, `D`, `J`, `K`, with independently bound object and morphism universes and `EssentiallySmall.{w}`; the usual sheafification and sheaf-compose instances express availability of the recorded Mathlib module and constant-sheaf categories. No equality between site object and arrow universes is imposed. |
| Geometric morphism u^* left adjoint to u_* | `L`, `V`, `adj : L ⊣ V`, `[PreservesFiniteLimits L]`. These are set-sheaf functors, not arbitrary module/derived functors. |
| Commutative ring O | `O : Type w`, `[CommRing O]`. |
| Non-zero-divisor ell | `hregular : ∀ x : O, ell * x = 0 → x = 0`. |
| O complete for the powers of ell | `[IsAdicComplete (Ideal.span ({ell} : Set O)) O]`, the dependency's canonical completion convention. |
| A_n=O/(ell^n), constant on each topos | Existing `coefficientQuotientSheaf O ell n`, the sheafification of the constant quotient at exponent n+1. No replacement coefficient ring is introduced. |
| Strict module systems, semilinear successive transitions, compatible morphisms | Existing `CoefficientSystem`, its `level`, `transition`, `Hom.app`, `Hom.comm`, and category instance. No epimorphism or normalization is required of the transitions. |
| Restriction has its usual meaning | Existing `coefficientRestriction`, defined by Mathlib `SheafOfModules.restrictScalars` along `coefficientQuotientMap`. |
| Abelian systems, levelwise exactness and evaluation | Existing `coefficientSystemAbelian`, `coefficientEvaluation`, `coefficientEvaluation_exact` from the evaluation dependency. These are the same category used throughout. |
| Unbounded derived categories, standard cohomology | Mathlib `DerivedCategory` and its `HasDerivedCategory.{d}` size choices, on the actual system and module categories; `IsGE` is the standard cohomological t-structure. |
| Applying inverse image levelwise is exact | Conclusion `S : CoefficientSystemOrdinaryImage`: `lift n : AlgebraicInverseImage L A_n A_n` transports ring addition, multiplication, zero, one, module addition, zero and scalar multiplication through L; its natural underlying-sheaf isomorphism fixes maps. `constants` fixes the ring identification on every constant quotient coefficient. `inverseExact` and `systemExact` assert exactness. |
| Actual ordinary direct images and level adjunctions | `S.right`, `rightUnderlying`, `levelAdj`, `levelTranspose`. The last equation requires the module Hom transpose to be the given set-sheaf adjunction's transpose, so these are the geometric direct images with the induced coefficient action. |
| Actual levelwise system functors, including maps | `S.inverse`, `rightSystem`, the natural isomorphisms `inverseEvaluation` and `rightEvaluation`, `inverseTransition`, `systemAdj`, `systemTranspose`. Naturality of the evaluation isomorphisms identifies their action on every morphism. The system transpose is the level module transpose at every n. |
| Inverse image on derived systems is exact termwise inverse image | `CoefficientDerivedImage.inverse` and `inverseFactors` identify localization followed by this functor with termwise application of S.inverse followed by localization. Exactness is already asserted for S.inverse. |
| Total right derived image computed by K-injectives | `direct`, `directUnit`, `isRightDerived`, `computes`. The universal right-derived pair and invertibility on every K-injective complex specify the computation, not an arbitrary functor bearing a name. The same data at each level appear in `level n`. |
| Derived adjunction | `adjunction` and `transpose` in `CoefficientDerivedImage`. The transpose at a strict complex map is the ordinary complex transpose followed by the universal direct-image comparison. This normalizes both unit and counit. |
| Canonical evaluation/inverse-image comparison | `CoefficientSystemDerivedImage.inverseEvaluation`, normalized on every complex by `inverseEvaluation_rep` using the ordinary levelwise comparison and the localization factors. |
| Canonical evaluation/direct-image comparison | `directEvaluation`; `counit` and `unit` are the actual evaluated adjunction equations. The normalized inverse evaluation and the counit equation determine the direct-image comparison as the adjunction mate. |
| Compatibility with quotient maps | Ordinary `restrictInverse` is fixed on underlying sheaves by `restrictInverseUnderlying`. Derived `restrictedDirect` is fixed by `restrictedDirect_mate`, and `restrictedInverse` by `restrictedInverse_mate`. `inverseTransition` and `directTransition` impose the two actual transition squares for every pair n<=m. |
| Compatibility on objects and morphisms | All comparisons are natural isomorphisms of functors; the transition squares hold for every derived object. Naturality thus gives the squares for every system morphism, rather than mere objectwise isomorphisms. The evaluation dependency supplies identity/composition of the actual quotient transitions and their adjoint sigma maps. |
| Inverse image commutes with derived coefficient change | `tensor`, `tensor_unit`, `derivedTensor`, `derivedTensor_rep`. `tensor_unit` fixes the ordinary comparison on the scalar-extension unit, equivalently pure tensor generators. `derivedTensor_rep` identifies its derived value with the chain-level tensor comparison on flat-term K-flat representatives. The scalar functors are exactly `PY.scalar h` and `PX.scalar h` from the recorded derived change-of-rings interface. |
| Normalized means adjoint transitions invertible, all m>=n | `IsNormalizedCoefficientSystem` says that the inverse Hom-equivalence of `(P.scalar h).derivedAdj` sends the actual `(P.transition h).app M` to an isomorphism, for every `h : n ≤ m`. There is no arbitrary collection of transition isomorphisms. |
| Every level inverse image fully faithful on D+ | Premise of the `origin` field: `Function.Bijective ((level n).inverse.map : (A ⟶ B) → _)` for all A,B admitting lower bounds, and every n. This is precisely full faithfulness on the full bounded-below subcategory, without assuming full faithfulness on unbounded objects. |
| M uniformly bounded below as a derived system | `∃ a : ℤ, M.IsGE a` in `origin` and `boundedBelow`, on the derived system itself. It is not merely a collection of unrelated lower bounds at different n. |
| Every evaluation in the essential image of D+ inverse image | `∀ n, ∃ H, (∃ a, H.IsGE a) ∧ Nonempty ((level n).inverse.obj H ≅ (PX.evaluation n).obj M)` in `origin`. No compatible choice of individual lifts is assumed. |
| System counit is an isomorphism | `IsIso (system.adjunction.counit.app M)` in `origin`. |
| Ru_* M bounded below | The `boundedBelow` field asserts this for every bounded-below input, hence in particular for the M of `origin`. |
| Normalization preserved on these objects | Second conjunct of `origin`, using exactly `IsNormalizedCoefficientSystem` for PX and PY and `system.direct.obj M`. |
| Pro-etale/etale finite-coefficient instance | The theorem is universal in L,V,adj and sites. The imported `Scheme.proEtaleSiteComparison` supplies this geometric morphism and `ProEtale.siteComparison_boundedBelow` supplies its D+ full faithfulness for finite coefficients. No different special-case theorem or arbitrary comparison morphism is introduced. The node's last proof step identifies the constant-sheaf and finite-coefficient realizations; the final paragraph of the theorem docstring records this specialization. |

Dependency declarations read and reused:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  `sheafificationAdjunction`, `toSheafify` for the actual constant coefficient generators.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; its signature and underlying-presheaf construction
  were read in the pinned source.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; with the standard `IsGE` from TStructure.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, the acyclic-source null-homotopy predicate.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the coefficient dependency's `coefficientLevelModules` is transparently this category.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, reused through the
  evaluation package's actual universal scalar-extension pairs.
- `Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint`: the full module was read,
  including `coefficientQuotientSheaf`, `coefficientQuotientMap`, `coefficientRestriction`,
  `CoefficientSystem`, `coefficientEvaluation`, `coefficientTensor`, `coefficientTensorAdj`,
  `CoefficientEvaluationDerivedPackage`, and `coefficientEvaluationDerivedLeftAdjoint`.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`: publicly retains the
  `SheafOfModules.AlgebraicInverseImage` used here in the equal coefficient/module
  universe, with independent site object/morphism universes. All its graph equations
  and the generalized interface were read; no private copy is used.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparison`,
  `preservesFiniteLimits_proEtaleSiteComparison`, `proEtaleSiteComparisonModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`:
  `AlgebraicGeometry.ProEtale.siteComparison_boundedBelow` and its canonical
  `finiteCoefficientDerivedComparisonAdjunction`.

All recorded proof modules that are already stated are imported privately, including
K-injective existence, total derived functors, exact derived factorization, derived
adjunctions and their transpose normalization, K-flat pullback, canonical tensor
pullback, bounded-below injective resolutions and negative vanishing, direct-image
composition, Yoneda, and full faithfulness of degree-zero single embeddings. The
primary theorem's docstring gives the node's full construction and proof route.

Edge cases checked:

- Level 0 means exponent 1, so no smallest positive level is lost.
- Equal indices n=m are included in every quotient and transition quantifier;
  the canonical scalar unit and derived adjunctions supply the identity case.
- Arbitrary n<=m and triple compositions use the same actual coefficient quotients
  and the evaluation package's already fixed coherent transitions.
- No flatness of O/(ell^n) over O/(ell^m) is assumed. Derived tensor can be unbounded
  below. The normalization proof reflects vanishing of cohomology using faithfulness
  on sheaves, not a false boundedness assertion for those tensor products.
- M=0, zero transitions and nonnormalized systems are allowed in the main comparisons.
  Normalization is assumed only in the corresponding conditional conclusion.
- Zero rings and degenerate/empty topoi are not excluded. The regularity condition
  has its literal ring-theoretic meaning; constant-generator normalization uses
  sheafification rather than a nonempty-object assumption.
- No constructibility or finite generation of individual coefficient sheaves is imposed.
- Universe variables are explicitly bound. C and D need not have equal object/arrow
  universes, and the common coefficient/module universe may be larger than both sites.

Searches (all through prescribed msearch.py or read-only rg):

1. LeanFinder query `Derived direct image of inverse systems of sheaves of modules
   commutes with evaluation and inverse image`: 8 hits, principally ordinary
   `SheafOfModules.pushforwardComp`/`pushforward_assoc` and continuous-sheaf
   pushforward composition, no derived varying-coefficient system theorem.
2. LeanSearch query `Derived direct image commutes with evaluation on systems of
   sheaves of modules`: 8 hits, including `SheafOfModules.evaluation`,
   `evaluationPreservesLimit`, `PullbackConstruction.adjunction` and presheaf
   evaluation. These evaluate a site object, not the varying coefficient level.
3. Loogle `SheafOfModules, CategoryTheory.Adjunction, Functor.IsRightDerivedFunctor`:
   unknown last identifier, no hits; corrected query
   `CategoryTheory.Adjunction, SheafOfModules.restrictScalars`: 0 hits.
4. Mathlib grep `coefficientSystem|CoefficientSystem|evaluation.*rightDerived`: 0 hits.
5. `rg` in the prescribed upstream WeilConjectures tree and upstream name index for
   the item id, `CoefficientSystem`, and the proposed declaration names: no match.
6. `rg` in the project's Sheaf tree located the exact strict-system and evaluation
   package in `CoefficientEvaluationDerivedLeftAdjoint.lean`. Specialized adic
   `CoefDerivedSystemEvaluationCalculus` uses a DVR/scheme coefficient tower and
   does not give the generic geometric-morphism comparison here. No existing
   `CoefficientSystemDerivedComparison` module or declaration was found.

No statement correction or STATEMENT-DISPUTED flag. The existing stage-1 maintenance
note was read: it is resolved, and calls for keeping this statement and route.

Validation: scompile.py checked the sandbox and final-name module separately.
After disabling unused automatic injectivity/size-of-spec generation on the large
comparison record, both compiled cleanly (22.5 s and 45.4 s in the successful pass),
with the 60-second per-file limit unchanged. No global build or live source edit.

## Second reading by NV

Author's second pass against the full node and completed module; independent review
is the maintainer's delivery review, as specified in the dispatcher brief. No other
agent was started and this section does not claim an independent agent review.

Checked every row above against the actual fields. In particular, the theorem
constructs both evaluation packages and the geometric module functors; they are not
premises. Replaced a first draft of derived restricted-inverse coherence with an
explicit natural isomorphism normalized by the level-adjunction mate equation, then
used it in the inverse-transition square. Checked directions and intermediate
coefficient categories in both transition squares and in both unit/counit equations.
The compiler accepted these equalities. Removed an incorrect proof-plan sentence
suggesting boundedness of arbitrary derived coefficient tensor, replacing it with
the node's cohomological reflection argument. No mathematical statement changed.
