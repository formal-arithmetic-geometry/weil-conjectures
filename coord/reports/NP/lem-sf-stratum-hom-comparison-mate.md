## Worker report

The module `Sheaf.AlgebraicGeometry.StratumHomComparisonMate` states
`AlgebraicGeometry.StratumHomComparisonMate.stratumHomComparisonMate` with one `sorry`.
No theorem is proved. All helper definitions have concrete data, built from the recorded
functors, canonical comparison maps, adjunctions, and exact-derived compatibility isomorphisms.
There are no new nodes, dependency repairs, or changes to the mathematical statement.

I read the latest blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`,
second paragraph, together with its statement file. The older source path in the node is
historical; the current paragraph has the same stratum reduction and requires equality with
the specified internal-Hom map. The 7-step theorem docstring carries the node's complete
argument: bounded-below applicability, normalized representable Hom bijections, etale evaluation,
ordinary mate transposition, projection and exceptional-counit squares, injectivity of the
tensor transpose, and cancellation to get invertibility.

Hypotheses and clauses, using the namespace `AlgebraicGeometry.StratumHomComparisonMate`:

| Node text | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field k | `D : WeilConjectures.FiniteFieldDatum.{u}`, with base `Spec (.of D.k)` |
| Prime ell different from char k | `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p` |
| Finite extension E/Q_ell | `E : Type (u + 1)`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]` |
| Ring of integers, chosen uniformizer, positive level, A | Existing `Padic.coefficientExtensionRing l E (n + 1)`; every positive level is a successor. Its `Finite` proof is supplied explicitly by `Padic.finite_coefficientExtensionRing`; no finiteness hypothesis is added |
| Separated finite-type k-schemes S and X | `aS`, `aX` and the three instance binders `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on each |
| Locally closed k-immersion and its closed/open factorization | `c : S ⟶ V`, `v : V ⟶ X`, `[IsClosedImmersion c]`, `[IsOpenImmersion v]`, and `_hs : (c ≫ v) ≫ aX = aS`; V carries the induced map `v ≫ aX` |
| Ordinary constant-A categories on e and p | `Etale.D` and `ProEtale.D` are transparent abbreviations of `DerivedCategory (Sheaf topology (ModuleCat.{u+1} A))`. This is the published fixed-scalar presentation of constant-ring modules, used by the comparison, exceptional-adjoint and projection dependencies |
| C_T = nu_T^* | Existing `ImmersionProjectionComparison.comparison A T`, the exact `comparisonUpperStar` induced on derived categories |
| H_tau = RHom, tensor | `Etale.hom`, `ProEtale.hom`, and `tensor` abbreviate the existing `derivedHom` and K-flat `derivedTensor`; no second construction |
| Q_tau = v_! c_* and J_tau = Rc! v* | Existing `locallyClosedEtaleExtension`, `locallyClosedProEtaleExtension` and `z.adjoints.etaleRight v`, `z.adjoints.proetaleRight v` |
| Ambient adjoints and pasted exceptional counits | `z : LocallyClosedExceptionalComparison A c v`; `Etale.Normalized` and `ProEtale.Normalized` end in the actual `(z.adjoints.etalePasted v).counit` and proetale pasted counit |
| L locally constant finite | `L : Sheaf S.smallEtaleTopology (ModuleCat.{u+1} A)` and `Scheme.IsFiniteLocallyConstantSheaf L` in `Conclusion`. Finitely generated values over this finite A are finite modules |
| L has flat geometric stalks | The full `∀ Ω [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S), Module.Flat A (...)` clause, using `Scheme.pointSmallEtale s` and its `ulift.sheafFiber` |
| L as a derived object | Existing `ImmersionProjectionComparison.single A L`, namely the degree-zero single functor |
| M bounded constructible | `M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X` |
| N = J_e M bounded constructible | `Etale.DerivedCategory.isBoundedConstructible A S ((z.adjoints.etaleRight v).obj M.obj)` |
| Canonical Delta and gamma | `extensionComparison` transports the recorded exact closed-mate/open-unit comparison through `extensionIso`; `z.gamma` is the recorded counit-compatible exceptional comparison |
| Specified b_s | `directImageMate A (c ≫ v) ⟨_, hK⟩` uses literally `fixedComparisonDirectImageMatePlus.app`, included by `DerivedCategory.Plus.ι.map`, and conjugated by the published exact/derived D+ compatibility maps. It is not an arbitrarily chosen isomorphism |
| b_s applicable to H_e(L,N) | The existential proof `hK : DerivedCategory.TStructure.t.plus (Etale.hom ... L N)` is supplied in the conclusion, not assumed. Its proof is the lower-bound argument in the node |
| Canonical natural chi_e and chi_p | `χe : Etale.HomIso ...`, `χp : ProEtale.HomIso ...` are natural isomorphisms of the two-variable bifunctors on the full unbounded categories |
| Inverse transpose of chi | `Etale.Normalized` / `ProEtale.Normalized`, universally in P and B: tensor of `χ.inv.app` with identity, then right-ordered evaluation, equals `projection`, then Q of ordinary counit tensor identity, then Q of evaluation, then the pasted exceptional counit |
| Canonical tensor identifications | `projection` is the dependency's canonical arrow transported through `extensionIso`. `ordinaryAdjunction` transports the actual ordinary derived adjunction through `leftDerivedUpperStarComp` and the exact-pullback comparisons. `evaluation` inserts the existing signed symmetry before tensor-Hom evaluation |
| Beta | The original `AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom`, without any isomorphism assumption |
| H_p(Delta^-1,1) | `homChange`: contravariant `derivedHom.map` of `extensionComparison.inv.op`, evaluated at C_X M |
| H_p(1,gamma) beta_(L,N) | `stratumMap`: beta followed by covariant Hom of `z.gamma.hom.app M` |
| Displayed equality in D(X_p,A) | First conjunct of `IdentityAndIsomorphisms`, in Lean composition order: beta_(Q L,M) then `homChange` then `χp.hom.app` equals C_X of `χe.hom.app`, then `directImageMate`, then Rs_p of `stratumMap` |
| Every displayed arrow invertible if beta_(L,N) is | Second conjunct of `IdentityAndIsomorphisms`: the antecedent is exactly `IsIso beta_(L,N)`; the conclusion lists beta_(Q L,M), Hom(Delta^-1,1), chi_p, C_X(chi_e), b_s, the stratum map, and its ordinary direct image |
| Only ambient closed adjoints | The only exceptional functors used are `z.adjoints.etale`, `z.adjoints.proetale`, their open-restriction composites, and their pasted adjunctions. No constructible exceptional adjoint, biduality, or comparison-isomorphism assumption for beta is introduced |

The outer existential proofs `hX : IsNoetherian X` and `hqc : QuasiCompact (c ≫ v)`
are established conclusions needed to instantiate the recorded interfaces, not extra assumptions.
The theorem asserts `Conclusion` at the actual p-adic coefficient ring, with its proved
finiteness instance. The generic helpers do not assert this conclusion for other coefficient
rings. Within `Conclusion`, normalized chi maps are existentially supplied together with their
normalizations, rather than accepted as unexplained arbitrary maps or assumed to exist.
Their normalization at all P,B determines the maps uniquely by tensor transposition.

Dependency declarations read and used (the listed node modules are public imports):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`; the construction and quotient are read in `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `def-weil-scheme-morphism-properties`: convention-only record; it defines no separate declaration. The named Mathlib properties are used directly.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategoryModule`, read also at its defining public source `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`; the helpers expand this same category.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `FiniteCoefficientModules`, `finiteCoefficientRealization`, `finiteCoefficientDerivedComparison`. Its published exact realization identifies the fixed-scalar presentation used consistently here and by the exceptional-comparison dependency.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, whose left functor is the comparisonUpperStar used here.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`, retaining its public generic ringed-site definition; its recorded `AlgebraicGeometry.Etale.derivedHom` and `derivedTensorHomAdjunction` are used on sheaf categories. The ordinary-module-only abbreviation is not applied to a sheaf object.
- `lem-weil-finite-duality-locally-closed-comparison`: `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison`, `LocallyClosedComparisonAdjoints`, `locallyClosedEtaleExtension`, `locallyClosedProEtaleExtension`, `etaleRight`, `proetaleRight`, `etalePasted`, `proetalePasted`, and `LocallyClosedExceptionalComparison` with its gamma and counit equation.
- `def-weil-pbc-constructible-complexes`: `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`, `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` and `BoundedConstructibleDerivedCategory`.
- `lem-weil-pbc-comparison-direct-image-canonical-mate`: `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`, `fixedComparisonDirectImageMatePlus`, read with its full endpoints, construction, invertibility and counit specification.
- `lem-weil-stratum-ambient-hom`: `Sheaf.Paper.StratumAmbientHom`, the two `nonempty_stratumAmbientHomIso` declarations. This item adds the specific normalization to the unnormalized natural isomorphisms, and uses the same ordinary functors and fixed-scalar presentation already used by its other dependencies.
- `def-sf-evaluation-hom-site-comparison`: `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison`, `siteComparisonEvaluationHom`, the evaluation transpose through the canonical tensor identification.
- `lem-sf-immersion-projection-site-comparison`: `Sheaf.AlgebraicGeometry.ImmersionProjectionSiteComparison`, its two `projection` maps, canonical `extensionComparison`, `comparison`, `single`, and tensor `symmetry`.

Recorded proof dependencies are imported without `public` when not already statement
dependencies: `BoundedAboveRHomHyperExt`, `RingedDerivedClosedSymmetricMonoidal`,
`RingedDerivedMonoidalComparisons`, `ProjectionMateExact`. The Noetherian finite-type
Mathlib declarations are already public through the statement imports. No proof import
introduces a cycle. The source's current CompactObject example is withdrawn and empty;
the delivered module uses the required module header and public-section conventions.

Searches before writing:

- `msearch.py ... leanfinder "Stratum derived internal Hom etale proetale site comparison equals evaluation comparison counit mate"`: 8 hits, including `LightCondensed.ihomPoints_symm_comp`, the locally constant counit lemmas, and `Condensed.profiniteSolidCounit`; none states the two-site stratum composite identity.
- `msearch.py ... leansearch "The derived internal Hom comparison for a locally closed immersion agrees with evaluation under the stratum adjunction"`: 8 hits, including `CategoryTheory.ihom.ihom_adjunction_counit`, `CategoryTheory.ihom.ev`, and `Scheme.Modules.restrictAdjunction_counit_app_app`; these give generic evaluation/adjunction APIs, not the node's statement.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.conjugateEquiv"`: 12 hits, including `conjugateEquiv`, `conjugateIsoEquiv_apply_hom`, and mate identities; generic transport only.
- `msearch.py ... grep "stratum.*[Hh]om|[Hh]om.*stratum"`: only a Hahn-series comment in Mathlib, no match.
- `rg -n 'stratum.*[Hh]om|[Hh]om.*stratum|immersionInternalHomIso|stratumHomComparison' lean/WeilConjectures lean/Sheaf`: found the existing unnormalized `StratumAmbientHom`, normalized single-site `EtaleGenericStratumMate`, intrinsic proetale `StratumAmbientProjectionData`, and unrelated stratum results. None states this etale/proetale comparison equation. The single-site construction was read to check the evaluation orientation.
- Search for `lem-sf-stratum-hom-comparison-mate` under `lean/WeilConjectures`: no declaration or reference.
- Search for the new namespace and theorem name in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Edge cases checked before writing: L = 0 and M = 0 are allowed; no nonzero or positive-rank
hypothesis occurs. Empty S or X is allowed, as are identity closed/open factors. The
normalization is expressed through functorial identities and actual counits, so includes
these cases. The coefficient index n = 0 represents the first allowed level A_(E,1),
not the forbidden level zero. No finite Tor dimension on M or N, perfectness assumption
on arbitrary P in the natural isomorphisms, or boundedness assumption on those natural
isomorphisms has been added. The only beta isomorphism premise occurs in the conditional
conclusion. Site object universe u+1 and morphism universe u are retained; the coefficient
ring lies in u+1, consistently with all fixed-scalar dependencies. All variables and the
universe are bound explicitly; `autoImplicit false` is enabled.

Validation: scompile.py compiled the complete file in sandbox and library module modes
without errors or warnings (5.9 and 6.2 seconds before the final explicit dependency-import
list was expanded). The final dry run and delivery recheck the final module independently.

## Second reading by NP

This is the author's second pass; no independent reader was spawned, as the dispatcher
brief forbids starting agents and assigns independent review to the maintainer. I reopened
the node and delivered file. In particular I checked the direction of Delta^-1 under
contravariant Hom, the position of gamma after beta, the order of all three RHS factors,
the presence of every isomorphism conclusion, and the exact inverse-transpose normalization
at both sites. I checked that the natural chi types quantify over full unbounded categories,
that b_s is the actual recorded D+ mate transported into the ambient category, and that its
lower-bound witness is concluded rather than assumed. The canonical exact-closed extension
identifications and signed symmetries resolve the differing presentations without adding
an assumption. This pass added explicit public imports for each recorded statement-dependency
module; it found no mathematical mismatch or reason to correct the node.
