## Worker report

Item: `lem-trf-point-restriction-whole-roos-square`, stage 2, Q149.
Module: `Sheaf.Paper.PointRestrictionWholeRoosSquare`.
Main declaration: `WeilConjectures.PointRestrictionWholeRoos.point_restriction_whole_roos_square`.

The delivery states the actual whole-cone restriction square and its normalized localization.
There is one theorem, with proof `sorry`. Every helper has real data: `Ambient`, `Scalars`,
`Systems`, `U`, `F`, `T`, `TT`, and `G` abbreviate existing constructions; `left` and `right`
compose the existing canonical cone-coordinate isomorphism with the corresponding product
projection. No new coefficient category, inverse image, system transport, Roos cone or derived
limit is constructed. No dependency is repaired, and no statement is corrected.

The previous dispatch report concerned stage 1. The live item has Q73's reviewed seven-step
split and no `lean` binding; this is the requested stage-2 statement. There is no released
stage-2 repair note for this item. The downstream parent has the larger
`PointSystemRoosTransport` interface, but its theorem also asserts the ambient realization
and sections/limit comparisons: it is not an exact existing match for this node, and is not
imported as a premise of the child that its proof uses.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Finite field, its algebraic closure, geometric Frobenius | `D : FiniteFieldDatum.{t}` and `PointSystemTransport.pointPower D r`; the latter is built from `frobeniusPointIso`, which is Spec of geometric field Frobenius. |
| Prime different from the characteristic | `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`. |
| Finite extension of the l-adics, valuation ring and all positive quotient levels | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`; the existing quotient system uses `Padic.coefficientExtensionIdeal l E (n+1)`. No choice of uniformizer enters the square; these ideals are the recorded powers defining the quotients. |
| Small pro-etale site, completed coefficient sheaf, constant R action | `Ambient D l E` is `SheafOfModules` of `pointRestrictionRing ... none`, which is the completed sheaf, and `T` is the existing `pointRestrictionSections` on complexes. `Scalars` is the canonical common-universe ULift of the valuation ring. This does not replace the completed sheaf by the discrete constant sheaf. |
| Strict systems with quotient-linear transitions and ordinary unbounded derived category | `Systems` is `coefficientSequenceModules`; the strict maps live in `CochainComplex (Systems D l E) ℤ`, and `derivedTransport` is in the localization of that entire category. There is no normalized-system or boundedness hypothesis. |
| U_s, G_r, and X=U_s M, Y=U_s G_r M | `U` is the recorded `coefficientSequenceRestriction` on complexes, `G` the recorded system pullback on complexes, and the objects are `(U ...).obj M` and `(U ...).obj ((G ... r).obj M)`. |
| r at least one | `r : ℕ`, `hr : 1 ≤ r`. |
| H(V), its signs and both product coordinates | Existing `CategoryTheory.roosF`, `roosU`, `roosPmap`, and `roosχ`. At degree `p+1`, `roosχ V p` orders the summands as `P^p ⊞ P^(p+1)`. Hence the differential is exactly `(-db-(1-s)a,da)`, and the shifted coordinate is first. No signed-coordinate variant is substituted. |
| Ambient R-linear restriction σ on every unbounded completed-module complex | The existential natural transformation `σ` is between the actual module sections functors. Its sectionwise equality is literally `σ.app N x = pointRestrictionRaw ... N x`. `NatTrans.mapHomologicalComplex σ` gives the chain map; its scalar linearity is in the morphism type `ModuleCat`. |
| Localization on all ambient complexes, including realizations without completeness | The existential functors `A`, `B`, their natural factorization isomorphisms `eA`, `eB`, and `τ : A ⟶ B`, with the representative equation for every `K : CochainComplex (Ambient ...) ℤ`. No completeness, constructibility, boundedness, K-flatness or K-injectivity of K is assumed. |
| Actual strict u and its localization I | `PointSystemTransport.chainTransport ... hl r hr` and `PointSystemTransport.derivedTransport ... hl r hr`, respectively. `HasRestrictionComponents ... chainTransport` explicitly asserts its actual site-restriction values, retaining transitions. The dependency's finite-comparison normalization uses exactly `inverseImageFiniteComparisonComplex` and its tensor-unit insertion j; no replacement finite map is supplied. |
| Canonical κ^T on X and Y | `κT` is a natural isomorphism on all ambient tower complexes. Its two projection equations identify each coordinate with `pointRestrictionSections.map (left/right V p n)`. They fix the same product comparison on both summands, and apply in particular to X and Y. |
| Canonical κ^F with scalar transport | `κF` is a natural isomorphism on strict system complexes. Its two sectionwise `HEq` projection equations are the actual F-image of `left/right` on X. Here `HEq` identifies only the carriers from the already fixed coefficient restriction; it imposes equality of the whole section maps, not a comparison chosen independently at each derived level. |
| (1-s')P=P(1-s) | The conjunct `roosU (complexSections.obj M) ≫ roosPmap u = roosPmap u ≫ roosU (transportedComplexSections.obj M)`; Lean composition is left-to-right. |
| H(u)(b,a)=(Pb,Pa) | The conjunct involving `(roosF.map u).f (p+1)` and `biprod.map ((roosPmap u).f p) ((roosPmap u).f (p+1))`, conjugated by the fixed `roosχ` coordinates. There is no off-diagonal entry. |
| Entire actual restriction square | `roosF.map u ≫ κT.inv.app Y = κT.inv.app X ≫ (NatTrans.mapHomologicalComplex σ ...).app (roosF.obj X) ≫ T.map (κF.hom.app M)`. Both sides have domain `H(T^Tow X)` and codomain `T H(Y)`. |
| Both coordinates restrict each x_n along h^r | The explicit `HasRestrictionComponents` conjunct supplies the literal restriction formula at every integer degree and level. The preceding diagonal formula applies it separately in degrees p and p+1, while the two κ projection laws identify the product coordinates. Thus both coordinates, including the shifted one, have the same actual restriction formula. |
| Normalized total-limit identifications η | The existential natural isomorphism `η : Q ⋙ CoefTower.totalLimit Scalars ≅ roosF ⋙ Q`. Its equation against `rightDerivedFunctorUnitQ` fixes its value on the canonical ordinary-limit inclusion `limit.isoLimitCone.inv ≫ roosι V`. The isomorphism changes only termwise-limit presentation. The existing `roosι` has coordinates `(0,(π_n z)_n)`, precisely the stated augmentation. |
| η_Y Rlim(I)=H(u)η_X | The last conjunct applies `CoefTower.totalLimit` to the actual `derivedTransport` component and includes the two exact-functor localization factor maps. Its right side is `η_X ≫ Q.map (roosF.map u)`. It uses the whole derived-system morphism I, not independently specified levelwise morphisms. |
| Naturality, inverted quasi-isomorphisms, independence of representatives | σ, κT, κF, η, τ and the existing chainTransport/derivedTransport are natural transformations or natural isomorphisms. Two explicit conjuncts assert that `roosF.map` preserves quasi-isomorphisms for all ambient and scalar towers. Exact sections and inverse image preserve quasi-isomorphisms by their dependency statements. The chain square therefore localizes; naturality applies to inverses of quasi-isomorphisms and zigzags. The η unit equation fixes the normalized representative comparison, so it is independent of the chosen resolution. |

The theorem uses independent site universe `t` and coefficient-field universe `u`; the module
universe is `max u (t+1)`. The overly specialized imported `pointReductionModuleDerived`
instance is disabled for this file, as in the existing whole-system interface. This does
not impose any equality of universes or change the chosen derived categories. Marking the
existing `roosF` irreducible during elaboration avoids repeatedly expanding its cone and
product constructions. A scoped heartbeat allowance is used; the 60-second time limit is
unchanged. The final module compiled in both modes in 12.0 and 15.5 seconds.

### Dependency declarations read and used

All original `stmt_deps` and their records were read. The concrete sources used here are:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`: `WeilConjectures.TraceFormulaCoefficientConventions`, its finite-field and coefficient data. The square only needs those coefficient parameters, not the auxiliary finite-type scheme of the trace-formula convention record.
- `Sheaf.SixFunctors.SchemeFrobenius`: `FiniteFieldDatum.geometricGaloisFrobenius`; its point version is the recorded `frobeniusPointIso` below, as used by `PointSystemTransport.pointPower`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: `integralConstantToCompletionOfUniverses` and the actual completed and finite coefficient sheaves publicly exposed by it.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearSections.SemilinearDerivedSectionsData`, `semilinearDerivedSections`; the concrete quotient-linear system category is its recorded ringed-sequence-site implementation.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`: `CoefficientDerivedSystemCalculus`, `coefficientDerivedSystemEvaluationCalculus`; its completed-system interpretation is reused through the recorded concrete restriction/realization and point-system interfaces, rather than chosen from its existential theorem.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`: `isoSectionwiseInverseImage_equivalence`, `isoSectionwiseModuleInverseImage`, `isoSectionwiseModuleInverseImage_exact`; these specify reindexing and transported actions.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` and its public dependency `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`: `inverseImagePullbackComparisonDerived`, `inverseImageFiniteCoefficientMap`, `inverseImageCompletedCoefficientMap`, `inverseImageFiniteComparisonComplex`.
- `Sheaf.Paper.CoefTowerCoaugmentation`: `CoefTower.totalLimit`, the actual right derived ordinary inverse limit on module towers; its scalar/category universes are those of the common lifted valuation ring.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `pointModuleSections`, `point_proEtale_sections_exact`; its constant-scalar version is the existing `pointRestrictionSections`.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `strictRoosComparison`, with normalized augmentation and naturality on the entire ordinary derived tower category.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`: `ringedStrictTowerHomotopyLimitIndependentCoefficients`, retaining different site-object and site-morphism universes.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`, `frobeniusPointRestriction`, the prescribed point inverse-image transport recipe.
- `Sheaf.Paper.PointAutomorphismRestrictionNatural`: `pointRestrictionScalars`, `pointRestrictionRing`, `pointRestrictionSections`, `pointRestrictionInverseImage`, `pointRestrictionRaw`, `point_automorphism_restriction_natural`.
- `Sheaf.Paper.PointSystemTransportDescent`: `pointPower`, `pull`, `complexSections`, `transportedComplexSections`, `chainTransport`, `HasRestrictionComponents`, `derivedTransport`, `point_system_transport_descent`; the finite `finiteComparison_inverse` and `finite_evaluation` clauses fix its j normalization.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`: `exactProductFunctorStrictLimit`, supplying the canonical projection-normalized comparisons; its signed coordinates `(x,y)` are converted by `(x,y)=(a,-b)` in the proof plan.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosχ`, `roosU`, `roosPmap`, `roosι`. Its already landed node `def-weil-strict-roos-model` is added to `stmt_deps`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`: `coefficientSequenceModules`, `coefficientSequenceRestriction` and its exactness; its already landed node `def-coef-ringed-sequence-site` is added to `stmt_deps`.
- Proof inputs: `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`, `ProEt.countableProducts_exact`; Mathlib's `CategoryTheory.Localization.lift`, `liftNatTrans` and `natTrans_ext` (the localization node's actual Mathlib match, not a missing lean record).
- Upstream `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`: `Functor.rightDerivedFunctorUnitQ`, the actual universal derived unit with its complex-level Q factor maps. Mathlib supplies `limit.isoLimitCone`, `HomologicalComplex.coneOfHasLimitEval`, and `isLimitConeOfHasLimitEval` for the canonical change of ordinary-limit presentation.

The two added `stmt_deps` are existing landed nodes, as explicitly permitted by the
parallel-landing brief. Their records and all other node fields remain unchanged. No new
nodes and no dependency modules are delivered. The eventual proof-import of this module
into its parent is for the maintainer; no upstream or shared source was edited.

### Source and edge cases

Read the current main-20261015 integral-model proof, especially (3): integral maps are
constructed as derived limits of compatible levelwise maps before rationalization. Read
the local Stacks `sites-cohomology.tex`, `lemma-derived-limit-is-ok` (Tag 0941), including
the simultaneous K-injective tower calculation. The detailed whole-cone normalization
is the existing DAG refinement, not a claim that Stacks prints this Frobenius square.

Checked by hand: zero system, zero transitions (1-s is the identity, the Roos cone is
contractible), constant towers and their zero shifted-coordinate augmentation, arbitrary
nonzero differentials with the stated negative shifted sign, r=1, and the identity
point automorphism. The strict calculations apply equally to unbounded complexes and
non-normalized systems; there is no derived-completeness or surjectivity assumption.
The smallest level n=0 denotes the first quotient R/varpi, never exponent zero. There
is no empty tower-index case: the index is the given positive countable tower.

### Searches

Fresh searches are logged in sandbox `searches.jsonl` by `msearch.py`:

- LeanFinder: “Point restriction on the whole strict Roos cone commutes with diagonal products and the normalized derived inverse limit comparison”. Eight hits (LightProfinite/Profinite cones, generic sequential-product cone identities); none states this square.
- Loogle: `CategoryTheory.towerTransitionEndomorphism, CochainComplex.mappingCone`. No hits: towerTransitionEndomorphism is an upstream project declaration, not a Mathlib identifier in the search index.
- Mathlib grep: `roos|Roos` in `Algebra/Homology`, and `point.*restriction.*[Rr]oos|whole.*[Rr]oos` in Mathlib. Both zero hits.
- LeanSearch: “Naturality of restriction on both coordinates of a strict Roos homotopy inverse limit cone”. Eight hits: generic IsLimit naturality, limit.isoLimitCone projection formulas, cone-point isomorphisms, and PresheafOfModules.limitCone. Useful universal-property ingredients, no exact match.
- Repository `rg` searches for `whole.roos|wholeRoos|pointRestriction.*[Rr]oos|point_restriction_whole` and `point.*restriction.*[Rr]oos|whole.*[Rr]oos` in both `lean/WeilConjectures` and `lean/Sheaf`; exact item-id grep in `lean/WeilConjectures`. No upstream attachment. Existing `StrictRoosModel` is reused. The larger downstream `PointSystemRoosTransport` and the bounded/completed-input `PointSectionsCompletionCone` are not exact matches for this node.

## Second reading by Q149

A second author pass was made with the live node, all seven proof steps, and the final
module open. No independent agent was started: the dispatcher explicitly forbids it, and
the maintainer performs the independent review.

I checked the three displayed equations in composition order and verified both domains
of the restriction square are `H(T^Tow X) -> T H(Y)`. `left` is the p coordinate in degree
p+1, so the shifted summand is present. `biprod.map` has exactly the two P components;
the κ projection equations determine both, so no off-diagonal term can be hidden. The
scalar action uses the completed coefficient structure transported by the canonical
coefficient inverse, not a discrete integral coefficient sheaf.

This pass added the explicit `HasRestrictionComponents` conjunct and both Roos
quasi-isomorphism-preservation clauses. It also replaced a raw `Q.map u` formulation
of the final identity by the actual localized `derivedTransport` with its two
canonical exact-functor factor maps, and added the ambient σ localization equation.
The normalization equation uses the universal complex-level derived unit rather
than a homotopy-category unit with silently identified endpoints. The ordinary
limit change is the canonical `limit.isoLimitCone` from the termwise limit cone.

No hypothesis was silently added to M or K. No statement dispute or correction was
found. All theorem proofs are exactly `by sorry`, helpers contain no postponed data,
and `autoImplicit` is false. Validation: prescribed scompile.py, sandbox and actual
module modes, no errors or warnings; the final additions are included in that check.
