## Worker report

The module `Sheaf.Paper.RingedSliceComparisonsShift` states
`SheafOfModules.ringedSliceComparisonsShift`, with one postponed theorem proof.
Its statement is the conjunction of shift compatibility for the specified direct-image
comparison, its adjunction mate in the stated orientation, and the two input squares
for tensor restriction on each of the two sites. The natural-language node is unchanged.

The auxiliary declarations belong to this same statement: they expose the inherited
restriction shift, the adjunct of the specified coefficient isomorphism, and predicates
spelling out its tensor-shift normalization and compatibility equations. They introduce
no new tensor, module category, derived category, restriction, or arbitrary comparison.
All auxiliary data have actual definitions. Only the main theorem contains `sorry`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
|---|---|
| Small sites C,D | `{C D : Type u} [SmallCategory C] [SmallCategory D]`, with topologies `J,K`; the same small-site presentation used by the recorded derived-slice API. |
| Continuous u:D→C | `(u : D ⥤ C) [u.IsContinuous K J]`. |
| Inverse image preserves finite limits | `[PreservesFiniteLimits (u.sheafPullback (Type u) K J)]`. |
| Commutative ring sheaves R,S | `{R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}`. |
| Specified isomorphism f⁻¹R≅S | `(c : (u.sheafPullback CommRingCat.{u} K J).obj R ≅ S)`. `ringedSliceShiftStructuralMap u c` is exactly its image under the existing ring-sheaf adjunction, so the module structure map is fixed. |
| V and U=u(V) | `(V : D)` and the expression `u.obj V`. |
| Localized ringed morphism f_V | `Over.post (X := V) u` and `localizedRingedSiteMap u (ringedSliceShiftStructuralMap u c) V`. Its continuity instance is a presentation prerequisite for that existing declaration, supplied by `localize_ringed_site_morphism_general`; it adds no geometric assumption. |
| Restricted rings | `R.over V`, `S.over (u.obj V)`, with underlying ring sheaves `localCoefficientRings`; the latter is the existing forget-commutativity abbreviation. |
| Ordinary unbounded derived categories of module sheaves | Four `HasDerivedCategory.{w}` binders for the two module-sheaf categories and their slices. `RingedSliceDerivedImage` and `ringedSiteDerived` use precisely `DerivedCategory (SheafOfModules ...)`; there is no boundedness or completion. |
| Canonical global and local derived adjunctions | The two inputs `e,l : RingedSliceDerivedImage ...` retain actual module pullback/pushforward, both universal derived transformations, the derived universal properties, and the normalized Hom bijection for their adjunctions. These are presentations of the specified functors, not arbitrary left/right functors. |
| Canonical β and adjunction-compatible θ | `d : RingedSliceAdjunctionSquare e.adjunction l.adjunction ...` supplies `d.beta` and `d.lambda`. The latter has source `j_V^* ⋙ Lf_V^*` and target `Lf^* ⋙ j_U^*`, exactly θ's orientation in the node. Its unit/counit fields fix it as the mate of β. |
| Canonical normalization of β | `_normalized` is the all-complex right-derived-unit square from the recorded slice-localization theorem. It uses `ringedSlicePushforwardComplexIso`, the identity on sections, between the two ordinary routes. Thus an arbitrarily rescaled β is excluded. The whole equation, including both restriction factorization maps, is retained. |
| Resolution shifts for derived pullback and pushforward | The four `CommShift ℤ` inputs are constrained by `NatTrans.CommShift` for `e.epsilon`, `e.eta`, `l.epsilon`, `l.eta`. These are the canonical resolution-shift normalization: shifting before or after the universal comparison gives the same map. They are the complex-level form of the universal-transformation normalization in `derivedAdjunctionShiftCompatible`. |
| β commutes with every integer shift | First conjunct, `NatTrans.CommShift d.beta.hom ℤ`. Its defining equation is `c_(E[n]) ≫ s_G = s_F ≫ c_E[n]` in Lean composition order. |
| θ commutes with every integer shift | Second conjunct, `NatTrans.CommShift d.lambda.hom ℤ`, with the actual composite functor shifts, so both restriction shift maps are included. |
| Tensor comparison τ for j_V^* | Third conjunct `RingedSliceTensorShiftCompatibility K R V`. |
| Corresponding tensor comparison for j_U^* | Fourth conjunct `RingedSliceTensorShiftCompatibility J S (u.obj V)`. |
| Canonical tensor comparison, natural in both variables | In the compatibility predicate, `d : RingedSliceEvaluationComparisons ...` supplies `d.rho`; `_hd : RingedSliceTensorModel ... d` fixes it on every flat-term K-flat pair by the existing pure-tensor representative square. Its simultaneous naturality is a field of the existing comparison structure. |
| Canonical tensor shifts | `RingedSliceTensorShiftNormalized` fixes the `CommShift₂Int` structures relative to the existing `CoefficientTensorModels.iso`, the actual `DerivedCategory.Q.commShiftIso`, and chain isomorphisms determined on all sheafified pure-tensor generators. The predicate is required for both the original site and its slice, so tensor shifts cannot be chosen independently with another sign. |
| `(K[n])^r=K^(r+n)` and differential `(-1)^n d` | The existing `CochainComplex` and `DerivedCategory` integer shifts, written `⟦n⟧`, use this convention; normalization compares with their actual localization isomorphisms. |
| First-input shift is identity on summands | In the first half of `RingedSliceTensorShiftNormalized`, `γ.hom.f k` sends the generator with degrees `(p,q)` in `(P[n],Q)` to the same generator in `(P,Q)` at `(p+n,q)`, without a scalar. |
| Second-input shift has sign `(-1)^(np)` | The second half sends the generator at `(p,q)` in `(P,Q[n])` to `(p*n).negOnePow •` the generator at `(p,q+n)`. Integer multiplication is commutative, so this is precisely the node's `(-1)^(np)`. |
| Equation in each input with the other fixed | The conclusion inside `RingedSliceTensorShiftCompatibility` is `∀ M N n`, followed by a conjunction of the first-input and second-input equations. Each equation uses `rho` at the shifted pair, the tensor of the restriction shifts, and the target tensor shift on one side; the other side is restriction of the source tensor shift, the restriction shift on its output, then the shift of `rho` at `(M,N)`. |

The tensor predicate quantifies over presentations of the existing tensor and their
normalized shifts, rather than selecting an unnormalized isomorphism with choice.
The representative comparisons and naturality fix these shifts on arbitrary derived
objects: every object is represented up to isomorphism by a K-flat complex. The
existential chain isomorphisms in the normalization are characterized on every summand
and every local pure tensor, hence determine unique chain maps. They are not a bare
`Nonempty` choice of derived comparison.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; sites here use its existing
  associated Grothendieck-topology presentation, with no extra covering-index axiom.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`, `overFunctorMap`;
  the existing slice constructions are reused through the recorded restriction API.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`:
  `localizedRingedSiteMap`, `ringedSiteModuleMap`,
  `localize_ringed_site_morphism_general`.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent alias of `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.RingedDerivedSliceLocalization`, and its public
  `Sheaf.Paper.RingedDerivedSliceData`:
  `ringedDerivedSliceLocalization`, `RingedSliceDerivedImage`,
  `RingedSliceAdjunctionSquare`, `ringedSliceRestriction`,
  `ringedSliceRestrictionFactors`, `ringedSlicePushforwardComplexIso`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its canonical K-flat representative characterization agrees with the slice
  specialization `RingedSliceTensorModel` used in the statement.
- `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`, `mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso`,
  and their summand formulas, which establish the source's tensor-shift convention.
- `Sheaf.Paper.DerivedAdjunctionShift`:
  `CategoryTheory.derivedAdjunctionShiftCompatible`, including its
  universal-transformation shift normalization and unit/counit compatibility.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `ringedOverFunctor_exactGeneral`, `ringedDerivedRestrictionGeneral`.
  The delivered instance exposes the existing `mapDerivedCategory.CommShift` data;
  it constructs no new shift isomorphism and postpones no proof.
- The existing representative API in
  `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose` and its public
  `RingedSliceEvaluationModels`, and
  `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `RingedSliceEvaluationComparisons`, `RingedSliceTensorModel`,
  `ringedSliceComplexRestriction`, `ringedSliceDerivedRestriction`,
  `CoefficientClosedStructure`, `CoefficientTensorModels`,
  `coefficientTotalTensor`, `coefficientTensorGenerator`.

All stated proof dependencies have imports: the independent K-flat predicate and
resolution modules, independent-universe K-injective resolutions, upstream
`KInjectiveRestrictLocalized`, the normalized derived-slice comparison module,
Mathlib K-injective shift and adjunction-shift uniqueness, the evaluation-transpose
module through its public dependency import, and independent-coefficient tensor
descent. No downstream projection-restriction module is imported; that module
assumes the shift conclusions which this item states.

Edge cases checked before and during writing:

- `n=0`: both representative generator formulas have coefficient 1 and the
  equations use the actual zero-shift isomorphisms, rather than a definitional
  assertion that shift zero is the identity functor.
- Negative n and negative first degree p: `n,p : ℤ` throughout;
  `Int.negOnePow` supplies the sign, with no natural-degree restriction.
- Odd n,p: the second formula gives -1; the first remains unsigned. In
  characteristic two the same unit action is 1, so no characteristic exclusion.
- Zero ring, zero complexes, and zero sheaves: no nontriviality, nonemptiness, or
  invertibility assumption on a section occurs. The coefficient *identification*
  is the only stipulated ring isomorphism.
- Unbounded inputs: all complexes are indexed by ℤ and all derived objects are
  in the ordinary unbounded derived category. There is no lower/upper bound.
- Empty site: the theorem is conditional on an object V, as the node is, and
  adds no existence assumption for a site object. Empty coverings are unaffected.
- Identity morphism and arbitrary site object V: no property of u or V other
  than the displayed geometric morphism and slice constructions is imposed.
- Localization sizes: `w` is explicit and independent of the small-site universe
  `u`; the four localization instances are those required by the recorded API.

Searches for an existing exact statement (all via the prescribed `msearch.py`):

- LeanFinder, "Canonical slice restriction comparisons for derived direct image
  pullback and tensor commute with integer shift isomorphisms": 8 hits, including
  `Functor.commShiftPullback` and generic localization/factorization shift lemmas.
  None states the simultaneous β/θ/tensor slice normalization.
- Loogle, `"NatTrans.CommShift", "mapDerivedCategory"`: zero hits.
- Mathlib grep under `Algebra`,
  `overFunctor.*shift|shift.*overFunctor|over.*commShift`: zero hits.
- LeanSearch, "Restriction to a localized ringed site commutes with derived functor
  shift comparisons": 8 hits, notably `mapDerivedCategory.CommShift`, shift
  compatibility of its factorization, and `commShiftOfLocalization`.
  The exact-functor shift instance is reused; none states the desired comparisons.
- Project/source `rg` for `ringed-slice-comparisons-shift`,
  `[Ss]lice.*[Ss]hift|[Ss]hift.*[Ss]lice`, and `CommShift` in ringed modules:
  no existing theorem for this node. `RingedSliceHomSourceShift` concerns the
  different internal-Hom source-shift comparison; `RingedProjectionRestriction`
  records the present conclusions as fields of its Local data and therefore
  cannot supply a noncircular existing proof/statement of this general lemma.

The local Stacks source was read at `lemma-pullback-tensor-product` (07A4),
`lemma-restrict-K-injective-to-open` (08FI), and the preceding exact restriction
discussion. The target node explicitly identifies the signed-shift argument as
agent-written, and the docstring includes its six proof steps, with all dependency
roles and both tensor signs.

Validation: the prescribed `scompile.py` compiled the standalone sandbox and the
actual library module name cleanly (about 9 seconds each), without warnings.
One initial instance elaboration needed all four universe arguments on the existing
exactness theorem; these were made explicit. Two implicitly used instance binder
names were prefixed with `_`, as the linter requested. No mathematical hypothesis
or conclusion changed. There are no node faults or statement disputes, new DAG
nodes, dependency repairs, or source-statement corrections in this delivery.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
