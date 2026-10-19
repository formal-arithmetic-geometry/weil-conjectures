## Worker report

The module `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose` states
`CategoryTheory.ringedSlice_evaluation_transpose`. Its only postponed proof is that theorem,
whose docstring contains all five steps of the DAG proof. Definitions contain actual data.
The item statement, its dependency lists, and its proof have not been changed.

The theorem first asserts existence of the normalized comparison data, then asserts the
three identities for every such datum. Thus the normalization is not an extra hypothesis
whose satisfiability is assumed, and the claim is not limited to arbitrarily chosen maps.
`RingedSliceEvaluationComparisons` is the owning node's interface for its explicitly
specified comparisons, not another tensor or internal-Hom definition. Its associated predicates specify
actual representative formulas and commutative localization squares. The first conjunct is
`Nonempty {d // RingedSliceEvaluationNormalized ... d}`; the second quantifies over
all comparison data satisfying that same predicate. The four long model predicates
are separate transparent definitions to keep the dependent record constructor small. All helper declarations
are listed in `lean.declarations` and have source/blueprint docstrings.

Hypotheses and clauses, in the order of the natural statement:

- A site small in the module universe is `{C : Type c} [Category.{v} C]`,
  `J : GrothendieckTopology C`, with coefficients/modules in `max c v u`.
  Site objects, arrows and coefficient sizes are independent. The abelian-sheaf
  sheafification instances are made explicit; they exist at this size. `A` is a sheaf
  of **commutative** rings. No subcanonical topology or fibre products are assumed.
- The module categories are the recorded `SheafOfModules`, also exposed by
  `ringedSiteModules`; the two unbounded categories are `DerivedCategory` with separately
  bound localization universes `w` and `w'`. `U : C` is arbitrary.
- The slice ring is `A.over U`, with `J.over U`. Complex restriction is exactly
  `SheafOfModules.overFunctor` mapped to complexes. `ringedSliceDerivedRestriction` is
  the recorded `ringedDerivedRestrictionGeneral`, supplying the very same localization
  instance explicitly at the definitionally equal presentations of the underlying slice
  ring. `ringedSliceLocalizationIso` is its actual `mapDerivedCategoryFactors`.
- `H` and `H_U` are `derivedInternalHomOfUniverses` and its slice specialization.
  No unconstrained replacement Hom bifunctor appears.
- `S,T` and `SU,TU` are the existing `CoefficientClosedStructure` and
  `CoefficientTensorModels` for those exact Hom functors. The tensors are `S.tensor` and
  `SU.tensor`; their model is the existing actual `coefficientTotalTensor`, and their
  generators are `coefficientTensorGenerator`, including the actual sheafification unit.
  The `uncurry_model` field already fixes the tensor-Hom counit and transpose.
- `rho` is an isomorphism for each pair of derived objects. `rho_naturality` is exactly
  simultaneous naturality in the two arguments (equivalently a natural isomorphism on
  the product category). `kflat` supplies the exact `RingedSliceFlatRestriction` property: preservation of K-flat flat-term models. The raw comparison record is categorical and is specialized here to the exact recorded Hom and restriction functors; its separate normalization predicates carry every site-specific formula.
  `RingedSliceTensorModel` supplies a chain isomorphism on each such pair, requiring identity on
  every local pure-tensor total-degree summand, and the full square with `T.iso`,
  `TU.iso` and the actual restriction/localization comparison. The identity-ring-map
  localization is encoded directly by sectionwise `overFunctor`; no arbitrary ring
  map, pullback, or ordinary-unit comparison is chosen.
- `eta` and `eta_naturality` give the contravariant/covariant natural Hom isomorphism.
  `RingedSliceHomModel` quantifies over every source complex and every K-injective target complex.
  Its chain isomorphism preserves each `(n,p,p+n)` product projection, evaluated at
  every `W -> V -> U` and every local section. `Over.mk W.hom.left` is exactly
  relocalization to the original site over `V.left`. Thus this is equality of the
  actual local families with their existing Hom-complex differential, not just existence
  of an isomorphism of the right objects. The two `RingedKInjectiveHomModel` equations
  identify the K-injective representatives using the actual fixed augmentation and
  `coefficientHomResolutionIso`. The localization square fixes eta itself.
- Evaluation is the existing `S.evaluation`, the right-tensor adjunction counit;
  transposition is the existing `S.transpose`, the actual adjunction Hom equivalence.
  The first conjunct is precisely `rho.inv` followed by `r.map evaluation` equals
  `SU.tensor.map (eta.hom, identity)` followed by slice evaluation. Composition is
  written in Lean's left-to-right `≫` order.
- `V L M` range over all derived objects; `V` is the statement's test object `T`
  (the letter `T` is already occupied by its canonical tensor-model datum).
  `f : S.tensor.obj (V,L) ⟶ M` is any derived morphism. The second conjunct is
  precisely the displayed transpose equation, including restriction of `f` after
  `rho.inv` and restriction of `S.transpose V L M f` before `eta.hom`.
- `sigma` and `sigmaU` are fixed by their total-tensor chain isomorphisms:
  `sigma_naturality` and `sigmaU_naturality` impose simultaneous naturality in both
  arguments on their respective derived categories. `RingedSliceKoszulModel` and
  `RingedSliceKoszulModelU` require every pure-tensor generator to map to
  `(p*q).negOnePow` times the exchanged generator and commute with the actual
  tensor representative comparisons. The third conjunct is exactly restriction of
  source symmetry followed by `rho M L` equals `rho L M` followed by slice symmetry.
- There is no boundedness, perfectness, finite-generation, or invertibility hypothesis
  on evaluation. K-flatness, flatness and K-injectivity occur only on representatives
  inside their canonical comparison characterizations, not on `V,L,M`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (transparent `SheafOfModules` specialization).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, its localization construction,
  functorial-replacement and K-injective representative comparisons.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `overMap`, `overFunctorMap`;
  `Mathlib.CategoryTheory.Sites.Over`: `J.over`, `Sheaf.over`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `CategoryTheory.ringedOverFunctor_exactGeneral`,
  `CategoryTheory.ringedDerivedRestrictionGeneral`.
- `Mathlib.Algebra.Homology.BifunctorShift`: total tensor via
  `CochainComplex.mapBifunctor`; the existing `coefficientTotalTensor` wraps it.
- `Sheaf.Algebra.Homology.KFlat` and its public independent-coefficient interface:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  and its uniquely characterized comparison; see the dependency-record repair below.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`:
  `CategoryTheory.ringedInternalHom_tensor_adjunction`, `ringedInternalHom_restriction`,
  `ringedInternalHom_exact`. The first declaration is not the entire dependency:
  the source also contains the slice comparison and exactness clauses. The item's
  helper interface retains its additional explicit representative normalization.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`:
  `CategoryTheory.isKInjective_restrict_localized`.
- `Sheaf.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `homComplexFunctor`, `homComplex_exists` and its fixed product projections.
- `Sheaf.Paper.CoefficientRingedTensorHomModel` and its public representative module:
  `WeilConjectures.CoefficientClosedStructure`, `CoefficientTensorModels`,
  `coefficientTotalTensor`, `coefficientTensorGenerator`, `coefficientHomComponent`,
  `coefficientHomResolution`, `coefficientHomResolutionIso`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`:
  `SheafOfModules.wf_site_derived_tensor_descent`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`:
  `SheafOfModules.exists_localizedSiteTensorRestriction` (including its pure-tensor clause).
- Proof infrastructure: `SiteTensorFunctoriality` for the sheaf tensor and its generators;
  `PresheafOfModules.sheafification` and its adjunction; the two sheafification compatibility
  declarations in `Mathlib.CategoryTheory.Sites.CoverLifting` recorded by the Mathlib leaf.

Sources opened: the current blueprint's `lem-weil-delta-restriction.proof.md` and
`sites-cohomology.tex` at the actual pullback-K-flat, pullback-tensor-product,
internal-hom and restriction-RHom-to-U lemmas. The source's evaluation/transpose
argument applies to slice restriction and does not assert it for closed immersions.

Edge cases checked before drafting: zero test/source/target complexes; degree-zero
modules; odd degrees (the sign is `(p*q).negOnePow`, not sign-free symmetry); terminal
`U` (the usual identity restriction); arbitrary slices with no terminal object in the
original site; the empty site (the statement quantifies over `U`, so has no such
instance); unbounded complexes on both sides. The same maximum module universe
contains the slice's object universe `max c v`; no equality `c=v`, `w=w'`, or `u=c`
is imposed. Replacing rho by minus rho would violate `RingedSliceTensorModel`, which is why
naturality alone is not used as its characterization.

Searches made with the prescribed `msearch.py`:

- LeanFinder: "Slice restriction of sheaves on a ringed site preserves derived tensor Hom
  evaluation and tensor Hom transpose"; eight hits, ordinary sheaf/unit adjunctions and
  LightCondensed Hom formulas, none the normalized unbounded slice statement.
- Loogle: "CategoryTheory.MonoidalClosed.curry_natural_right, CategoryTheory.expComparison_ev";
  zero hits for the combined query.
- Mathlib grep: `expComparison_ev|curry.*natural` in `CategoryTheory/Monoidal/Closed`;
  21 hits, ordinary currying naturality and Cartesian exponential comparison. These do
  not identify the ringed-site derived tensor/Hom representative comparisons.
- LeanSearch: "Restriction to a slice ringed site preserves the tensor Hom adjunction
  evaluation and Koszul symmetry in the unbounded derived category"; eight hits,
  scalar restriction/coextension and ordinary sheafification/pullback adjunctions,
  no matching statement.
- `rg` of the upstream `WeilConjectures` source for the item id and slice/evaluation/
  transpose combinations found no match. `rg` of the project's `lean/Sheaf` found
  tensor/Hom model and restriction infrastructure, but no theorem with all three
  normalized equations. A second exact-name search for every new declaration in
  Mathlib, upstream and `lean/Sheaf` found no collisions.

No mathematical statement dispute or source correction was needed. Compiler validation
and delivery preflight are performed through the prescribed wrappers only.

## Dependency modules

`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` receives only a `lean`-record repair
under §1(B), reusing an existing module and theorem. Its old primary declaration,
`AlgebraicGeometry.Scheme.pbcActualScalarDerivedPullIso_exists`, is a scalar-change
comparison for a scheme morphism. It cannot supply the generic ringed-site tensor
pullback or its K-flat preservation clause. The existing
`SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
states both clauses for a general ringed-topos morphism and arbitrary ring map, with
independent site object and Hom universes. It specifies a unique natural tensor
comparison by the canonical total-complex square. Its public imports include the
ordinary pure-tensor comparison and ordinary unit normalization. The source was
read both locally and via `scompile.py --source`; no new dependency module is written.
The node's mathematical statement, proof, dependencies and all other fields remain intact.
The item itself spells out the identity-ring-map slice specialization and its exact
model formulas, including separate source and target localization universes.

## Second reading by Q03

This is a fresh self-reading of the retained packet against the node and the full Lean
file, under the dispatcher's instruction not to start other agents. It does not claim
an independent worker review; the maintainer supplies the independent review. I reopened
the current blueprint delta-restriction proof, Stacks 07A4, 08J9 and 08JB, the exact
`CoefficientClosedStructure`/`CoefficientTensorModels` definitions, and the published
general tensor-pullback theorem. The following checks record actual clause matches.

| Node hypothesis or clause | Lean rendering and finding |
| --- | --- |
| Site small relative to modules; commutative ring; arbitrary slice object | `C : Type c`, `Category.{v} C`, `J`, `A : Sheaf J CommRingCat.{max c v u}`, and `U : C`. `max c v u` contains the site and slice object sizes; no equality of the site universes or special property of `U` is imposed. The sheafification instances support the recorded abelian category. |
| Module sheaves and unbounded derived categories | Every complex uses the recorded `SheafOfModules` over the underlying ring sheaf and degree type `ℤ`. `HasDerivedCategory.{w}` and `HasDerivedCategory.{w'}` keep localization sizes independent. No boundedness or finite-generation binder occurs. |
| Exact derived slice restriction and identity coefficient map | `ringedSliceComplexRestriction` is termwise `SheafOfModules.overFunctor`; `ringedSliceDerivedRestriction` is the recorded `ringedDerivedRestrictionGeneral`; `ringedSliceLocalizationIso` is `mapDerivedCategoryFactors`. Ring and module sections at `V : Over U` are the original sections at `V.left`, so the identity-ring-map unit identification introduces no scalar twist. |
| Actual derived Hom and tensor, with normalized evaluation | `derivedInternalHomOfUniverses` is used on both sites. `S,SU : CoefficientClosedStructure` and `T,TU : CoefficientTensorModels` are the dependency's interfaces, whose `uncurry_model` fixes the evaluation on actual sheafified generators. `S.evaluation` is the adjunction counit and `S.transpose` is its Hom equivalence. |
| K-flat flat-term models remain such after restriction | `d.kflat : RingedSliceFlatRestriction J A U` quantifies over each K-flat flat-term complex and concludes both K-flatness and termwise flatness of its restriction. These are model conditions, not assumptions on the arbitrary derived objects. |
| Canonical natural tensor comparison | `d.rho` is an isomorphism for every pair; `rho_naturality` states its two-variable naturality. `RingedSliceTensorModel` fixes each generator at every `p+q=k` and `V : Over U`, and its localization square relates `d.rho` to `T.iso`, `TU.iso`, the actual chain isomorphism, and `ringedSliceLocalizationIso`. |
| Canonical Hom restriction comparison on K-injective models | `d.eta` and `eta_naturality` have the required contravariant/covariant types. `RingedSliceHomModel` quantifies over arbitrary source complexes and K-injective targets, fixes each Hom projection by evaluating at `W : Over V`, and imposes the localization square. Its two `RingedKInjectiveHomModel` equations use the fixed augmentation, so no arbitrary K-injective identification is substituted. |
| Koszul symmetry on all derived objects | The retained packet had only `sigma` and `sigmaU` components and normalization at objects literally of form `DerivedCategory.Q.obj P`. This was the returned H3 mismatch. Added `sigma_naturality` and `sigmaU_naturality`, each for all `L M L' M'` and arrows `f,g`, with swapped tensor map `(g,f)` on the right. `RingedSliceKoszulModel` and `RingedSliceKoszulModelU` still fix the pure-tensor image to `(p*q).negOnePow` times the exchanged generator through `T.iso` or `TU.iso`. Naturality along isomorphisms from K-flat models now fixes components at every derived object, including objects not literally those model images. |
| Evaluation identity | The theorem's first equality is `(d.rho (H.obj (op L,M)) L).inv ≫ r.map (S.evaluation L M) = SU.tensor.map (eta.hom, identity) ≫ SU.evaluation (r.obj L) (r.obj M)`. This is exactly the node's composition order in Lean's `≫` convention. Neither evaluation is inverted. |
| Transposition identity for every test object and derived morphism | `(V L M)` are arbitrary derived objects and `f : S.tensor.obj (V,L) ⟶ M` is arbitrary. The second equality applies `SU.transpose` to `rho.inv ≫ r.map f`, and equates it to `r.map (S.transpose V L M f) ≫ eta.hom`. The node's test object `T` is named `V` because `T` already names the tensor model. |
| Symmetry identity | The final equality is `r.map (d.sigma L M).hom ≫ (d.rho M L).hom = (d.rho L M).hom ≫ (d.sigmaU (r.obj L) (r.obj M)).hom`. Both symmetry families now have global naturality as well as their signed model normalization. |
| Canonical comparison existence, rather than an assumed arbitrary comparison | The first conjunct is `Nonempty {d // RingedSliceEvaluationNormalized ... d}` and the rest quantifies over every normalized `d`. Thus the new naturality fields must also be constructed by the single postponed theorem; their existence is not an additional input hypothesis. |

Dependency-record rereading: `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` still
needs the retained §1(B) repair because its base declaration concerns a scalar-change
square for a scheme morphism. The existing generic theorem named in the repaired
record treats an arbitrary ringed-topos adjunction and ring map. Its first conjunct
preserves the K-flat flat-term class; its second is the unique natural tensor comparison
with its full total-complex square. The saved `lean.statement` stopped inside the `hPR`
binder at `(J`, an H2 truncation. It now copies the entire 104-line, 6409-character
signature from the published source, including `hPS`, the two tensor bifunctors, their
model comparisons, and both conclusion clauses. Extraction uses the final theorem-body
delimiter, not a named-argument `:=` inside a binder. The module was also read with
`scompile.py --source Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
No dependency module or mathematical statement changed.

Rechecked edge cases: degree-zero generators give sign `1`; two odd degrees give sign
`-1`; zero objects and zero morphisms are included by the unrestricted binders. For an
object merely isomorphic to a localized K-flat model, the added naturality square
transports the model symmetry component. Inverse naturality follows from the components
being isomorphisms. Source and slice naturality are separate, so the slice is not limited
to objects literally in the image of restriction. Unbounded complexes and arbitrary
independent localization universes remain included.

## Returned points repaired

- H3: added both global symmetry naturality fields; retained all signed representative
  equations and all three target equations.
- H2: replaced the truncated dependency signature by the full published theorem signature.
- H1/H11: replaced the placeholder second-reading text with the above explicit rereading,
  covering each hypothesis, normalization and conclusion, the dependency-record mismatch,
  and the actual repairs. This is honestly identified as a self-reading under the current
  no-delegation brief.

## Validation

The saved packet first passed `deliver2.py ... --no-push` as commit `167657a985`.
That mechanical pass did not detect the returned semantic naturality defect; the repair
above was therefore made while retaining the rest of the saved work. Both sandbox node
copies were compared against the current shared nodes: only their `lean` fields differ.
The delivery wrapper refreshes the base and builds the reviewable commit.

After the naturality repair, the delivered module passed the prescribed
`scompile.py Q03 lem-weil-pbc-ringed-slice-evaluation-transpose <module>` on 2026-10-17:
sandbox compilation 7.8 seconds; library-name compilation 8.8 seconds; exit zero,
with no errors or warnings. There remains exactly one postponed proof, the named main
theorem. Definitions contain actual data and no new theorem was added.


## Independent maintainer review repair

The independent review of immutable delivery ed46ece0c85acb5c24ece3b11b21e84f5cf3b9e5
found the mathematical statement and its representative normalizations correct.
It repaired the mechanical H9 omission of explicit proof-dependency imports required
by coord/brief-stage2.md section 3. The complete replacement module adds imports of
RingedTopoiCanonicalTensorPullbackOfUniverses, RingedInternalHomExactRestriction,
KInjectiveRestrictLocalized, WeilSiteDerivedTensorDescent, SiteTensorFunctoriality,
Presheaf.Sheafification and Sites.CoverLifting. No declaration, signature, definition,
proof, mathematical node field or dependency record was altered.

The independent reviewer reran scompile.py on the immutable snapshot module: sandbox
8.4 seconds, library-name check 9.6 seconds, exit zero and no diagnostics. The replacement
module also passed: sandbox 8.3 seconds, library-name check 9.5 seconds, exit zero and
no diagnostics. The installed wrapper currently delegates these private overlay checks
to its server service. No direct SSH, live Lean write, repository edit or global build
was performed by the reviewer. The standalone review.md records the complete review.
