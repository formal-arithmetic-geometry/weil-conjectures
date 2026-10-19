## Worker report

The module `Sheaf.Paper.FiniteClopenDerivedDecomposition` states the entire finite-clopen
coefficient decomposition through 16 named theorem statements and their canonical helper
functors. Every theorem proof is `sorry`. Definitions have actual data: site composition,
sectionwise module restriction, exact termwise descent, full-subcategory lift, or an existing
coefficient construction. No equivalence, object, or map is selected from an unspecified
existence proposition. The primary record lists every declaration in the module.

I read the node and all its statement dependencies, their recorded signatures and source
modules, Stacks `sites.tex` at lemma-mapping-property-glue (Tag 04TS, with 04TQ/04TR), and the
current main-20261015 section-invariant blueprint text. The latter supplies the finite-clopen
argument's purpose; the eleven-step expansion is the node's existing proof, not a new blueprint
claim. Each theorem docstring records the relevant steps of that expansion.

The hypothesis and conclusion correspondence is as follows. All family theorems retain the
finite-type, finite-index, closed-immersion, disjointness and covering hypotheses through a
section-level `include`; these hypotheses are therefore present in the elaborated theorem,
even where the conclusion alone would not mention them.

| Node text | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field and the prime distinct from its characteristic | `P : PurityFiniteSetting`; `P.field`, `P.coefficients`, and `P.coefficients.different` are the recorded data. |
| Finite extension, valuation ring, uniformizer, positive finite quotient | `P.extension`; the existing `Padic.coefficientExtensionRing` and integral constructions. A natural number `n` denotes exponent `n+1`, so every positive level occurs. |
| Finite-type scheme over k | `X : Over (Spec (CommRingCat.of P.field.k))`, `[hft : LocallyOfFiniteType X.hom]`, `[hqc : QuasiCompact X.hom]`. |
| Finite family of k-subschemes, with specified inclusions | `I : Type w`, `[hfinite : Finite I]`, `Xi : I → Over ...`, `j : ∀ i, Xi i ⟶ X`. The index universe is independent, and there is no `Nonempty I` assumption. |
| Open and closed | `[∀ i, IsOpenImmersion (j i).left]` and `[hclosed : ∀ i, IsClosedImmersion (j i).left]`. |
| Pairwise disjoint and covering | `hdisjoint` compares the underlying image sets at unequal indices; `hcover` says their indexed union is `Set.univ`. |
| Small pro-etale sites, unchanged sizes | `Scheme.ProEt.topology`, with objects in `Type (u+1)` and morphisms in `Type u`; ring/module sections are in universe `u+1`. |
| R is a finite coefficient sheaf or the completed integral sheaf | `clopenRing X n integral`: its two branches are the existing `integralCoefficientCommRingSheaf` and `completedIntegralCommRingSheafUnrestricted`. |
| Restriction gives an exact module equivalence | `finiteClopen_module_equivalence`; the forward functor is exactly `Functor.pi'` of `clopenRestriction`. Both directions preserve finite limits and finite colimits. Each coordinate restriction is additive and exact by `clopenRestriction_exact`. No nonexistent Abelian or Preadditive product-category instance is assumed. |
| Explicit inverse U ↦ product of component sections | The family `φ F V` consists of additive equivalences to `∀ i, (F i)(V ×_X Xi)`. Its three equations specify scalar action through the pullback projection, componentwise restriction maps, and componentwise action on module morphisms. Thus it identifies the inverse as a module-valued presheaf, including all its operations and maps. The additive equivalences allow small representatives of finite products even when the finite index type has a larger universe. |
| Induced unbounded derived equivalence | `finiteClopen_unbounded_decomposition`; its functors are `clopenRestriction.mapDerivedCategory`, so they are degreewise restriction localized at quasi-isomorphisms. The target is the product of the component derived categories, never a derived category of an assumed abelian product. |
| Cohomology and derived tensor componentwise | The homology-functor natural isomorphisms and the tensor-functor natural isomorphisms in `finiteClopen_unbounded_decomposition`. Tensor is expressed using the existing normalized `RingedSiteDualityModel`, not a new tensor choice. |
| The same finite and integral coefficient restrictions | `finiteClopen_finite_restriction_identification` and `finiteClopen_integral_restriction_identification` give coefficient-ring identifications, scalar transport normalized after `DerivedCategory.Q`, and comparison with the actual finite or complete constructible pullback. The latter is compared on complete objects only: completed pullback on all unbounded modules is not incorrectly asserted to be an equivalence. |
| Strict towers and derived inverse limits | `finiteClopen_strict_roos` is a natural isomorphism of functors on strict towers of complexes, using the actual `integralOperationsRoosFunctor`. Whiskering restricts all tower terms, transitions and tower morphisms. Exact restriction preserves triangles; exact countable pro-etale products make this same Roos complex compute the derived limit. This keeps its original maps, rather than asserting uniqueness of a cone in a bare triangulated category. |
| Finite Dbc and Dbctf equivalences | `clopenFiniteConstructiblePullback`, `clopenFiniteTorPullback`, and `finiteClopen_finite_equivalences`. The lifts use the recorded intrinsic predicates and actual `finiteDerivedPullback`, on objects and arrows. |
| Any common finite cohomological and Tor bounds | `finiteClopen_finite_bounds`: for each ordered `[a,b]`, support containment and `HasProEtaleTorAmplitude` are each equivalent to their componentwise conditions. `finiteClopen_finiteTor_iff` additionally records existence of common bounds. |
| Integral Dbc and Dbctf equivalences | `finiteClopen_constructible_equivalences`, using the existing `constructibleIntegralPullback` and its full-subcategory lift `clopenIntegralTorPullback`. |
| Integral bounds uniform in all reductions | `finiteClopen_integral_bounds`: the same `a,b` is outside the universal quantifier over every `n`; the componentwise side universally quantifies over both `i` and `n`. |
| Rational and algebraically closed coefficients | The final two conjuncts of `finiteClopen_constructible_equivalences` use the existing raw `rationalDerivedPullback` and `commonStageDerivedPullback`, with their integral and representative formulas unchanged. At these stages `finiteTorFieldCoefficientCategory` is an alias, so these are also precisely the field Dbctf equivalences. |
| Tensor and tensor units on these equivalences | `finiteClopen_tensor_and_reduction` states the finite, completed integral, rational and common-stage natural tensor comparisons; `finiteClopen_coefficient_units` gives each actual unit comparison. `clopenIntegralUnit` is the regular completed module in degree zero, rationalized at the rational stage; `clopenCommonStageUnit` is that same unit at any specified finite coefficient stage. These formulas also apply when the input objects belong to the finite-Tor full subcategories. |
| Coefficient reduction and scalar extension | `finiteClopen_tensor_and_reduction` includes integral-to-finite reduction and every consecutive or nonconsecutive finite quotient (`n ≤ m`, including equality). `finiteClopen_scalar_extension` gives completed extension along every `ι : E →ₐ[Padic l] L` and compatibility with rationalization. `clopenIntegralScalarComparison` and `clopenRationalScalarComparison` reexport the existing canonically normalized scalar comparisons. The common-stage pullback uses precisely those comparisons on every representative, as specified in `commonStageDerivedPullback_existsUnique`. |
| Empty family | `finiteClopen_empty` asserts `IsEmpty X.left` and uniqueness of the empty product's object and every morphism. None of the other equivalence or bound statements excludes this case. |

The helper `clopenResidue_isUnit` states only a consequence of the supplied k-structure:
ell is a nonzero scalar in k and remains invertible in every residue field. The helpers
supplying `Invertible` instances use `IsUnit.invertible` inside their definitions. There
is no extra local-invertibility hypothesis on X or the components.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its fixed data.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `...QuasiCompact`, `...OpenImmersion`,
  `...Morphisms.ClosedImmersion`: `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`,
  `IsClosedImmersion`, with exactly their recorded meanings.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`; the inclusion
  is the existing `MorphismProperty.Over.map` along the weakly-etale open immersion.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `finiteIntrinsicDerivedTensor`, `constructibleIntegralPullback`, `constructibleIntegralTensor`,
  `rationalDerivedPullback`, `rationalDerivedTensor`, `commonStageDerivedPullback`,
  `commonStageDerivedTensor`, and the integral/rational scalar comparisons.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: `intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`, over the actual completed coefficient sheaf.
- `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule` publicly retains `FiniteTorAmplitude`:
  the intrinsic `finiteTorConstructible`, `finiteTorConstructibleIntegral`, and their full
  subcategories are used. The additional fixed-scalar predicate is the canonical realization
  of that identical intrinsic condition; no new Tor notion is supplied here.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` publicly retains the actual finite
  and completed coefficient rings. Both are used directly, with commutativity forgotten
  only by the existing `sheafCompose` functor when forming module categories.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `...ExactFunctor`, `...HomologySequence`:
  `DerivedCategory`, `HasDerivedCategory.standard`, `Functor.mapDerivedCategory`,
  `DerivedCategory.homologyFunctor`, with no new localization.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: the existing Roos convention.
- The seven already recorded nodes added to `stmt_deps` expose objects directly appearing
  in the signatures or definitions: `def-pur-integral-derived-operations`,
  `def-weil-integral-scalar-extension`, `def-weil-rationalization-karoubi`,
  `def-weil-algebraically-closed-coefficients`,
  `lem-weil-constant-coefficient-objects-constructible`,
  `lem-sfb-ringed-site-duality-maps`, `lem-coef-derived-system-evaluation-calculus`.
  They supply, respectively, strict Roos operations, scalar extension, the two field
  categories, the specified coefficient units, normalized derived tensor models,
  and the actual finite quotient derived functor. These are existing dependencies,
  not new nodes or dependency repairs.

The proof-route modules are explicitly imported without `public` when not used by a
signature. For derived-limit existence the imported integral operations already export
`Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`, including the recorded declaration
names. I did not additionally import `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`:
those two modules declare the same full names. This avoids the known duplicate-declaration
failure while retaining exactly the proof dependency's interface.

Edge cases checked before writing: an empty I (empty X and terminal product), a singleton
identity inclusion, empty components within a nonempty cover, the zero sheaf and zero
complex, the first positive coefficient level, different component support/Tor intervals,
intervals uniform in all reductions, equality in `n ≤ m`, identity coefficient extensions,
and repeated or enlarged finite coefficient stages. In particular, no common bound is
chosen separately for each reduction. Finite coefficients retain the additional Tor
condition; it is not identified with constructibility. There is no Karoubi completion.

Searches (2026-10-17):

- `msearch.py leansearch`, “Sheaves of modules on a finite disjoint clopen cover are equivalent
  to the product of the module categories on the components”: eight hits, including
  `TopCat.Sheaf.isProductOfDisjoint`, `SheafOfModules` and `Scheme.coprodPresheafObjIso`.
  Their source types concern topological sheaf sections, module objects, or scheme structure
  sheaves, not this pro-etale coefficient/derived equivalence.
- `msearch.py leanfinder`, “Finite clopen decomposition gives an equivalence of proetale module
  sheaves and bounded constructible derived categories with products of the categories on
  the components”: eight condensed-module functor hits, no exact match.
- `msearch.py loogle`, `SheafOfModules, Equivalence`: no hits.
- `msearch.py grep`, `clopen.*(derived|sheaf)|derived.*clopen|[Dd]isjoint.*[Ee]quiv`:
  25 hits, predominantly unrelated equivalences and topology; no full statement.
- `rg` over the named upstream `WeilConjectures` tree and project `lean/Sheaf` with the same
  conceptual patterns and this item's id: related binary open/closed recollement,
  clopen projectors, and etale sheaf facts, but no finite four-stage coefficient
  decomposition. The upstream `ProEtale/Derived/ClosedImmersion.lean` equivalence is a
  binary recollement construction in a different coefficient presentation, not this item.
- `rg` over those source trees and `dag/lean_names_upstream.json` for the proposed helper
  and principal theorem names returned no collision.

No statement correction, disputed mathematical assertion, new independent definition
node, or dependency-record repair is needed. Only `lean` and the authorized additions
to `stmt_deps` are changed in the item copy. Compilation uses only `scompile.py` and
file-only delivery checks; the shared repository and upstream sources are read-only.

Validation: the final module passed `scompile.py` without errors or warnings. The wrapper
reported 34.8 seconds for its sandbox check and 22.4 seconds for the library-path check,
both under the unchanged 60-second per-file limit. There was no global build.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
