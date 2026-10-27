## Worker report

Item: lem-sfb-profinite-free-slice-derived-hom. Stage 2, Q65, 2026-10-22.

The delivery states `AlgebraicGeometry.ProEtale.ProfiniteFreeSlice.exists_comparison`
in `Sheaf.Paper.ProfiniteFreeSliceDerivedHom`. Its conclusion is `Nonempty
(Comparison Λ X P)`. The structure packages exactly the specified canonical
identifications, the natural isomorphism of ordinary unbounded derived functors,
and the free-generator/K-injective normalization. No object is chosen from the
postponed theorem: all helper definitions have real data, and the theorem only
asserts existence of the fully normalized comparison package. There are two
postponed theorems: `pointModulePullback_exact` (the structural property needed to
form the termwise point pullback) and `exists_comparison`. Both have source and
complete proof docstrings. The instance declarations project proofs from the
named structural theorem; no definition has sorry data.

The previous worker's reported stage-1 refusal was not a stage-2 obstruction.
The live item was split/reviewed by Q56 on 2026-10-22 but had no `lean` record.
I read that live version and state it without re-splitting. Only `lean` changes.
There is no statement correction, disputed statement, dependency repair, or new node.
The supplied CompactObject example has since been withdrawn and forwards to the
identical upstream declaration; its node's current binding was read as well.

Hypotheses and clauses, with their exact Lean counterparts:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Any scheme X, with its small pro-etale site | `X : Scheme.{u}` and `Scheme.ProEt.topology X`, whose object universe is u+1 and morphism universe is u. No affine, separated, Noetherian, qcqs, or nonempty assumption. |
| Compatible coefficient universes | Explicit `universe u`, abelian groups and set sheaves in u+1; the site objects remain in u+1 and arrows in u. This uses the given size convention and does not identify the site's object and morphism universes. |
| Any commutative condensed ring Λ | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, `[MonObj Λ]`, `[IsCommMonObj Λ]`. This is the unbundled form of `Profinite.CondensedRing`; it requires no topological presentation. |
| p_X and B = p_X^*Λ | `upperStarFromPoint X` and the recorded `condensedRingObj Λ X`. `pointModulePullback` is the existing `mapMod` lift. |
| Internal B-module category | The existing abbreviation `ModuleObjectRingedComparison.Internal Λ X`, definitionally `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj Λ X)`. |
| Ordinary unbounded derived category | `DerivedCategory (Internal Λ X)`. Neither bounded subcategories nor a completed category is used. |
| K-injective total right derived image | `CondensedRing.moduleObjectDerivedPushforward Λ (test X P).hom`, definitionally the total right derived functor of the full `lowerStar`. `derivedSliceModel` uses `rightDerivedFunctorObjQIso`, not a degreewise cohomology calculation. |
| Derived internal Hom | The actual `CondensedRing.derivedHom Λ X`; its section-ring comparison is `ModuleObjectRingedComparison.hom Λ X`, defined using `derivedInternalHomOfUniverses`. |
| Arbitrary profinite P | `P : Profinite.{u}`; no nonempty or finite hypothesis. |
| U = X[P], projection ρ | `test X P := (profiniteToProEtOf X).obj P`, with projection `(test X P).hom`. |
| h_P(Q) and h_U(V) | `parameter P` and `represented X P`, formed with the recorded sites' `uliftYoneda`. `ULift` changes size only and retains actual continuous maps and site arrows. |
| A = Λ[P] | `freeParameter Λ P` uses precisely `Profinite.CondensedAction.InternalBar.free (Mon.mk Λ)` on `parameter P`; no alternative condensed free object is defined. |
| B[h_U] is the left adjoint of forgetting modules to sets | `localFree Λ X` is the existing free abelian sheaf functor followed by `Mod.free`; `localFreeAdjunction` is the composite of the two actual adjunctions. `freeOnTest` applies it to h_U. |
| Canonical p_X^(-1)h_P ≅ h_U | `Comparison.setIso`; `setGenerators` says its transpose under the actual composite set adjunction sends id_P to id_U. Yoneda determines every other generator by restriction. |
| Canonical p_X^*A ≅ B[h_U] | `Comparison.freeIso`; `freeGenerators` says its abelian-adjunction transpose sends the actual universal free generator to the actual generator of h_U. Naturality and B-linearity determine the map. |
| For every unbounded K, gamma is a derived isomorphism | `Comparison.gamma` is a natural isomorphism from `(CondensedRing.derivedHom Λ X).obj (op (derivedFree Λ X P))` to `sliceDerived Λ X P`. `derivedFree` is the degree-zero image of p_X^*A; `sliceDerived` is exact termwise ρ^* followed by Rρ_*. Taking its component at K gives precisely the stated gamma. |
| U_proet is the slice X_proet/U | The existing weakly-etale site localization and object restriction are used in the proof imports. `baseChanged`, `product`, and `productToTest` use their actual base-change/composition functors and adjunction, so the normalization evaluates at V ×_X U. |
| The right-hand side is represented by J(V ×_X U) | `sectionToSlice` is a real map from M(V ×_X U) to (ρ_*ρ^*M)(V), constructed from the module unit followed by the base-change graph restriction. `sectionIdentification` asserts this specified map is an isomorphism; it is not arbitrary extra comparison data. |
| Restriction of a K-injective J is K-injective | `Comparison.restrictionKInjective`. Thus the extra local instance binder in `localization` restricts no J: the immediately preceding conclusion supplies it. |
| Free-generator evaluation on a K-injective representative | `representative J` is an isomorphism of entire cochain complexes. `evaluateHomSection` takes the (0,n) projection of the actual Hom complex, restricts the local Hom map along V ×_X U → V, then evaluates on the generator indexed by V ×_X U → U. `evaluation` identifies the component of the chain isomorphism with that formula, followed by the specified `sectionToSlice`. |
| Unchanged differential | `representative` has type a chain isomorphism, with source the genuine Hom complex and target the genuine termwise ρ_*ρ^* complex transported through the exact equivalence. The degree-zero source leaves only its (0,n) Hom factor; the chain-map condition therefore says d is postcomposition by the unchanged d_J. No degreewise substitute is used. |
| This chain map specifies gamma | `Comparison.localization` is the full localization equation, using `localizationIso`, the actual `coefficientHomResolutionIso`, the fixed Hom-resolution augmentation, and `derivedSliceModel`. It forces gamma to localize this very chain map. Writing the equation after postcomposing with the canonical resolution map avoids selecting an arbitrary inverse or representative isomorphism. |
| Natural in K | `gamma` is a natural isomorphism of functors on the entire unbounded derived category. The localization equation includes every K-injective representative; such representatives compute all derived objects and morphisms. |
| Agreement with internal/section-module equivalence, tensor, evaluation | The actual `equivalence`, `complexForward`, `forward`, and `localizationIso` are reused. `closedStructure`, `tensorModels`, `tensorComparison`, `homComparison`, and `homEvaluation` retain the existing derived comparison and its evaluation square. `homTransportNormalized` is exactly the evaluation equation of that dependency, with its recorded pure-tensor normalization. The chain evaluation uses the original sections and maps, not an unrelated module encoding. |
| For all unbounded N, ρ^*p_X^*N = p_U^*N under canonical composition | `Comparison.pointComposition` and `pointComposition_underlying` specify the module comparison by its precise underlying `upperStarFromPointComp`, preceded by the existing canonical scalar-extension forgetful comparison. The real construction `pointDerivedComposition` lifts that very comparison termwise; its component at any N is the assertion. |

Definitions and dependency interfaces read and used:

- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: the recorded universe convention; its site/derived universe bounds are explicit in the module.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
- `lem-weil-pbc-profinite-point-pullback`: `Sheaf.Paper.ProfinitePointPullback`, `AlgebraicGeometry.ProEtale.profinite_point_pullback`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.coefficientRing`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
- `sk-def-sfb-derived-categories`: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, `CategoryTheory.derivedInternalHomOfUniverses`.
- `def-sfb-profinite-test-objects`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.profiniteToProEtOf`.
- `def-sfb-condensed-free-module-generators`: `Sheaf.CategoryTheory.CondensedInternalBarResolution`, `Profinite.CondensedAction.InternalBar.generator`.
- `def-pur-localized-ringed-site`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, `SheafOfModules.overFunctor`.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`.
- `lem-pe-internal-section-tensor-comparison`: `Sheaf.CategoryTheory.InternalSectionTensorComparison`, `CategoryTheory.InternalAbelianSheafModule.internal_section_tensor_comparison`.
- `lem-sfb-module-object-ringed-site-derived-comparison`: `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`, `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.moduleObject_ringedSite_derived_comparison`.
- `lem-sfb-internal-module-operations-transport`: `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`, `AlgebraicGeometry.ProEtale.InternalModuleOperations.internal_module_operations_transport`.

The section/Hom representative normalization additionally reuses the published
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation` API:
`WeilConjectures.coefficientHomComponent` and `coefficientHomResolutionIso`.
These expose the fixed Hom-product projection and the fixed localization
factorization of the already required `def-pur-hom-complex` and
`def-pur-derived-internal-hom`; they introduce no new mathematical notion.
All recorded statement dependencies are public imports. Every recorded proof
dependency with a stated module is imported publicly if already a statement
input, otherwise by a plain proof import. Mathlib leaves import their recorded
source modules (`Sites.Fpqc`, `CategoryTheory.Yoneda`).

Sources read: Stacks `sites-cohomology.tex`, the full restriction-of-K-injectives
lemma at line 4314 (Tag 08FI) and the construction and restriction discussion
starting at line 8836 (Tag 08J7); HRS PDF pages 5–7, including the point morphism,
Example 3.1, and exact pullback with Λ_Y = f^(-1)Λ_X; the current blueprint
pullback-from-point unit and the item's current statement and seven proof steps.
The current framework note `coord/pefw-upstream-framework.md` was read; the code
uses the live `WeilConjectures.SixFunctors.ProEtale.ModuleObject` declarations.

Edge cases checked before stating:

- P a singleton: h_U is terminal, the free module is B and gamma is the identity
  identification of RHom_B(B,K) with K, up to the canonical pullback comparisons.
- P empty: h_P and h_U are initial sheaves, both free modules are zero, U is empty,
  and both sides of gamma are zero. There is no nonempty hypothesis in any binder.
- P finite, including zero elements: Hom out of the finite free parameter gives
  the corresponding finite product, and the projection direct image does likewise.
- X empty and Λ the zero ring: the definitions and all comparisons still type;
  the relevant categories are trivial. No scalar nontriviality is assumed.
- Unbounded J: every complex has degree index ℤ. K-injective restriction, rather
  than termwise injectivity or a bounded-below replacement, computes the model.
- The object universe of X.ProEt is u+1 and its morphism universe is u; the ring,
  module, and set-sheaf universes contain both. No equality of those two site
  universes, nor perfection/flatness of an input K, was imposed.

Searches actually run (via the prescribed msearch wrapper unless marked rg):

- LeanFinder: “Pullback of free condensed module on a profinite set and derived
  internal Hom as restriction followed by direct image on a slice site”. Eight
  hits, headed by `LightCondensed.ihomPoints` and its functoriality lemmas.
  They concern light condensed modules over an ordinary ring and do not state
  the relative scheme, general condensed-coefficient, unbounded derived identity.
- Loogle: `SheafOfModules.pullbackObjFreeIso, SheafOfModules.hom,
  SheafOfModules.overFunctor`. Zero hits with unknown `SheafOfModules.hom`.
  The actual source is `SheafOfModules.homObj`, read and used via the recorded API.
- Mathlib grep: `free.*[Ss]lice|[Ss]lice.*[Hh]om|pullbackObjFreeIso` in
  `Algebra/Category/ModuleCat`. Five hits in `Sheaf/PullbackFree.lean`, for
  ordinary constant-index free modules and their generator normalization. These
  do not supply the free-on-a-representable relative slice derived calculation.
- LeanSearch: “Derived internal Hom from a free module on a representable sheaf
  is derived direct image of slice restriction”. Eight hits, including
  `LightCondensed.ihomPoints`, `CategoryTheory.Sheaf.freeYonedaHomEquiv`, and
  presheaf/module free constructors. No result states this node. The free
  constructors already used by the dependencies are reused in this delivery.
- rg over both `lean/WeilConjectures` and `lean/Sheaf`: first searched the item id,
  `profiniteFree`, `freeSlice`, and slice/Hom patterns, which located the generic
  internal/section and slice comparison APIs but no relative profinite result.
  A final focused search for the item id, `profiniteFreeSlice`,
  `ProfiniteFreeSlice`, and `freeSliceDerivedHom` returned no existing declaration.

Validation: the helper definitions were compiled incrementally with scompile.py
on the live server, in module mode, with explicit universes and autoImplicit false.
An initial full-statement compile exposed missing point-mapMod exactness instances;
the structural theorem now supplies precisely those inherited properties. The
localization elaboration was repaired under the unchanged 60-second file limit.
The final full-file compile and delivery preflight are recorded below.

Final validation: the complete delivery passed deliver2.py --no-push, including
server preflight and per-file compilation, producing dry-run commit 478487187f9.
The only admitted proofs are the two documented stage-2 theorems.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
