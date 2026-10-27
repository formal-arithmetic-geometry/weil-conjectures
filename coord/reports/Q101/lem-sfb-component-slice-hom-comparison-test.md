## Worker report

Item: `lem-sfb-component-slice-hom-comparison-test`. The delivery states the node in
`Sheaf.AlgebraicGeometry.ComponentSliceHomComparison`, namespace
`AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice`. The main theorem is
`component_slice_hom_comparison_test`; its only postponed proof is `by sorry`.
Every auxiliary definition has actual data. All auxiliary declarations belong to
this node's normalized comparison, and are listed in `lean.declarations`.
The node's mathematical statement, dependencies and proof are unchanged.

The hypothesis and clause correspondence is as follows.

* A commutative condensed ring is the existing `Profinite.CondensedRing.{u}` with
  `[IsCommMonObj Λ.X]`; this includes coefficients without a topological-ring
  presentation. The theorem takes an arbitrary `Scheme.{u}` with `[IsAffine W]`
  and `[IsWContractibleRing Γ(W, ⊤)]`.
* `affineComponentSpace W` is the existing genuine profinite component quotient.
  `Modules Λ S` abbreviates internal modules over `profiniteCoefficient Λ.X S`
  on `Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u+1}`. Thus coverings
  are the finite jointly surjective coverings and the coefficient is the actual
  slice pullback of Λ. Site objects, site morphisms and abelian coefficients
  retain respectively universes `u+1`, `u`, `u+1`; module objects are in `u+2`
  and module morphisms in `u+1`. No site-universe equality is imposed.
* `PullbackData` uses `componentTests`, `componentInverse`, and
  `componentModules`, without replacing the component geometric morphism.
  Its coefficient isomorphism and `factorization` fix the identification at Λ
  with `upperStarFromPoint W`. Its `evaluation` is exactly the dependency's
  `ComponentPullbackUnboundedEvaluation`, including its Kan-unit normalization.
  `PullbackData.derived` is `modules.mapDerivedCategory` on ordinary unbounded
  complexes localized at quasi-isomorphisms.
* For each `U : W.ProEt`, the theorem quantifies `[IsAffine U.left]` and
  `[IsWContractibleRing Γ(U.left, ⊤)]`. `componentMap W U` is the actual map
  of components supplied by `componentAffineObject`. `restrictSheaf` is the
  existing `overMapPullback`, hence literal precomposition on the profinite
  slice. `RestrictionData.coefficient_sections` fixes coefficient transport
  to the identity on actual sections. Its `lax_eq` and `tensor_normalization`
  fix the usual sectionwise tensor maps. Exactness and monoidality are
  asserted as conclusion data, never extra hypotheses of the main theorem.
* `schemeRestriction` is `supportPullback Λ.X U.hom`, the actual inverse image
  with its canonical coefficient transport. `restrictionSections` identifies
  its values with literal restriction via the existing
  `upperStarIsoLocalizationRestriction`. `compositeTest` composes the two
  pro-etale maps; `componentCompositionIso` is the identity on the component
  quotient, with its commuting-triangle proof written out.
* `OrdinaryComparison.iso` is the requested natural isomorphism
  `dW.modules ⋙ schemeRestriction ≅ r.modules ⋙ dU.modules`.
  `OrdinaryBasisFormula` fixes its values on EVERY w-contractible affine
  `V : U.left.ProEt` to the identity on `M(pi_0(V) -> T -> S)`, using the
  dependency's normalized evaluation and the preceding component identity.
  The final uniqueness clause fixes this natural isomorphism canonically.
  Its formula includes all further slice tests: both sequences of successive
  restrictions are the same identity after the canonical component and
  literal-section identifications. Gluing uniqueness gives equality globally.
* `schemeCanonicalMonoidal` transports the existing native module inverse-image
  tensor structure along `supportPullbackIsoUpperStar`. `OrdinaryMonoidal`
  requires this precise structure and the `MonoidalSquare` condition. Thus the
  ordinary comparison respects tensorators and coefficient units, rather than
  an unspecified isomorphism of the underlying functors.
* `OrdinaryComparison.derived` is DEFINED from
  `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso`. This fixes its
  normalization on every unbounded representative. `DerivedComparison`
  specializes `ExactSquareComparison` to these four fixed functors.
  `normalizationW/U/T/R` fix all four derived tensor structures by the
  homotopy-localization tensor and unit equations;
  `monoidal_iso` asserts the derived square is monoidal. The small-colimit
  infrastructure is existential conclusion data for the canonical functors.
* `homComparison F K L` is the EXISTING
  `(Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory K).natTrans.app L`.
  Thus alpha and beta are exactly transposes of pulled-back tensor-Hom
  evaluation. `sliceHomT` and `sliceHomR` assert invertibility of the canonical
  slice-Hom maps. `transportHom` transports the two inputs using the displayed
  slice comparison with contravariance in its first input. `evaluation_square`
  is equality of the restricted global alpha with the transported local beta,
  including the evaluation and tensor comparisons; no arbitrary map occurs.
* `sections` is ordinary additive sections represented by the coefficient unit;
  `derivedSections` is its full right-derived functor into `DerivedCategory Ab`.
  The exact-section fields use w-contractibility of U and the Stonean property
  of T. `SectionComparison.ordinary_formula` specifies pullback of a section
  `a` as `ε F ≫ F.map a`. `derived_formula` fixes its full derived comparison
  by the right-derived unit on EVERY homotopy representative, as in (4.2).
  `localSectionsComparison` is this pullback map followed by derived sections
  of the actual `homComparison`.
* `derived_sections_square` writes the exact equality requested for
  `RΓ(U,alpha)`: start at `RΓ(T,RHom(rK,rL))`, invert the canonical slice-Hom
  map, apply normalized evaluation, invert the derived slice comparison,
  apply `RΓ` to the restricted alpha, then use target slice-Hom and the
  displayed input transports. The result equals `localSectionsComparison`
  for `F_U`. This is an equality of morphisms of ENTIRE derived objects.
* `HomSectionsIdentification` provides the canonical additive cohomology/Hom
  equivalences. It is normalized on every actual derived section by
  `sectionClass` and `sectionTranspose`. These use the degree-zero coefficient
  identity, exact derived sections, and the canonical right-adjoint shift
  mate `homShift`; an unnormalized additive equivalence would not satisfy
  this specification. `cohomology_formula` identifies the homology map of
  `localSectionsComparison` with `shiftedHomMap`, namely
  `F.mapDerivedCategory.map f ≫ (F.mapDerivedCategory.commShiftIso n).hom.app L`.
  The integer `n : ℤ` includes both positive and negative shifts.
* `fully_faithful_test` assumes only `Nonempty dU.derived.FullyFaithful` and
  asserts `IsIso` for the actual full right-derived-sections image of the
  restricted global alpha. It does not replace this conclusion by a list of
  isomorphisms of cohomology groups.
* Naturality in modules is part of `OrdinaryComparison.iso`; naturality in
  both Hom inputs is inherited from the existing `ihomComparison`, the Hom
  bifunctor, natural section comparisons, and the displayed natural iso.
  Successive restriction compatibility is fixed on all nested basis tests
  by `OrdinaryBasisFormula` and its uniqueness clause; the derived iso is
  termwise localization of precisely that comparison. There are no bounded,
  perfect, constructible, flat-input or dualizable-input binders on K and L.

Dependency declarations were read before using them. The principal ones are:

* `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`
  and its w-local/strictly-local hierarchy.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Paper.ComponentRelativeProfiniteSite`:
  `affineComponentSpace`, `component_relative_profinite_site`.
* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`; the existing
  module-object presentation used by component pullback is related to this
  general ringed-site presentation by the imported
  `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`. Internal Hom is the
  existing native derived closed structure, not a new RHom construction.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`; the size-convention node is metatheoretic.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `overMap`, with the literal slice topology.
* `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.sliceFrom`, `sliceEquiv`, `weaklyEtale_localization`.
* `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` reexports
  `derivedInternalHomOfUniverses`; the existing native module-object derived
  internal Hom and its ringed-site comparison supply the same notion here.
* `Sheaf.AlgebraicGeometry.ComponentPullbackUnboundedEvaluation`:
  `componentAffineObject`, `componentAffineObjectMap`,
  `ComponentPullbackUnboundedEvaluation`, `componentEvaluationDerivedIso`,
  `component_pullback_unbounded_evaluation`.
* `Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel`:
  `profiniteCoefficient`, `componentTests`, `componentInverse`, `componentModules`.
* `Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison`:
  `supportPullbackIsoUpperStar`; native `upperStar` supplies the transported
  ordinary monoidal structure. `supportPullback` itself is from
  `CondensedClosedSupportAdjunction`.
* `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`:
  `DerivedCategory.singleFunctorObjUnitIso`; the exact-functor and right-derived
  APIs supply the degree-zero, homology, shift, localization and unit comparisons.

Every recorded proof dependency is imported (with plain imports where it is
only a proof dependency), including geometric exactness, localized module
exactness, the weakly contractible basis, localized tensor restriction,
ringed derived tensor pullback, ringed Hom shifts, slice evaluation transpose,
derived closed structure, the derived-Hom sections model, K-injective
resolutions, exact termwise localization and its natural-isomorphism API.

Sources checked: Hemo--Richarz--Scholbach Proposition 4.3(1), its proof and
(4.2); local Stacks `sites-cohomology.tex`, `lemma-section-RHom-over-U` (08JA)
and restriction (08JB), using evaluation adjunction 08J9 and tensor pullback
07A4. The current blueprint's internal-Hom stability proof was also read;
this is a supporting component-slice lemma, not a modification of that unit.

Edge cases: the zero condensed ring is allowed; the empty affine and empty
basis tests are allowed; empty-site module sections are zero. Zero K or L
is allowed. All integer shifts and arbitrary unbounded complexes are included.
An identity slice gives the identity on the same component sections. A further
slice V over U changes no underlying test scheme and gives the same component
composite, as checked explicitly in `componentCompositionIso`. No coefficient
flatness is assumed: the coefficient comparison is an isomorphism.

Searches for reuse (all with the prescribed wrapper or scoped `rg`):

* LeanFinder query: “Restriction of component pullback to weakly contractible
  affine slice and evaluation adjoint derived internal Hom comparison on
  derived sections”. Eight results concerned ordinary module pullback and
  ordinary sheaf-Hom sections, with no normalized unbounded component-square theorem.
* Loogle query: `ihomComparison`. Zero results through the wrapper; the upstream
  `Functor.LaxMonoidal.ihomComparison` was subsequently located by source search
  and is reused directly.
* Mathlib grep query: `component.*[Ss]lice|[Ss]lice.*component` in CategoryTheory.
  Zero results. Scoped upstream and `lean/Sheaf` searches for component,
  restriction, evaluation, `ihomComparison`, and this exact node id found
  the component-evaluation dependency and the downstream
  `WContractibleComponentDerivedHom`, but no declaration of this node.
  The downstream theorem was read as an API example and is not imported.
* Additional scoped searches located literal profinite `overMapPullback`,
  scheme `upperStarIsoLocalizationRestriction`, coefficient transport,
  `mapDerivedCategoryNatIso`, and signed shift/derived-section APIs. These
  existing definitions are reused; none is copied into a replacement notion.

No statement fault or dispute was found. No new DAG node or dependency repair
was needed. The helper assertion records merely collect the clauses of this
node; their existence is asserted by its one theorem.

Validation: `scompile.py Q101 lem-sfb-component-slice-hom-comparison-test
lean/Sheaf/AlgebraicGeometry/ComponentSliceHomComparison.lean` passed in both
sandbox and actual library namespaces with no errors or warnings. Early
performance failures were repaired by factoring generic tensor and comparison
predicates; no compiler time limit was raised.

## Second reading by Q101

The delivered section with this heading was the worker re-reading their own module ("not a
claim of an independent second agent"). The maintainer's independent second reader replaced it
with the reading below. The Lean module and the node record are unchanged.

Node clauses and the Lean that renders them (`Sheaf.AlgebraicGeometry.ComponentSliceHomComparison`):

1. W a w-contractible affine scheme: `[IsAffine W] [IsWContractibleRing Γ(W, ⊤)]`. Holds.
2. Λ a commutative condensed ring: `Profinite.CondensedRing.{u}` with `[IsCommMonObj Λ.X]`; no
   topological-ring or nonzero hypothesis. Holds.
3. S = π₀(W), Prof/S with finite jointly surjective coverings, Λ_S = q_S^*Λ: `Modules Λ S` =
   `Mod (Sheaf ((coherentTopology Profinite).over S) Ab) (profiniteCoefficient Λ.X S)`. Holds.
4. π_W, F_W = π_W^* with F_WΛ_S = p_W^*Λ: `PullbackData` holds exactly the existential data of the
   landed `component_pullback_unbounded_evaluation` (continuity, braided/exact `componentInverse`,
   coefficient iso α with the monoidal factorization through `upperStarFromPoint`, and
   `ComponentPullbackUnboundedEvaluation`). `modules` = `componentModules`, `derived` =
   `mapDerivedCategory`. Holds. The same existential Braided structure is in the landed dependency,
   and this delivery inherits it.
5. U → W a w-contractible affine test, T = π₀(U): `U : W.ProEt` with `[IsAffine U.left]
   [IsWContractibleRing Γ(U.left, ⊤)]`, and `componentMap W U` = `(componentAffineObject W U).hom`.
   Holds.
6. r_T: `RestrictionData.modules` is `overMapPullback` (literal precomposition) followed by
   coefficient transport. The braided structure is pinned to the instance (`lax_eq`), the
   coefficient is the identity on sections, and the module tensorator is pinned by
   `tensor_normalization` (tensorObjπ is epi). Holds.
7. r_U, restriction to W_proet/U ≃ U_proet: `schemeRestriction` = `supportPullback Λ.X U.hom`
   (actual inverse image). `restrictionSections` identifies it with literal restriction through
   `ProEtale.upperStarIsoLocalizationRestriction`. Holds.
8. The canonical natural isomorphism r_U F_W ≅ F_U r_T: `OrdinaryComparison.iso`. It is pinned on
   every w-contractible affine V over U by `OrdinaryBasisFormula`: the identity on
   M(π₀V → T → S), through the dependency's Kan-normalized evaluations (`basisSections` is the
   `.choose` of a clause pinned on every section) and `componentCompositionIso` (identity on the
   quotient). The conclusion clause `∀ e', e'.iso = e.iso` gives uniqueness. Derived version:
   `OrdinaryComparison.derived`, defined by mapDerivedCategoryNatIso/CompIso. Holds.
9. It identifies the coefficients, the tensor comparisons and the units:
   `OrdinaryMonoidal` (m = transported native structure, `MonoidalSquare`). On the derived level:
   `normalizationW/U/T/R` (μ and ε pinned on Qh objects) and `monoidal_iso`. Holds.
10. It identifies the pulled-back evaluation maps, and α_{K,L} is the transpose of evaluation:
   `homComparison` = Mathlib-style `Functor.LaxMonoidal.ihomComparison` of the derived functor.
   `evaluation_square` is the equality of the two composite closed comparisons, and
   `sliceHomT`/`sliceHomR` are 08JB. True for a monoidal natural isomorphism. Holds.
11. RΓ(U, α_{K,L}) is identified with the evaluation-adjoint map RΓ(T, RHom(K|_T, L|_T)) →
   RΓ(U, RHom(F_U K|_T, F_U L|_T)): `derived_sections_square`. Its middle arrow is
   RΓ_U(S.map α_F). The section identification is `SectionComparison`. Its ordinary part is pinned
   by ε ≫ F.map a. Its derived part is pinned through the right-derived unit on every homotopy
   representative, so by the universal property. It is the pullback normalization of (4.2). I
   checked that the square follows from `evaluation_square` and the naturality of the section
   comparison, so it is consistent. Holds.
12. H^n map = f ↦ F_U(f) for every n ∈ ℤ: `cohomology_formula` with `shiftedHomMap`. The group
   identifications `HomSectionsIdentification` are pinned on every class by `sectionClass` /
   `sectionTranspose` (unit, uncurry, right-adjoint shift mate). The same generic convention is
   used on both sides. Holds, and it holds for arbitrary K, L on T, which is stronger than needed
   and true.
13. If F_U is fully faithful on D, then RΓ(U, α) is an isomorphism of derived objects:
   `fully_faithful_test`, with hypothesis `Nonempty dU.derived.FullyFaithful` and conclusion
   `IsIso` of RΓ_U(S.map α). It is not a per-degree statement. Holds.
14. Natural in K, L and compatible with successive restrictions. Naturality is built in (natural
   isomorphisms, and ihomComparison is a natural transformation). Successive restrictions are not
   a separate clause. They follow from the basis identity formula, which is stated on every
   w-contractible test V of U, and from uniqueness. I accept this as a derivable consequence.
15. No boundedness, perfectness or dualizability: none is assumed. Holds.

Edge cases checked:
- W or U empty: modules are zero and the formulas are vacuous.
- U = W.
- The zero ring Λ.
- n positive, negative and zero.
- Zero K, L.

Universes: site u+1/u and coefficients Ab.{u+1}, as in the dependency. No universe equation is
added.

The exactness fields (sectionsT/U) are true conclusions: T = π₀(U) is extremally disconnected,
and U is w-contractible.

Searches: the live side tree has no other `ComponentSlice` declaration or module. The
ihomComparison, overMapPullback, supportPullbackIsoUpperStar and upperStarIsoLocalizationRestriction
APIs are reused rather than copied. Only the item's `lean` field changed. There is one `sorry`
theorem, and the docstrings carry the source and the blueprint.

Advisory (stmt_deps cannot be changed at stage 2): the statement uses definitions owned by
def-zl-condensed-lisse-evaluation-model (componentInverse, componentModules, componentTests,
profiniteCoefficient), def-sfb-condensed-closed-support-functor (supportModules/supportPullback)
and def-sfb-condensed-pullback-tensor-comparison (supportPullbackIsoUpperStar). They are reached
only transitively through lem-sfb-component-pullback-unbounded-evaluation; the maintainer may add
them to stmt_deps.
