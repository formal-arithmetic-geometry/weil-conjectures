## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint` states
`AlgebraicGeometry.Scheme.proEtale_ringed_closed_kernel_adjoint`, with one `sorry`.
Its three helper definitions have real data: the functor-category kernel of the
open adjunction unit, its composite with the closed inverse image, and the
canonical comparison on any K-injective resolution. No arbitrary functor or map
is substituted for a support construction. No new DAG node or dependency repair
is needed. The original natural-language statement is unchanged.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Scheme X, closed immersion i:Z→X | `{X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]` |
| Quasi-compact complementary open immersion j:U→X | `(U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]` and `hU : Set.range U.hom = (Set.range i)ᶜ` |
| Any sheaf B of commutative rings | `B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}`; no constant, finite, torsion, or completeness condition |
| Sites small in the sheaf universe | Scheme universe u; original ProEt objects in u+1 and morphisms in u; rings and modules in u+1. Published operations supply the standard localization and all-module K-injective-resolution instances. |
| Module categories over B, i⁻¹B, j⁻¹B | Published `proEtaleRingModules` abbreviates recorded `ringedSiteModules` / `SheafOfModules`; inverse-image functor codomains are exactly the indicated inverse-image coefficient sheaves. |
| Inverse and direct images from the ringed theorem | `proEtaleModuleInverseImage`, `proEtaleRingedDirectImage` with ordinary adjunctions `ai`, `aj` |
| Extension by zero from that theorem | `q.functor ⋙ proEtaleRingedExtensionByZero U B`; the equivalence q and `_eq` identify actual open inverse image with the recorded slice restriction. `_aBang` is its ordinary adjunction. |
| H_N = ker(N → j_*j* N) | `ringedSupportKernel U.hom B aj := kernel aj.unit` in the functor category. Evaluation preserves this kernel, giving the canonical pointwise kernel and inclusion. |
| i!_0 N = i* H_N | `ringedClosedKernelShriek i U.hom B aj := ringedSupportKernel ... ⋙ proEtaleModuleInverseImage i B` |
| Natural H ≅ i_*i!_0 carrying inclusion to counit | `eH`; `eH.hom = Functor.whiskerLeft ... ai.unit`; `eH.hom ≫ a0.counit = kernel.ι aj.unit` |
| Natural module-linear Hom bijections | `a0 : proEtaleRingedDirectImage i B ⊣ ringedClosedKernelShriek ...`; `a0.homEquiv` is the natural bijection between the actual module morphisms, with inverse given by its counit. |
| Exact i_* | Existential finite-limit and finite-colimit preservation on the actual functor, together with its additivity; these are conclusions, not assumptions. |
| Unbounded derived i_* ⊣ Ri!_0 | `d0 : (proEtaleRingedDirectImage i B).mapDerivedCategory ⊣ (ringedClosedKernelShriek ...).rightDerivedFunctor` |
| Ri!_0 K = i!_0 I_K for a K-injective resolution | `ringedClosedKernelResolutionIso ... r`, for every `r : K ⟶ I` with `[QuasiIso r] [I.IsKInjective]`. Its data is `rightDerivedFunctor.mapIso (asIso (Q.map r))` followed by `rightDerivedFunctorObjQIso I`. |
| Derived counit induced by sheaf counit | Last quantified equation: apply derived i_* to the specified resolution comparison, use `mapDerivedCategoryFactors`, localize `(a0.mapHomologicalComplex ...).counit.app I`, and compose with `inv (Q.map r)`. |
| j_! ⊣ j* on derived categories | `Nonempty ((q.functor ⋙ proEtaleRingedExtensionByZero U B).mapDerivedCategory ⊣ (proEtaleModuleInverseImage U.hom B).mapDerivedCategory)` |
| i* ⊣ i_* on derived categories | `di`, on exact `mapDerivedCategory` functors |
| j* ⊣ Rj_* | `dj`, with canonical `rightDerivedFunctor` of direct image |
| Ordinary termwise closed counit | The universally quantified formula for `di.counit.app (Q.obj I)` uses the two exact descent comparisons and `Q.map ((ai.mapHomologicalComplex ...).counit.app I)`. |
| i*i_* ≅ 1 | `∀ P, IsIso (di.counit.app P)`; naturality is part of the counit. Its ordinary counit is also explicitly invertible. |
| Derived open counit | Formula for `dj.counit` on every K-injective I, using `rightDerivedFunctorObjQIso I`, exact open descent and the localized ordinary `aj` counit. |
| j*Rj_* ≅ 1 | `∀ P, IsIso (dj.counit.app P)`; naturality is part of the counit. |
| j*i_* = 0 | `∀ P, IsZero ((proEtaleModuleInverseImage U.hom B).mapDerivedCategory.obj ((proEtaleRingedDirectImage i B).mapDerivedCategory.obj P))` |
| No boundedness or constructibility assumption | All derived categories are the full `DerivedCategory`, and every complex is `CochainComplex ... ℤ`. No such predicate occurs. |
| No supported localization triangle used | None is a hypothesis or construction in the module. The docstring carries the nine-step kernel and K-injective proof plan from the node. |

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, scheme morphisms.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact: the recorded
  quasi-compactness notion is `QuasiCompact`; no finite-type condition is added.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed:
  `proEtaleModuleCoefficients`, `proEtaleRingedDirectImage`,
  `proEtaleRingedExtensionByZero`, `proEtale_ringed_open_closed`.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage: `proEtaleModuleInverseImage`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`, the small-model transports.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective: `CochainComplex.IsKInjective`.
- Added landed dependency `def-weil-pbc-proetale-operations`, importing its
  recorded `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` module. This
  publicly reexports the general `ProEtaleOperations` interface:
  `proEtaleRingModules`, `proEtaleRingModules_hasDerivedCategory`, and
  `proEtaleRingModules_hasKInjectiveResolutions`. It is used for arbitrary
  ring-sheaf module categories and instances, not its constant-ring specialization.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective:
  `Functor.rightDerivedFunctorObjQIso` and canonical `rightDerivedFunctor`.
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction:
  `Adjunction.mapHomologicalComplex`, `Adjunction.mapHomotopyCategory`.

Stated proof dependencies are imported: `ProEtaleImmersionLimitPreservation`,
`ProEtaleRingedOpenComparison`, `RingedTopoiModuleAdjunctionRepair`,
`RingedSiteKInjectiveResolutionsOfUniverses`, `KInjectiveTotalDerived`,
`ExactFunctorDerivedFunctor`, the upstream right-derived Comp and termwise
homotopy adjunction modules. The Mathlib exact-functor factorization and
K-injective Hom theorem are reached by the public imports. The size convention
is metatheoretic and adds no declaration.

Source read: local Stacks proetale.tex at lemma-closed-immersion (09AA),
lemma-closed-immersion-complement-retrocompact-exact (09BM),
lemma-open-immersion (09BN), lemma-ses-associated-to-open (09AH). In particular
09BM and 09AH require precisely the stated quasi-compact open complement.
No Noetherian or qcqs hypothesis on X is needed here. The source theorem's
qcqs filtered-colimit conclusion is not part of this item.

Edge cases checked mathematically before writing:

- Z empty: the open is all X, its unit is invertible, so H and i!_0 vanish.
- U empty, including a nonreduced closed subscheme with full support: the open
  unit has zero target and H is the identity. The closed counit and supported
  unit are isomorphisms by 09AA/09AH; no equality of scheme structures is assumed.
- Empty X: the same constructions apply in the zero module categories.
- Zero coefficient ring and zero module: kernels, exact descent and all
  counit formulas remain meaningful; no nonzero hypothesis is present.
- Nonconstant and infinite coefficients: B is arbitrary, and every action
  and morphism is retained by the recorded ringed functors.
- Truly unbounded complexes and arbitrary K-injective resolutions: integer
  grading throughout, and the last formula quantifies over every resolution,
  including the identity resolution of an already K-injective complex.
- Site object and morphism universes remain different. No equality of them
  is imposed to use the module or derived APIs.

Searches for existing statements/constructions:

- `msearch.py ... leanfinder "right adjoint to closed immersion direct image
  module sheaves as inverse image of the kernel of the open unit"`: 8 hits,
  including Scheme.kerAdjunction and scheme structure-module restrict/pushforward
  adjunctions. None gives the arbitrary pro-etale ring-sheaf support adjoint.
- `msearch.py ... loogle "CategoryTheory.Adjunction,
  CategoryTheory.Limits.kernelFunctor"`: 0 hits; kernelFunctor unknown.
- `msearch.py ... grep "sectionsWithSupport|supportKernel|kernelFunctor"
  CategoryTheory`: 0 hits.
- `rg` in the upstream WeilConjectures tree and project lean/Sheaf for
  `RingedOpenClosed|ringedOpenClosed|supportKernel|closedKernel|iShriek|closedSupport`:
  finite-coefficient support constructions and constant-ring closed adjunctions
  exist, notably ProEtaleIntrinsicClosedSupport/ClosedAmbient. They require
  constant finite coefficients (the latter also Noetherian X) and do not state
  this arbitrary-B theorem. They were read and not copied as new notions.
- Upstream `rg` for the exact item id: no hit.
- `rg` for all new declaration names in Mathlib's CategoryTheory, upstream
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no existing
  declaration of these names. Generic categorical kernels and the canonical
  right-derived comparison are used directly.
- Current server source was read with `scompile.py --source` for
  ProEtaleRingedOpenComparison, ProEtaleOperations, and the recorded
  ProEtaleConstantRingOperations wrapper, since local sources can lag.

No statement dispute or mathematical node fault found.

## Second reading by Q42

A separate clause-by-clause pass was made with the node and final Lean file
open. No second agent was started, as required by the dispatcher brief; the
maintainer's independent review remains independent of this worker.

This pass found that bare existence of derived adjunctions would not identify
their counits. Explicit closed and open counit formulas were added. It also
found that a formula only on K-injective I should explicitly cover a resolution
of arbitrary K; the concrete `ringedClosedKernelResolutionIso` and the final
formula now quantify over every `r : K ⟶ I` with `QuasiIso r` and K-injective I.
The inclusion is matched to the ordinary counit by an equality of natural
transformations, not just an unspecified supported-object isomorphism.
The open extension functor uses the equivalence to the recorded slice module
category; its input remains modules over the actual inverse-image ring.

All auxiliary additivity and exactness binders are existential conclusions,
not additional mathematical hypotheses. There is one postponed theorem,
matching this DAG node, with the complete nine-step proof plan in its docstring.
The helper definitions contain no `sorry`, no choice from mere existence, and
no extra hypothesis. No statement correction or dependency module is supplied.
