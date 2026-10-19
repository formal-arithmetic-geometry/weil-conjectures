## Worker report

The item is stated by `AlgebraicGeometry.ProEtale.CondensedRing.tAdmissible_dualizable_truncations` in `Sheaf.Paper.TAdmissibleDualizableTruncations`. Its proof is the single `sorry` in this delivery. The six proof steps of the DAG are carried into the theorem docstring. The companion definition module has real constructions throughout, with no postponed proof, arbitrary coefficient map, chosen tensor structure or existence-only local-model data. The item's natural statement is unchanged.

Hypothesis-by-hypothesis rendering:

- The arbitrary commutative condensed ring is `Λ : Profinite.CondensedRing.{u}` with `[IsCommMonObj Λ.X]`. The transparent abbreviation is exactly `Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`; its underlying object already has the bundled `MonObj` structure. This is the tensor-abelian ring-object encoding used by the recorded pulled-back-coefficient interface, including general coefficients, rather than just continuous coefficients of a field. The dependency interface now binds general condensed rings; its former continuous-coefficient module is publicly imported and retains every specialized constructor. No second condensed ring definition is introduced.
- `scalarRingSheaf Λ` reconstructs the actual section rings using `InternalAbelianSheafModule.sectionRingSheaf`. `scalarRing Λ` evaluates at the terminal profinite set. Thus R is Γ(*, Λ), not an extra ring or an independently supplied algebra. `scalarSectionMap Λ S` is the ring restriction along `terminal.from S`.
- `hΛ : IsTAdmissible Λ` has the three explicit clauses. `∀ I : Ideal R, I.FG → Module.FinitePresentation R I` is the stated coherence condition. Every finitely presented `N : ModuleCat.{u+1} R` must satisfy `IsPerfectRingComplex ((singleFunctor _ 0).obj N)`. This is exactly existence of a bounded finite-projective complex representing N[0], equivalently a finite resolution by finitely generated projectives: bounded acyclic tails of projectives split, so an arbitrary bounded representative can be replaced by a resolution. No bound uniform in N is required. The third clause is `∀ S : Profinite.{u}, ExtremallyDisconnected S → (scalarSectionMap Λ S).Flat`; compact Hausdorff and total disconnectedness belong to `Profinite` itself.
- `X : Scheme.{u}` is arbitrary. `hX : HasLocallyFiniteIrreducibleComponents X` is `∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (irreducibleComponents U).Finite`. It imposes only the Zariski-local component condition, with no noetherian, affine or quasi-compact assumption.
- `LisseAmbient Λ X` is literally `DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u+1}) (condensedRingObj Λ.X X))`. The ring is the recorded `condensedRingObj`, definitionally `(upperStarFromPoint X).obj Λ.X`; its monoidal structure is transported by that functor. `Mod` is the internal presentation of the very module sheaves specified by `ringedSiteModules`, via the recorded `sectionModuleEquivalence`, not another coefficient category. The derived monoidal structure is the published ordinary K-flat derived tensor of `ModuleObject.Derived.Tensor`; its unit is the coefficient module in degree zero.
- `dualizableProperty Λ X K` is `Nonempty (HasRightDual K)`. `HasRightDual` includes an actual right dual and `ExactPairing`, with evaluation, coevaluation and both triangle identities for that existing derived monoidal structure.

Clause-by-clause rendering:

- The first conjunct quantifies over every ambient K with `dualizableProperty Λ X K` and every integer n. It asserts the same property for `(DerivedCategory.TStructure.t.truncLE n).obj K` and `.truncGE n`, so the functors are exactly the ambient standard truncations.
- The second conjunct gives `h : (dualizableProperty Λ X).IsTriangulated` and `HasRestrictedStandardTStructure Λ X h`. The latter uses the canonically inherited shift and triangulation on the full subcategory, then requires an actual `TStructure` with `t.le n K ↔ DerivedCategory.TStructure.t.le n K.obj` and the analogous `ge` equation for every n and K. These are precisely the restriction of the ambient standard t-structure, with no unrelated t-structure supplied as input.
- The third conjunct says for every module sheaf M that `M[0]` is dualizable if and only if `HasScalarLocalModels Λ X M`. The ordinary heart is module sheaves in degree zero; thus both heart inclusions are stated.
- `HasScalarLocalModels` requires an actual `Scheme.Cover.{u} Scheme.proetalePrecoverage X`. For each member i separately, it existentially quantifies `N : ModuleCat.{u+1} R` with `Module.FinitePresentation R N`, and an isomorphism between the actual restriction `upperStar Λ.X (U.f i)` of M and `scalarModuleOn Λ (U.X i) N`. The scalar module is constructed by the existing discrete constant module functor, `changeOfRings` along `constantScalarMap`, the recorded sectionwise/internal equivalence, and the actual `upperStarFromPoint`. The coefficient arrow is the counit of `constantSheafAdj` at Λ, hence the canonical constant-section map. Monoidal inverse image identifies this construction with Λ_X tensor over the discrete constant R of the discrete constant N. The sheafified ordinary tensor is used, not a completed tensor or an arbitrary local comparison map.
- The final conjunct states `HasScalarLocalModels` for `((DerivedCategory.homologyFunctor _ q).obj K)` for every dualizable K and every integer q. These are the cohomology sheaves of the very same ambient derived category.

Dependency declarations used (module and name):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its opens and open subspaces.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`, `Scheme.proetalePrecoverage`, `Scheme.Cover`.
- `Sheaf.Topology.ProfiniteCondensedRing`: the repaired `Profinite.CondensedRing` input abbreviation, publicly reexporting `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`; no specialized coefficient constructor is substituted for Λ.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`, and the transported commutative ring structure.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, as identified with internal `Mod` by the recorded `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence.sectionModuleEquivalence`; that module also supplies `sectionRingSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`; `DerivedCategory.TStructure.t`, its standard truncations and `homologyFunctor` come from the corresponding TStructure imports.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with the scalar action obtained from the specified ring map.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`: `DerivedCategory.IsPerfectRingComplex` with its bounded finite-projective-model definition.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`: `commutativeSiteConstantModuleFunctor`. Its object and morphism universes are independent and retain the profinite site sizes; its original constant-presheaf/sheafification construction is used verbatim.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: `SheafOfModules.changeOfRings`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`: `CondensedRing.upperStar` for actual identified-coefficient restriction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`: the ordinary derived monoidal structure, computed by K-flat resolutions.
- `Mathlib.CategoryTheory.Monoidal.Rigid.Basic`: `HasRightDual` and `ExactPairing`.

The stated proof-dependency modules are imported privately: coherent-ring perfect cohomology, perfect-ring classical generation, pro-etale sections-conservativity, the actual alpha isomorphism, and the pro-etale operations module, and `Mathlib.RingTheory.Flat.Basic` (`Module.Flat.lTensor_exact` and `rTensor_exact`). `def-pc-perfect-ring-complex` is already a public import through the definitions. The following proof dependencies have no recorded module on the checked base, so their later proof imports are left for the maintainer: `sk-thm-pe-weakly-contractible-basis`, `lem-zl-wcontractible-condensed-scalar-evaluation`, `lem-zl-condensed-dualizable-local-perfect-models`. They are proof-only prerequisites and are not replaced by assumptions in the theorem.

Edge cases checked: the zero condensed ring is permitted; the zero finitely presented module gives the zero local model; the empty scheme makes the local component condition vacuous; a pro-etale cover and its modules can vary and do not have a common rank or amplitude; n and q range over all integers, including negative degrees and truncations outside the support. Schemes need not be quasi-compact or noetherian. The site object universe is u+1 and its morphism universe is u; coefficient values and finitely presented modules lie in u+1, with no forced equality of the site sizes.

Searches: `msearch.py leanfinder` queried standard truncation preservation for t-admissible condensed rings and the discrete-module scalar local model; it returned general truncation functors and general condensed constant-module functors, with no exact theorem or coefficient-model package. `msearch.py loogle` queried `CategoryTheory.Triangulated.TStructure, CategoryTheory.HasRightDual` and returned no hits. `msearch.py leansearch` queried t-admissibility, regular coherence and scalar local models; its hits concern general condensed modules, discreteness and abelian structure. `msearch.py grep` with `tAdmissible|TAdmissible|RegularCoherent|regularCoherent` and with the proposed model names found only an unrelated number-field admissibility instance. Source and side-library `rg` found no matching t-admissibility/model declarations; the blueprint-id grep found no upstream theorem. Searches of the DAG found only this theorem, its proof nodes and consumers, not a coefficient-model definition; `blueprint_refs.py search t-admissible` returned zero blueprint nodes. Source reading found the already published commutative-site constant module functor, so the provisional constant-module reimplementation and its two extra postponed lemmas were removed. The search summaries are reproduced in the new definition node with the exact wrapper output records.

There is no statement dispute or source correction. The previous report of an unchanged N4-reviewed item concerned the stage-1 split; this packet supplies actual stage-2 Lean and preserves the stage-1 review metadata.

## New nodes

`def-zl-t-admissible-coefficient-models` records the missing coefficient-model package in its own module `Sheaf.Paper.TAdmissibleCoefficientModels`. It defines actual section rings and canonical maps, t-admissibility, ordinary scalar local models, the ambient dualizable predicate and the precise restricted-standard-t-structure predicate. Its source is HRS Section 3, Definition 3.3(1), Definition 6.1, Proposition 6.6 and Theorem 6.2(2). Searches described above find no existing definition of this package. Every generic ingredient is reused from its recorded node or Mathlib, including the constant-module functor, internal/sectionwise equivalence, coefficient inverse image, derived tensor, truncation, ordinary perfect complexes and duality. All helpers have source and blueprint docstrings and are listed in the node's Lean declarations. The definitions have no `sorry`. The item adds this node to its statement dependencies; all of its other fields except `lean` remain unchanged.

## Dependency modules

`sk-def-sfb-condensed-ring` receives the module `Sheaf.Topology.ProfiniteCondensedRing`. Its previous primary declaration, `Profinite.isCommMonObj_continuousCoefficientRingObj`, treats only coefficients from a topological commutative ring and does not supply the general condensed-ring input that the node introduces and HRS Theorem 6.2 assumes. The new `Profinite.CondensedRing` is a transparent abbreviation for the existing category of ring objects in tensor-abelian sheaves on the coherent profinite site. This is the node's equivalent ring-object encoding, with arbitrary noncommutative rings allowed before the theorem imposes commutativity. The old module is publicly imported, so all its named continuous-function, postcomposition, adic, subfield and valuation-subring constructions and commutativity instances remain available through that import. The repaired record lists only `Profinite.CondensedRing`, the declaration owned by the new module. Only the dependency's `lean` field changes, with a note explaining the defect and repair. The coefficient-model definitions and main theorem actually use the repaired bundled input type and its underlying ring object, so no topological realization is imposed on general Λ.

Validation: `scompile.py N7 lem-zl-t-admissible-dualizable-truncations` compiled all three final modules separately in dependency order, including their sandbox and library checks, with exit 0 and no errors or unexpected warnings. The sole postponed theorem is `AlgebraicGeometry.ProEtale.CondensedRing.tAdmissible_dualizable_truncations`; every delivered definition is real data. Compilation used only the prescribed wrapper and its unchanged per-file limits.

The first delivery preflight rejected imported declarations listed as declarations owned by the dependency module. The metadata now lists only its actual new abbreviation; the Lean files are unchanged.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer fix (cc reviewer, 2026-10-18)

One definition per notion (H4). The landed node det-def-sfb-constructible-local-model
(module Sheaf.AlgebraicGeometry.FiniteConstantLocalModel, on the base) already defines the heart
condition of this item word for word: a pro-etale cover with finitely presented Λ(*)-modules P_i
and M|_{U_i} ≅ Λ_{U_i} ⊗_{Λ(*)} P_i, the tensor taken along the inverse image of the
constant-sheaf counit (`HasFiniteConstantLocalModelOnCover`, `finiteConstantScalarExtension`,
`scalarCoefficientHom`). The delivery built a second copy (`constantScalarMap`,
`condensedScalarModule`, `scalarModuleOn`, and the body of `HasScalarLocalModels`). Likewise
`CategoryTheory.IsDualizable` (WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic) is
exactly `Nonempty (HasRightDual K)`.

Changed: in Sheaf.Paper.TAdmissibleCoefficientModels the three duplicate constructions are removed;
`HasScalarLocalModels Λ X M` is now the transparent abbreviation
`∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, HasFiniteConstantLocalModelOnCover Λ.X M U`, and
`dualizableProperty Λ X K` is `IsDualizable K`. The node def-zl-t-admissible-coefficient-models cites
[det-def-sfb-constructible-local-model] in its statement and stmt_deps instead of the constant module
functor node, and its lean.declarations lose the three removed names. The item module, its theorem
statement and lean record are unchanged; the dependency module Sheaf.Topology.ProfiniteCondensedRing
is unchanged. All three modules compile with nt_compile.py (rc 0, no errors).
