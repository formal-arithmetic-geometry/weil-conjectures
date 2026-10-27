## Worker report

Item: `lem-sfb-admissible-scalar-model-cohomology`, stage 2, Q143.
Module: `Sheaf.Paper.AdmissibleScalarModelCohomology`.
Main declaration:
`AlgebraicGeometry.ProEtale.AdmissibleScalarModel.admissible_scalar_model_cohomology`.
The theorem has a `sorry` proof. All four helper definitions have real data, and are
listed in `lean.declarations`. The existing node changes only in `lean`; its accepted
statement, dependencies, and proof are unchanged. No new nodes or dependency repairs.

Read the current blueprint source
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-ctf.proof.md`,
paragraph (2), and all statement-dependency statements and recorded interfaces. The module
carries all seven steps of the node's expanded proof in its theorem docstring. The theorem
identifies cohomology objects, not two complexes or derived objects, so its natural
cohomology isomorphism is the stated conclusion itself, not a substitute for a required
isomorphism between complexes.

The scalar realization is exactly the existing `finiteConstantScalarExtension Γ W`,
not a new realization functor. It is `(scalarConstant W).mapMod (scalarRingObj Γ)` followed
by `Mod.extendScalars (scalarCoefficientHom Γ W)`. Thus it takes a genuinely constant
scalar module and tensors along the fixed canonical scalar ring map.

The coefficient modules use the existing internal-module encoding in tensor abelian
sheaves, already used by the recorded local-model node. This is equivalent to ordinary
sectionwise module sheaves, with the identical underlying abelian sheaf, via
`InternalAbelianSheafModule.sectionModuleEquivalence`. Similarly an internal module in
abelian groups is an ordinary module: `ordinaryScalarModule` applies the existing
`InternalAbelianSheafModule.ordinaryModule` with its actual tensor action. It introduces
no arbitrary ring, module action, or equivalence witness. `scalarRing` applies the existing
`commMonToRing` to `scalarRingObj Γ`; its carrier is literally Γ evaluated at the point,
and its multiplication and unit are those of that existing scalar ring object.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| An algebraic closure of Q_ell | The existing `PadicAlgCl ℓ`, used by the recorded algebraic-closure coefficient |
| Finite E/Q_ell embedded in that closure | `E : PadicAlgCl.FiniteIntermediateField ℓ`; the type contains precisely finite intermediate fields, with their induced norm topology |
| O_E and E as condensed rings | `Profinite.padicIntegersRingObj ℓ E` and `Profinite.continuousMapRingObj E`, using the recorded constructions |
| Finite discrete commutative coefficients | The first universal clause binds `A : Type u`, `[CommRing A]`, `[Finite A]`, `[TopologicalSpace A]`, `[IsTopologicalRing A]`, and `[DiscreteTopology A]`, then uses `continuousCoefficientRingObj A` |
| Every finite ring, without ell-primary restriction | There is no annihilation, characteristic, nontriviality, domain, or field hypothesis on A |
| Qbar coefficient with finite-subextension-valued sections | `Profinite.padicAlgClRingObj ℓ`, literally the recorded construction; not all continuous Qbar-valued functions |
| Z_ell and Q_ell included by E=Q_ell | The bottom finite intermediate field is included in `∀ E`; its ring of integers and field give these two cases |
| Every scheme W | `(W : Scheme.{u})`, with no quasi-compactness, separation, or nonemptiness hypothesis |
| Small pro-etale site | Every realized module and cohomology object is in `Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u+1}) (condensedRingObj Γ W)` |
| Γ_W = p_W^* Γ | The existing `condensedRingObj Γ W`, the underlying object of the recorded `coefficientRing W (Mon.mk Γ)` |
| R = Γ(*) | `scalarRing Γ`, obtained from `scalarRingObj Γ = scalarSections.obj Γ` by the existing internal-to-ordinary ring functor |
| Constant scalar modules in C_W | `finiteConstantScalarExtension Γ W`, using `scalarConstant W` and the canonical `scalarCoefficientHom Γ W` |
| Noetherian R | First conjunct of `Assertions Γ W`: `IsNoetherianRing (scalarRing Γ)` |
| Additive C_W on every module | Existential witness of `(finiteConstantScalarExtension Γ W).Additive` in `Assertions`; it is a conclusion, not a hypothesis |
| Exact C_W on every module | `PreservesFiniteLimits` and `PreservesFiniteColimits` for that same functor; neither is assumed |
| Canonical finite coefficient ring identification | `IsIso (scalarCoefficientHom (continuousCoefficientRingObj A) W)`; this map already has `IsMonHom`, so it is the canonical ring isomorphism from the constant ring |
| Finite C_W(M) identified canonically with the constant M for every M | `∀ M, IsIso ((Mod.extendRestrictAdjunction (scalarCoefficientHom ... W)).unit.app (((scalarConstant W).mapMod ...).obj M))`; this is the fixed natural map m ↦ 1 tensor m, over the ring identification just stated |
| Integral constant-to-coefficient ring map is flat | `ObjectProperty.flat ((Mod.comap (scalarCoefficientHom ... W)).obj (Mod.regular (condensedRingObj ... W)))` in the integral clause |
| Bounded Q_0 of finite projective R-modules | `boundedProjectiveScalars Γ` uses `∃ a b, Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧ ∀ i, Module.Projective R (...) ∧ Module.Finite R (...)`, reading each term by `ordinaryScalarModule` |
| Every H^q(Q_0) finitely presented over R | For every object Q of that full subcategory and `q : ℤ`, `Module.FinitePresentation (scalarRing Γ) (ordinaryScalarModule Γ (Q.obj.homology q))` |
| Termwise ordinary realization | `(finiteConstantScalarExtension Γ W).mapHomologicalComplex (.up ℤ)`, applied to the actual scalar complex |
| H^q(C_W(Q_0)) is isomorphic to C_W(H^q(Q_0)), naturally | `∀ q, Nonempty (boundedProjectiveScalars.ι ⋙ mapHomologicalComplex ... ⋙ homologyFunctor ... q ≅ boundedProjectiveScalars.ι ⋙ homologyFunctor ... q ⋙ finiteConstantScalarExtension Γ W)`; this is an isomorphism of functors on the full category, not independent per-object choices |
| Finite constant local model of the realized cohomology | `HasFiniteConstantLocalModel Γ W` of the termwise realized complex's homology, for every Q and q |
| Torsion or zero cohomology included | No projectivity, torsion-freeness, nontriviality or positive rank condition is imposed on homology |
| Ordinary uncompleted setting; no ambient completeness | All cohomology is `HomologicalComplex.homology` in the ordinary abelian module category; no completion operation, ambient object, or completeness binder occurs |

`boundedProjectiveScalars` is only the full-subcategory domain needed to express naturality
for exactly the bounded finite-projective complexes named by this node. Its bound and term
conditions are the complex-level conditions in the recorded `DerivedCategory.IsPerfectRingComplex`;
it does not redefine perfectness of derived objects. `Assertions` is simply a conjunction
of this node's conclusions, reused in the three concrete coefficient clauses. These are
helpers of this statement, not independent new mathematical notions.

Dependency declarations and sources actually read:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, retaining the
  recorded continuous-function and adic constructions through its public imports.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`, `padicSubfieldCondensedRing`,
  `padicIntegersCondensedRing`, `padicIntegersRingObj`, and their commutativity instances.
  `Condensed.FiniteSubextension` exports the existing coercions for finite intermediate fields.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, and `condensedRingObj`.
- Mathlib `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent alias of Mathlib's `SheafOfModules`.
- Mathlib `Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q`; ordinary uncompleted complex cohomology is used before localization.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: `scalarSections`, `scalarRingObj`,
  `scalarConstant`, `scalarConstant_iso_constantSheaf`, `scalarCoefficientHom`,
  `scalarCoefficientHom_isMonHom`, `finiteConstantScalarExtension`,
  `HasFiniteConstantLocalModel`, and `finiteConstantLocalModel_iff_exists_cover`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite` and its publicly
  exported existing `ObjectProperty.flat`. The latter is used for the internal modules;
  the site is symmetric monoidal, so its two tensor exactness conditions express the
  same flatness as the recorded sectionwise predicate.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, whose exact bound and term conditions specify
  the scalar complexes here before passage to the ordinary derived category.
- Mathlib `Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- Mathlib `RingTheory.Noetherian.Defs`: `IsNoetherianRing` and `isNoetherianRing_iff`.
- Existing conversion interface `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `commMonToRing`, `ordinaryModule`, and `sectionModuleEquivalence`. These perform the
  explicit encoding changes, rather than adding mathematical hypotheses.
- Proof imports include every recorded proof-dependency module that is stated, plus
  Mathlib `PrincipalIdealDomain` (`PrincipalIdealRing.isNoetherianRing`) and
  `ShortComplex.PreservesHomology` (`CategoryTheory.Functor.homologyFunctorIso`, the
  exact Mathlib match of `lem-weil-pbc-exact-functor-complex-cohomology`). The generic
  flat scalar realization, its exactness theorem, flat pullback, constant module inverse
  image comparison, totally disconnected realization, and perfect cohomology theorem
  are imported unchanged from the recorded modules. Their use in the future proof is
  described step by step in the theorem docstring.

Edge cases checked before and after writing:

- Finite zero rings are allowed by `[CommRing A] [Finite A]`; no `Nontrivial A` appears.
- Finite rings of characteristic different from ell and finite rings of mixed prime
  support are included; the earlier continuous-coefficient exactness theorem has an
  ell-primary finite-case restriction, and was not substituted for this statement.
- The empty scheme is allowed. Both its coefficient and constant ring sheaves are the
  unique sheaf, so the finite canonical ring isomorphism remains meaningful.
- Zero scalar modules and the zero complex are allowed. Empty or reversed term intervals
  are not forbidden. Cohomology is quantified over every integer, including outside the
  bounds; its zero module is finitely presented and has the zero constant model.
- Integral perfect complexes can have torsion cohomology, for example the cohomology of
  multiplication by a uniformizer; no projectivity or torsion-freeness is demanded of it.
- All complex morphisms between the bounded finite-projective models occur in the full
  subcategory, so the natural isomorphism does not silently discard noninvertible maps.
- Site objects are in universe u+1 and site morphisms in u, with coefficient groups in
  u+1. No equality of the object and morphism universes was imposed.
- The base finite intermediate field includes E=Q_ell. The algebraic-closure case uses
  the finite-subextension-valued sheaf even for profinite spaces with functions of
  unbounded algebraic degree in the larger continuous-function sheaf.

Searches (all run through the prescribed search wrapper, with raw results in its log):

- LeanFinder: `Exact scalar realization from admissible condensed finite or l-adic
  coefficients commutes with cohomology of bounded finite projective complexes`.
  Eight hits on condensed solid/free objects, AB properties and light condensed modules;
  none states this scheme coefficient theorem.
- Loogle: `Functor.homologyFunctorIso, IsNoetherianRing, Module.FinitePresentation`.
  Zero hits; service reports unknown identifier `Functor.homologyFunctorIso`. Read the
  pinned Mathlib declaration directly in `ShortComplex/PreservesHomology.lean` instead.
- Mathlib grep wrapper: `admissible|Admissible|mapHomologicalComplex.*homology`, subdirectory
  `Condensed`: zero hits.
- LeanSearch: `Exact scalar realization for condensed admissible coefficient rings and
  finitely presented cohomology of bounded finite projective scalar complexes`.
  Eight hits on adic completion, algebra presentation, condensed abelianness and unrelated
  scalar actions; none states the item.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `finiteConstantScalarExtension`, `scalar_model_cohomology`, `Admissible` and `admissible`:
  no existing full statement. Found the existing canonical realization/local-model
  definitions and `Sheaf.Paper.AdmissibleScalarRealizationExact`; read the latter in full
  at its interface. Its Qbar coefficient is explicitly all continuous functions, and
  it lacks this item's perfect cohomology conclusion, so it is not an existing match.
- Checked `dag/lean_names_upstream.json` for scalar-model names. No full statement match.

No `STATEMENT-DISPUTED` issue or source-based statement correction is needed.

Validation: the first `scompile.py Q143 lem-sfb-admissible-scalar-model-cohomology ...`
run compiled both its sandbox and final module paths cleanly. The only subsequent source
change before preflight was to add the explicit Mathlib PID proof-dependency import and
remove two docstring indentation spaces. Dry-run and final delivery validation follow.

## Second reading by Q143

The section delivered under this heading was written by the same dispatcher worker
("a separate second reading by the dispatcher worker"), so it is not an independent
reading (delivery-errors H11). It is replaced by the independent reading of the
maintainer's reviewer. That reading used the node, the blueprint paragraph
det-prop-scalar-six-ctf.proof.md (2), every statement-dependency record and the Lean
module, all open together. The Lean, the node record and the worker report above are
unchanged.

Node clause by clause, with its Lean and the verdict:

- Prime ℓ and fixed algebraic closure: `(ℓ : ℕ) [Fact ℓ.Prime]`. The closure is the fixed
  `PadicAlgCl ℓ` used by every coefficient below. OK.
- Finite E/Q_ℓ inside the closure: `E : PadicAlgCl.FiniteIntermediateField ℓ`, which is
  `{E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) // FiniteDimensional ℚ_[ℓ] E}`. E = ⊥ gives
  Z_ℓ and Q_ℓ. OK.
- Condensed rings [sk-def-sfb-condensed-ring, sk-def-sfb-qlbar-condensed]:
  - O_E is `Profinite.padicIntegersRingObj ℓ E`. Its sections are C(S, O_E) with
    O_E = {|x| ≤ 1} and the topology restricted from Q̄_ℓ.
  - E is `Profinite.continuousMapRingObj E`. This is the E̲ of FiniteSubextension, with
    the restricted norm topology.
  - Q̄_ℓ is the recorded finite-subextension-valued `Profinite.padicAlgClRingObj ℓ`, not
    the all-continuous sheaf.
  - A finite discrete ring is `Profinite.continuousCoefficientRingObj A` with
    `[Finite A] [DiscreteTopology A]`. Its sections are C(S, A), the same construction as
    the node's T̲ with no Type-0 restriction. The landed lem-sfb-admissible-scalar-realization-exact
    uses the same encoding.

  The finite case has no ℓ-primary, nontriviality or field condition. `IsTopologicalRing A`
  is automatic for a discrete ring, so it adds nothing. OK.
- Every scheme W, small pro-étale site, Γ_W = p_W^*Γ [sk-def-pe-site,
  sk-def-sfb-pulled-back-coefficients]: `(W : Scheme.{u})` with no hypothesis. The modules
  live in `Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u+1}) (condensedRingObj Γ W)`, and
  condensedRingObj is the underlying object of the recorded coefficientRing. OK.
- R = Γ(*) and C_W(M) = Γ_W ⊗_{R_W} M_W on ordinary R-modules
  [det-def-sfb-constructible-local-model]:
  - `scalarRing Γ` is commMonToRing of `scalarRingObj Γ = scalarSections.obj Γ`, that is,
    evaluation at the point.
  - C_W is the recorded `finiteConstantScalarExtension Γ W`. It is
    `(scalarConstant W).mapMod ⋙ Mod.extendScalars (scalarCoefficientHom Γ W)`, where
    scalarCoefficientHom is the inverse image of the constant-sheaf counit (a MonHom).
  - Ordinary R-modules are the equivalent internal modules, read by the existing
    `ordinaryModule`. This is the same encoding the recorded local-model node uses.

  OK.
- R Noetherian [def-weil-pbc-noetherian-ring]: `IsNoetherianRing (scalarRing Γ)` in
  `Assertions`. It is a conclusion, for all four coefficient kinds. OK.
- C_W additive and exact: in `Assertions`,
  `∃ (_ : Additive), PreservesFiniteLimits ∧ PreservesFiniteColimits`. Additive is a Prop
  class, so the ∃ is a conjunction. The recorded instance is private, which is why it
  appears this way. OK.
- Finite Γ, canonical monoidal identification Γ_W ≅ constant ring sheaf:
  `IsIso (scalarCoefficientHom (continuousCoefficientRingObj A) W)`, the canonical map
  itself. With `scalarCoefficientHom_isMonHom` this is a ring isomorphism. It is not an
  arbitrary ∃-iso, which is the C3 fault repaired at stage 1. OK.
- Finite Γ, C_W(M) ≅ M_W for every M: `∀ M`, IsIso of the extendRestrictAdjunction unit at
  the constant module (the map m ↦ 1 ⊗ m), restricted to R_W along the identification
  just stated. This is canonical and natural in M. OK.
- Integral Γ = O_E, R_W → Γ_W flat [def-pc-flat-sheaf-modules]:
  `ObjectProperty.flat ((Mod.comap (scalarCoefficientHom …)).obj (Mod.regular …))`.
  - This is Γ_W, regarded as an R_W-module through the canonical map, with tensorLeft and
    tensorRight exact.
  - The monoidal structure on `Mod C R` is the relative tensor ⊗_R (ModuleObjects.Monoidal,
    `monoidalCategory`).
  - ObjectProperty.flat is one of the declarations recorded by def-pc-flat-sheaf-modules.

  OK.
- Q_0 a bounded complex of finite projective R-modules [def-pc-perfect-ring-complex]:
  `boundedProjectiveScalars Γ` is
  `∃ a b, IsStrictlyGE a ∧ IsStrictlyLE b ∧ ∀ i, Projective ∧ Finite` over `scalarRing Γ`.
  It is literally the inner model condition of the recorded `IsPerfectRingComplex`, applied
  to the actual complex. The node needs the actual complex, so this is not a second
  definition of perfectness. OK.
- Every H^q(Q_0) finitely presented [def-sc-finitely-presented-module]: `∀ Q q,
  Module.FinitePresentation (scalarRing Γ) (ordinaryScalarModule Γ (Q.obj.homology q))`.
  This covers every q ∈ ℤ, including degrees outside the bounds. OK.
- Natural isomorphism H^q(C_W(Q_0)) ≅ C_W(H^q(Q_0)): `∀ q, Nonempty (ι ⋙
  mapHomologicalComplex ⋙ homologyFunctor q ≅ ι ⋙ homologyFunctor q ⋙ C_W)`. This is an
  isomorphism of functors on the full subcategory, so it is natural in all chain maps. The
  realization is termwise and there is no completion. This identifies cohomology objects,
  not complexes, so the 2026-10-21 derived-form rule does not apply. OK.
- Finite constant local model, including torsion and zero cohomology:
  `HasFiniteConstantLocalModel Γ W` of the realized cohomology, for every Q and q. There is
  no projectivity, torsion-free or rank condition. OK.

Edge cases:

- Finite zero ring: allowed, there is no `Nontrivial`.
- Empty W: allowed.
- Zero complex, empty or reversed bounds: allowed.
- q outside the bounds: covered.
- Torsion cohomology over O_E: allowed.
- Universes: the site has objects in u+1 and morphisms in u, and coefficients are in
  `Ab.{u+1}`; no extra universe equation is imposed. A finite ring in `Type u` loses no
  generality.

Gates:

- The four helpers (`scalarRing`, `ordinaryScalarModule`, `boundedProjectiveScalars`,
  `Assertions`) have real data or are real Props, and carry source and blueprint
  docstrings.
- The theorem docstring carries all seven proof steps. The only proof is `sorry`.
- The node record changes only `lean`, and `lean.statement` is verbatim in the file.
- The path `Sheaf/Paper/AdmissibleScalarModelCohomology.lean` and the namespace
  `AdmissibleScalarModel` collide with nothing in the side-live tree.
- Duplicate search: the landed lem-sfb-admissible-scalar-realization-exact (Q94) has
  ℓ-primary finite rings, all-continuous Q̄_ℓ and no cohomology clause, so it is not this
  item.

Advisory:

- `continuousCoefficientRingObj` is formally owned by the universe-general module of
  def-weil-pbc-condensed-e-module-category. It is used here, as in the landed Q94 item,
  under sk-def-sfb-condensed-ring's T̲.

No mathematical mismatch was found. Only this section of the report was changed.
