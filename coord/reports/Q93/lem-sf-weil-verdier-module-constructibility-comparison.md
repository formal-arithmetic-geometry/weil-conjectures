## Worker report

The new module `Sheaf.Paper.NativeModuleConstructibilityComparison` states
`AlgebraicGeometry.ProEtale.nativeModuleConstructibilityComparison`. Its sole postponed
proof is this named theorem, with all seven DAG proof steps in its docstring. The remaining
declarations are actual constructions or the projection of the existing realization theorem;
none chooses data from an undetermined existence assertion. The normalized ring realization
is uniquely determined by its finite-field section formula.

Hypotheses and clauses, in order:

* Finite field k₀: `(k₀ : Type u) [Field k₀] [Finite k₀]`. The algebraic closure is
  `(k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k]`. Primality and the excluded
  characteristic are `[Fact ℓ.Prime]` and `hℓ : ℓ ≠ ringChar k₀`.
* The coefficient field and its extended topology are the recorded `PadicAlgCl ℓ`;
  `Profinite.padicAlgClRingObj ℓ` is precisely the finite-subextension condensed ring.
  `condensedRingObj ... T` supplies R_T. The native B_T is `adicConstantSheaf ℓ T`.
* Every site is `Scheme.ProEt.topology T`. Its object universe is u+1 and its morphism
  universe is u; scalar groups and sectionwise modules have universe u+1. The old
  internal/sectionwise equivalence and sectionRingSheaf are instantiated explicitly at
  these three universes, without equating the two site universes. The ordinary derived
  localization is `HasDerivedCategory.standard` in u+2. Universe polymorphism implements
  the metatheoretic size convention.
* `nativeModuleCoefficientIso` selects the existing normalized theta family from
  `locallyFiniteCoefficientRing_realization`. Its ring-map instance is the existing
  theorem's first projection. No arbitrary coefficient isomorphism is a hypothesis.
* `AdicSheaf ℓ T` is exactly the native internal-module presentation in sheaves of
  `WeilCoefficients ℓ`, hence of Omega-vector spaces. `NativeOrdinaryModules` is literally
  `ringedSiteModules` over `sectionRingSheaf` reconstructed from R_T, not another private
  category or a category of modules over discrete constant Omega.
* The existential E is an equivalence at the given separated finite-type T. Its first
  conjunct fixes the actual
  forward functor to `nativeToOrdinaryModules`: `AdicSheaf.forgetAb`, followed by
  `Mod.comap theta.hom`, followed by the existing `sectionModuleEquivalence.functor`.
  Thus r acts on a native module by theta(r), and the inverse transports with theta inverse
  and recovers its Omega-scalar action by constants. The second conjunct is equality of
  the entire functors to abelian sheaves, including their maps and restrictions.
* Exactness, preservation of kernels and cokernels in both directions are expressed by
  `PreservesFiniteLimits` and `PreservesFiniteColimits` for the forward and inverse functors.
  These say nothing incorrect about sectionwise cokernels; the target category uses
  Mathlib's sheafified cokernels.
* The next clause is the natural isomorphism of restriction functors. Ordinary restriction
  is the recorded `CondensedRing.upperStar`, expressed through the existing sectionwise
  equivalence. Native restriction is the recorded `adicUpperStar`. The clause quantifies over each
  immersion h : Z to T, then over each specified cover of Z and each member. It also
  asserts IsEquivalence for the canonical functors on Z and on those members, and supplies
  the restriction comparison between Z and each member. Thus the ambient equivalence is
  asserted in precisely the node setting; the local comparisons include members which
  need not themselves be finite type.
* On each specified covering member V, for each finitely presented scalar P, the
  local-model clause gives an r : Nat and an isomorphism between the image under the
  canonical equivalence of `Mod.finiteFree (adicConstantSheaf ℓ V) r` and
  `ordinaryScalarModel ... P`. This is exactly the correspondence of models under an
  equivalence, equivalently the isomorphism after applying its inverse. The converse
  quantifies over every r and produces a finitely presented P with this isomorphism. `ordinaryScalarModel` uses exactly
  `finiteConstantScalarExtension`, so its tensor is over the scalar constant sheaf and
  uses the canonical scalar map. Scalar modules are the dependency's internal modules
  in Ab over `scalarRingObj`, the existing encoding of ordinary Omega-modules.
* For every immersion h : Z to T and every fixed cover 𝒰 of Z the next iff uses `HasFiniteConstantLocalModelOnCover ... 𝒰`
  and native trivializations on exactly `𝒰.f i`. The finite rank is inside `forall i`,
  so it may vary by member. The following iff quantifies over a fixed
  `Scheme.Stratification T` and uses exactly its domains and immersions on both sides.
  Thus neither the cover nor the stratification is replaced during comparison.
* The theorem binds the geometric hypotheses once: `T.Over (Spec (CommRingCat.of k))`,
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` of its structure map say precisely
  separated finite type over k. The predicate iff is the recorded
  `IsAdicConstructibleSheaf` versus `IsConstantModelConstructible`, reading the ordinary
  object through the existing sectionwise equivalence. No Noetherianity, reducedness,
  connectedness, smoothness or equidimensionality assumption is added.
* The final clause uses that same fixed T and an equivalence D of ordinary
  `DerivedCategory` localizations. Its first natural isomorphism factors the termwise
  `mapHomologicalComplex` through `DerivedCategory.Q`; the next compares every
  `homologyFunctor`. The support iff quantifies over every pair a,b : Int and every degree
  outside [a,b]. Finally the bounded predicate and constructible cohomology in every degree
  are equivalent under D. Since D is an ambient equivalence and the subcategories are full,
  this exactly identifies the full bounded constructible subcategories. The inverse
  direction follows from essential surjectivity and these iff clauses, with no bound fixed
  in advance and no replacement by per-degree numerical equalities.

Dependencies read and used:

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
* `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint` and its ring structures.
* `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`:
  `locallyFiniteCoefficientRing_realization`, including its finite-subextension normalization
  and naturality. The current source already proves it; this delivery uses it unchanged.
* `WeilConjectures.WeilSheaf.LowerShriek`: the recorded native framework public entry,
  especially `AdicSheaf`, `adicConstantSheaf`, `IsAdicLisseSheaf`,
  `IsAdicConstructibleSheaf`, `adicUpperStar`; the source definitions are in its
  Adic.Module, Adic.Constructible and Adic.ConstantSheaf imports. No equivariant derived
  category is silently substituted for the ordinary module derived categories here.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `ModObj` and internal module morphisms.
* `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, literally SheafOfModules.
* `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible` and the bounded convention.
* `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: `scalarRingObj`,
  `finiteConstantScalarExtension`, `HasFiniteConstantLocalModelOnCover`, and its cover
  characterization. This is publicly imported and itself imports the preceding predicate.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `HasDerivedCategory.standard`, `Q`; its TStructure module supplies the bounded predicate.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded sheafified tensor interface.
* Added the already landed node `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
  to stmt_deps: `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
  `InternalAbelianSheafModule.sectionModuleEquivalence`, `sectionRingSheaf`. This is used
  directly, with its actual unchanged-ab-group sectionModuleFunctor, not reimplemented.

All recorded proof-dependency modules have plain imports (when they are not already public
statement dependencies): Mathlib change-of-rings, module sheafification, equivalence/injective
and finite-basis facts, finite presentation, qcqs geometry; CartesianCoefficients for the
canonical coefficient restriction and Adic.ExtensionByZero for native qcqs stratification.
The existing realization publicly imports the native framework and its forgetful comparison.

Edge cases checked before writing: rank 0 is `Fin 0` and gives the zero module, including its
finitely presented zero scalar model; covers need no common rank; the empty scheme admits the
empty partition and empty cover; non-reduced and disconnected schemes are permitted; all
integer bounds are quantified, including a>b (vanishing in every degree), negative bounds and
single-degree intervals. All scheme and scalar universes are explicit. No local notation,
private definition, blanket equality of universes, new axiom, or hollow map is used.

Searches actually run:

* msearch LeanFinder: "Equivalence between internal modules over an algebra sheaf in vector
  space sheaves and sectionwise modules, preserving constructibility". Eight generic hits,
  including ModuleCat.tilde, SheafOfModules.freeHomEquiv, PresheafOfModules.Sheafify.module,
  SheafOfModules.unitHomEquiv and forgetToSheafModuleCat; none states this comparison.
* msearch Loogle: "SheafOfModules, Mod, equivalence". Returned zero hits and diagnostic
  "unknown identifier 'equivalence'"; this is not recorded as proof of absence.
* msearch grep: "equivalence|Equivalence" in Algebra/Category/ModuleCat/Sheaf. Six hits,
  for pushforwardPushforwardEquivalence and its unit formulas and a quasicoherent use;
  these concern equivalences of sites, not the native presentation or scalar constructibility.
* msearch LeanSearch: "Internal modules in sheaves of vector spaces over an algebra sheaf
  equivalent to sheaves of modules over its section rings". Eight generic module/sheaf hits,
  including SheafOfModules, SheafOfModules.mk and Scheme.Modules; no whole-item statement.
* rg in `lean/WeilConjectures` and `lean/Sheaf` for the item identifier, native comparison
  names, module/equivalence paths, and module-comparison concepts. No existing whole theorem.
  Found InternalAbelianSheafModuleEquivalence and reused its existing DAG node and declaration.
  Native AdicSheaf.forgetAb is only a functor, not the required equivalence or constructibility
  comparison. InternalModuleAbEquivalence is over tensor-Z modules in Ab and is not this item.
* Required grep for the item identifier in WeilConjectures returned no hits. Source/docstrings
  of the recorded dependencies and the current blueprint `literature/blueprint/latest/`
  constructibility definition and lem-fix-weil-operations proof were read.

Validation: prescribed scompile.py compiles the module in both module modes with no
errors or warnings; the final scope-narrowed version is checked again before delivery. An initial unused Fintype warning was
repaired by using the mathematically identical `Finite k₀` hypothesis. Initial universe
ambiguities were repaired with explicit instantiation of the existing interfaces; no
mathematical hypotheses changed. No statement correction, new node or dependency repair
is required. Delivery dry-run and final delivery results are recorded by the wrapper.

## Second reading by Q93

This is a worker self-check, not a claim of an independent second agent: the dispatcher brief
forbids starting agents, and the maintainer provides the independent delivery review. I reread
the node and completed module together. All base-field, coefficient, geometric and size
hypotheses have the binders listed above. The result clauses retain the canonical
forward action, the unchanged abelian sheaf functor, exactness in both directions, restriction
comparison, both local-model directions, the specified cover and stratification, the actual
constructibility predicates, and the termwise derived comparison with each interval. The
ordinary sectionwise presentation is the existing equivalence, not a new scalar sheaf or
an arbitrary algebra action. I added explicit equality of underlying abelian-sheaf functors
and the fixed-stratification iff during this reading to make those clauses directly visible.
The final self-check also moved the finite-type T hypotheses to the outside and
restricted auxiliary equivalence assertions to strata and their covering members, instead
of claiming a stronger arbitrary-scheme theorem. No counterexample, dropped clause or
STATEMENT-DISPUTED condition remains.
