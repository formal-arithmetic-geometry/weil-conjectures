## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleDerivedSupportAdjunction` states
`AlgebraicGeometry.ProEtale.finiteSupportedH_derivedAdjunction`, with one `sorry` proof.
It states the complete conditional lemma, including the sheaf counit and the actual
canonical comparison identifying the derived counit. It defines no replacement category,
functor, coefficient action, unit, or derived operation. The mathematical statement is
unchanged. Its historical id does not request a distinguished triangle; none is added.

The previous failure confused Q25's completed stage-1 split with a completed stage-2
statement. The current node has the eight-step proof split and no Lean record. This
packet supplies the missing record and module, so it changes the item's node.

Hypotheses and conclusions, in the order of the natural statement:

| Node clause | Lean rendering |
| --- | --- |
| T is a scheme, locally Noetherian and quasi-compact | `{T Z U : Scheme.{u}}`, `[IsLocallyNoetherian T]`, `[CompactSpace T]` |
| Closed immersion i and complementary quasi-compact open immersion j | `i : Z ⟶ T`, `j : U ⟶ T`, `[IsClosedImmersion i]`, `[IsOpenImmersion j]`, `[QuasiCompact j]`, and `hU : Set.range j = (Set.range i)ᶜ` |
| A finite ring, possibly noncommutative, with discrete topology | `A : Type (u + 1)`, `[Ring A]`, `[Finite A]`, `[TopologicalSpace A]`, `[DiscreteTopology A]`; no `CommRing` binder |
| Left modules over the specified pro-etale coefficient sheaf | `FiniteCoefficientModules S A`, the published `ringedSiteModules` over `finiteCoefficientRingSheaf S A` |
| Ordinary unbounded derived categories and localization | `FiniteCoefficientDerivedCategory S A`, `DerivedCategory.Q`; all complexes have shape `.up ℤ` |
| F(N) = kernel of the actual open unit | The existing `finiteSupportedKernel j A`; its object is literally `kernel ((finiteModuleAdjunction j A).unit.app N)` |
| H(N) = i*F(N) | The existing `finiteSupportedH i j A`, definitionally `finiteSupportedKernel j A ⋙ finiteCoefficientModulePullback i A` |
| Exact closed pushforward | `[PreservesFiniteLimits (finiteModulePushforward i A)]` and `[PreservesFiniteColimits (finiteModulePushforward i A)]`; additivity is already the published instance |
| Fully faithful closed pushforward | `[(finiteModulePushforward i A).Full]` and `[(finiteModulePushforward i A).Faithful]` |
| j* is restriction | `hRestriction`: a ring-presheaf comparison `d` fixing constant sections and additive equivalences `rho N W`; their semilinearity, naturality in W and N, and the equation identifying the specified open unit with the first-projection restriction are explicit |
| Open restriction of every closed direct image vanishes | `hVanishing`, quantified over every `M : FiniteCoefficientModules Z A`, with `IsZero` of the actual open pullback of the actual pushforward |
| Closed unit is invertible on every supported sheaf | `hSupported`, quantified over every N; `IsZero (j*.obj N)` implies `IsIso ((finiteModuleAdjunction i A).unit.app N)` |
| Supported-unit isomorphism for F | `theta : finiteSupportedKernel j A ≅ finiteSupportedH i j A ⋙ finiteModulePushforward i A`, with each `theta.hom.app N` equal to that very closed unit |
| Sheaf adjunction | `adj : finiteModulePushforward i A ⊣ finiteSupportedH i j A` |
| Sheaf counit is inverse supported unit then kernel inclusion | `adj.counit.app N = theta.inv.app N ≫ kernel.ι ((finiteModuleAdjunction j A).unit.app N)` for every N |
| Total right derived functor RH and its comparison | Existential `RH` and natural transformation `beta : H.mapHomologicalComplex (.up ℤ) ⋙ Q ⟶ Q ⋙ RH`, with `RH.IsRightDerivedFunctor beta (HomologicalComplex.quasiIso ... (.up ℤ))` |
| H(I) is K-injective for every K-injective I | `∀ I [I.IsKInjective], CochainComplex.IsKInjective ((H.mapHomologicalComplex (.up ℤ)).obj I)` |
| RH(Q_TI) = Q_ZH(I) by the canonical comparison | `IsIso (beta.app I)`; its domain is exactly `Q_ZH(I)` and codomain exactly `RH(Q_TI)` |
| Termwise closed pushforward descends and is left adjoint to RH | `derivedAdj : (finiteModulePushforward i A).mapDerivedCategory ⊣ RH`; Mathlib's `mapDerivedCategory` is the actual termwise descent |
| Q_T i_*H(I) = i_*^D RH(Q_TI) by the canonical comparisons | The isomorphism `c` has exactly these source and target objects. Its hom is explicitly `mapDerivedCategoryFactors.inv.app (H(I)) ≫ i_*^D.map (beta.app I)` |
| Derived counit is the localized termwise supported-kernel map | `c.hom ≫ derivedAdj.counit.app (DerivedCategory.Q.obj I) = DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)`; this chain map has degree-q component `adj.counit.app (I.X q)`, already normalized by the sheaf-counit equation |

The equalities of derived objects in the prose are expressed as isomorphisms under
exactly the specified comparisons, rather than literal equality of localization objects.
No arbitrary comparison or rescaled adjunction is substituted. The universal property
is the standard right-derived functor property at the complex localization; the
homotopy-localization version in the recorded total-derived dependency is equivalent,
since the termwise additive functor already factors through the homotopy quotient.

Dependency declarations used (the full source signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`, and
  `finiteCoefficientModules_hasDerivedCategory` in namespace `AlgebraicGeometry.ProEtale`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleBaseChange`,
  `Scheme.proEtaleSheafInverseImage`, and the direct-image/site constructions.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`: `finiteCoefficientModulePullback`,
  `finiteCoefficientModulePullback_additive`, `finiteCoefficientModulePullback_exact`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction`: `finiteModulePushforward`,
  `finiteModuleAdjunction`, `finiteModuleAdjunction_existsUnique`, and
  `finiteModulePushforward_additive`. The adjunction is uniquely normalized by the
  small-model module-Kan transpose and works for noncommutative finite rings.
- `Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex`: `finiteSupportedKernel`,
  `finiteSupportedH`, and their additive instances. Only these existing constructions
  are used; its short-exact-sequence theorem and its extra hypothesis hB are not used.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation`:
  `Scheme.proEtaleOpenComposition` and `Scheme.proEtaleOpenSectionProjection`.
  These two site helpers are coefficient-independent. Its commutative-coefficient
  theorem is not applied to noncommutative A.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`;
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective` and `quasiIso_iff`;
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory` and `Functor.mapDerivedCategoryFactors`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomologicalComplex`, `Adjunction.mapHomotopyCategory`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
- The stated proof-dependency modules are imported without `public`:
  `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
  (`SheafOfModules.isGrothendieckAbelianOfUniverses`),
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
  (`CochainComplex.kInjectiveResolutionFunctor`), and
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
  (`Adjunction.preservesKInjectiveComplexes`). Homotopy/derived triangulations and
  the definition of an exact triangulated functor are supplied by their Mathlib imports.

Two already-landed nodes are added to stmt_deps, as permitted by brief-stage2 section 5:
`lem-exc-proetale-supported-kernel-complex` for its F/H definitions and
`lem-pur-proetale-open-unit-evaluation` for its site-composition/projection helpers.
Neither has a statement/proof dependency path back to this item. No new node or dependency
module is needed. All original stmt_deps remain, and no natural-language statement,
proof step, or proof dependency was edited.

Edge cases checked before writing: Z empty gives F = H = 0 and the zero counit;
U empty gives F naturally isomorphic to the identity and the expected closed equivalence.
The zero coefficient ring gives zero module categories and the formulas still type.
Matrix rings over finite fields are permitted: the proof uses only left-linear maps,
kernels, and coefficient transport, with no interchange of coefficient multiplication.
The complex I may be unbounded in both directions and need not have individually
injective terms; K-injectivity alone is assumed. The coefficient universe u+1 is the
published site/module convention, and the derived Hom universe is u+2. The pro-etale site
retains object universe u+1 and Hom universe u; no equality of these universes is imposed.
The empty schemes and zero complex are not excluded by any nonemptiness binder.

Searches made:

1. `msearch.py`, leanfinder: "Closed pushforward is left adjoint to inverse image of the
   kernel of restriction to an open complement with the derived counit computed on
   K-injective complexes". Eight hits: scheme-module restriction adjunctions,
   `CategoryTheory.Adjunction.derived_counit`/`derived'_counit`, and sheaf-module pushforward
   adjunction infrastructure. None is this normalized finite noncommutative statement.
2. `msearch.py`, loogle: "CategoryTheory.Adjunction.derived_counit,
   CategoryTheory.Functor.mapDerivedCategoryFactors, kernelFunctor". Zero hits; the tool
   reported the unknown identifier `kernelFunctor`. This was not taken as evidence that
   the supported functor was missing: the source search below found and reused it.
3. `msearch.py`, grep: "lowerStarClosedUpperShriekAdjunction|finiteSupportedH|derived_counit".
   Zero Mathlib hits. Direct source searches supply the relevant project hits below.
4. `rg` over the source WeilConjectures and the project's Sheaf tree for the item id,
   `finiteSupportedH`, `lowerStarClosedUpperShriekAdjunction`, and
   `derivedLowerStarClosedUpperShriekAdjunction`. The exact item has no existing statement.
   The upstream closed-immersion module has related fixed-ring sheaf adjunctions;
   I read their docstrings and signatures. They do not state all clauses of this
   conditional lemma in the actual continuous-function ringed-module categories with
   its explicit supported-kernel derived counit. The side source already defines F/H
   in ProEtaleSupportedKernelComplex, which this module imports instead of copying.
5. Read the current blueprint proof of lem-exc-proetale-support-triangle and Q25's
   eight-step split. The source requires computing the ambient right adjoint and
   identifying the first arrow; both are retained, with no support-triangle assumption.

No STATEMENT-DISPUTED finding or mathematical correction is needed.

Validation: the required scompile.py checked this module as a sandbox module and under
its intended library path. Both succeeded (7.7 s and 4.3 s), without errors or warnings.
There was no global build or direct live-source edit.

## Second reading by Q103

Independent maintainer second reading, 2026-10-17, of immutable delivery
0925567b78138c82c138348c05c278b431b6ddaa. This reading was performed after the
worker delivery, using the extracted snapshot, not by its author. The original
section contained only a notice that no worker second reading occurred. This
replacement supplies the actual reading required by H11 and the review brief.

I read the item node, all thirteen statement-dependency nodes, the delivered module
and report, and the exact dependency definitions and declarations in the read-only
Q103 clone and pinned Mathlib. I read both the master support-triangle source and
main-20261015 proof, particularly its first sentence computing the ambient right
adjoint and its final identification of the first triangle arrow. This internal
lemma supplies that adjunction and arrow identification; it does not itself assert
the whole localization triangle. The historical identifier does not add a clause.

Clause-by-clause reading:

- The scheme variables, local Noetherian class and CompactSpace give exactly a
  Noetherian T. Closed/open immersion classes, QuasiCompact j, and hU give the
  closed immersion and quasi-compact complementary open. CompactSpace carries no
  Hausdorff assumption. Z and U have no additional finiteness hypotheses.
- Ring A and Finite A allow all finite rings, including noncommutative and zero
  rings. The discrete topology is the coefficient convention, not a restriction
  on the underlying finite ring. No CommRing or Nontrivial binder is present.
- FiniteCoefficientModules is ringedSiteModules over finiteCoefficientRingSheaf:
  sheafified continuous functions on connected components, with left module
  actions. FiniteCoefficientDerivedCategory uses the ordinary unbounded derived
  category and DerivedCategory.Q, not a constructible subcategory or substitute site.
- finiteSupportedKernel has object kernel of the actual finiteModuleAdjunction j A
  unit, and its maps are kernel.map. finiteSupportedH is literally its composite
  with finiteCoefficientModulePullback i A. Those are reused definitions.
- The two finite-preservation instances encode exactness of i_*; Full and Faithful
  encode full faithfulness. Its published additive instance is available.
- hRestriction spells out restriction in the coefficient categories: d preserves
  constant scalars, rho is additive and semilinear over d, both object and module
  naturalities hold, and the actual open unit is restriction along the published
  first-projection map. This explicates the node's restriction hypothesis; it does
  not assume a support theorem or the desired derived adjunction. The commutative
  open-evaluation theorem is not applied to the noncommutative coefficient ring.
- hVanishing quantifies over every closed module sheaf. hSupported quantifies over
  every ambient module sheaf and uses its actual closed unit. They match the two
  remaining assumptions exactly.
- theta is a natural isomorphism whose hom components are explicitly the supported
  closed units. adj is i_* left adjoint to H, and its counit is theta inverse
  followed by the actual kernel inclusion. Thus the sheaf arrow is normalized.
- RH and beta satisfy Mathlib's IsRightDerivedFunctor for localization of all
  integer-indexed complexes at quasi-isomorphisms. Its left Kan universal property
  is the node's total-right-derived universal property; passing through the
  homotopy quotient gives the equivalent formulation of the cited dependency.
- The quantifier over I assumes only IsKInjective. It asserts K-injectivity of H(I)
  and invertibility of beta_I, which expresses RH(QI) = QH(I) by that comparison.
- mapDerivedCategory is the exact termwise descent of i_*. derivedAdj is its
  adjunction to RH on the full derived categories.
- c identifies Q(i_*H(I)) with i_*^D RH(QI). Its hom is exactly the inverse
  mapDerivedCategoryFactors component followed by i_*^D(beta_I). The final
  equation c.hom followed by the derived counit equals Q of the termwise adj.counit.
  Reading Adjunction.mapHomologicalComplex shows its degree-q map is precisely
  adj.counit at I.X q. Together with the earlier counit equation this proves that
  every arrow clause in the node is stated, not merely an unspecified isomorphism.

Dependency and proof checks: the original eleven statement dependencies remain;
the two additions name already published F/H constructions and the open-site helpers.
Neither dependency's substantive theorem is used as an extra assumption. The general
inverse-image record now points to ProEtaleInverseImage; the finite-ring adjunction
is the published finiteModuleAdjunction, uniquely determined by its small-model Kan
transpose. Its choice is therefore not a hollow arbitrary adjunction. The actual
coefficient inverse-image and direct-image maps retain scalar actions. The module
contains no definitions, axioms, local proofs, local notation or local instances;
its only theorem proof is one sorry. Both docstrings cite source places and the
blueprint id; the theorem docstring follows all eight proof steps.

I checked the source statements in derived.tex: lemma-adjoint-preserve-K-injectives
(08BJ), lemma-K-injective (070I), lemma-K-injective-defined (070Y),
lemma-enough-K-injectives-implies (070K), and lemma-right-derived-exact-functor
(015F); and injectives.tex: theorem-K-injective-embedding-grothendieck (079P) and
remark-existence-D (079Q). Their hypotheses fit the eight-step argument. In order:
the open-unit calculation kills the kernel on U; kernel factorization and full
faithfulness give the sheaf adjunction; its termwise extension preserves
K-injectivity; Grothendieck module sheaves have K-injective replacements; additivity
preserves cone and shift formulas; the three Hom bijections give the derived
adjunction; localization extends naturality; transposing the identity gives the
stated derived counit. The elementary steps supply their arguments rather than
citing an unprovided support theorem. The universe-general Grothendieck interface
and the small-model transport supply the needed size hypotheses.

Edge cases: empty T, Z or U, zero modules and the zero complex are allowed. For an
empty closed part H vanishes; for an empty open part the kernel is naturally the
identity. The zero coefficient ring and finite matrix rings are covered. There is
no characteristic restriction, termwise injectivity requirement, boundedness or
constructibility condition. Scheme universe u, site object universe u+1 and Hom
universe u are preserved; coefficients and module sections are in u+1 and the
standard derived localization uses its larger Hom universe. No silent equality of
site universes is imposed.

Independent searches used rg for sectionsWithSupport, kernel.*unit, kerAdjunction,
finiteSupportedH and closed-support adjunction names in pinned Mathlib, the source
WeilConjectures tree, and the Q103 Sheaf/WeilConjectures trees. I opened the related
ClosedImmersion declarations in the group clone's framework: their fixed-value
Sheaf (ProEt.topology X) (ModuleCat R) categories differ from the actual ringed-site
module categories here. Mathlib's Scheme.kerAdjunction concerns ideal subschemes;
the etale supported-kernel module concerns another site. None states this complete
normalized finite-ring theorem. Existing finiteSupportedKernel and finiteSupportedH
are reused. The worker report also records its three search kinds. No duplicate
notion is introduced. Traversing statement and proof edges from the item with
snapshot records overriding clone context found 497 reachable nodes, no missing
node and no cycle. No statement_change is present or needed, so no correction
citer audit is applicable.

Mechanical checks: lean.statement equals the source signature verbatim (up to the
excluded proof delimiter); every binder/universe is explicit with autoImplicit
false; no line exceeds 100 characters; the primary declaration/module/file record
is consistent. No new node or dependency module is delivered. No helper or
universe repair is required.

Compiler reproduction: the prescribed scompile.py was run on the immutable snapshot
module, not a rewritten copy. It exited 0 with no diagnostics: sandbox
Sheaf/Stage2/Sandbox0.lean, 5.8 s; intended library
Sheaf/AlgebraicGeometry/ProEtaleDerivedSupportAdjunction.lean, 15.7 s. The installed
wrapper identifies itself as server-only dated 2026-10-17 and invokes the private
server side overlay with wire confirmation. Thus the brief's older local-overlay
implementation could not be exercised; this is successful wrapper/server evidence,
not a claim of a local run. No direct SSH command, global build, delivery, merge,
git mutation or project-clone edit was performed.

Finding and disposition: H11, the original second-reading text was a placeholder.
Replace the complete report with this version, preserving the Worker report.
No mathematical, signature, construction, dependency or compilation defect was
found. The delivery is correct in substance; FIX is solely this report repair.
