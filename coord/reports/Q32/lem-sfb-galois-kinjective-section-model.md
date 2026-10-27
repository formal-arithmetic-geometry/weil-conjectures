## Worker report

The module `Sheaf.Paper.GaloisKInjectiveSectionModel` states
`AlgebraicGeometry.ProEtale.GaloisKInjectiveSectionModel.galois_kinjective_section_model`
with one `sorry`. All other declarations are real abbreviations, a concrete restriction
homomorphism, and the proposition/specification of this same node. No new independent
notion, dependency repair, statement correction, axiom, or proof is introduced.

Hypothesis and object correspondence:

- The field and separable closure are `k Ω : Type u`, `[Field k] [Field Ω]`,
  `[Algebra k Ω] [IsSepClosure k Ω]`. `Spec (.of k)` is s; the group in the original
  normalized module datum is `Ω ≃ₐ[k] Ω` with the existing Krull topology.
- `h : FieldActionTopos.Normalization k Ω` and
  `e : GeometricSectionsAdjunction.NormalizedModules k Ω h R` are precisely the
  fixed normalized equivalence and invariants adjunction named in the node.
  They are the current recorded dependency's interfaces, not arbitrary functors.
- `R : CondensedBar.Ring.{u}` is `CommMon` of condensed abelian sheaves, so it is an
  arbitrary commutative condensed ring, not only one from a topological ring.
  `R.toMon` is the existing unbundled coefficient datum; the ring on X is exactly
  `condensedRingObj R.X X`, the underlying ring of `coefficientRing X R.toMon`.
  The latter bundled presentation carries a distinct definitional monoid instance;
  using the actual module-pushforward presentation avoids inventing a transport.
- X and its named structure morphism are `(X : Scheme.{u}) (a : X ⟶ Spec (.of k))`;
  `[CompactSpace X] [QuasiSeparatedSpace X]` render qcqs over the field.
- The categories are the actual `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) ...`,
  `Profinite.CondensedAction.Modules R.toMon`, and the existing `ActionModule`.
  `ActionAbelian` and the field/action `HasDerivedCategory.{u+2}` instances are the
  dependency's compatible categorical presentation. `Assertion` supplies standard
  localizations for X-modules, condensed modules and Ab, with derived Hom universe
  u+2 in every case. No equality of site object and morphism universes is imposed.
- F_R and its left adjoint are the dependency's `geometricFunctor e a` and
  `geometricLeft e a`, using actual lowerStar and upperStar. Γ_G is
  `e.invariants.functor`, with the inclusion and transpose normalization already in e.
- `singleton` is `Profinite.of PUnit` in the existing `AsSmall` presentation.
  `singletonEvaluation` composes `Mod.forget` and `sheafSections` at this object.
  `globalSections` is the analogous composition at the final pro-etale test X.
  These are transparent functor compositions of existing definitions, retaining
  sections and forgetting scalars; no second module category or global-section
  construction is substituted. This is the section realization of Hom_R(R,-)
  in the recorded ringed-site hypercohomology convention.
- The geometric test is the original pullback of `h.free` at the singleton. Its
  identification with X^s[P], including all three coordinates, is the dependency's
  `GeometricNormalization.tests`. `geometricRestriction` is the actual presheaf
  restriction along its structure arrow to X, followed by the inverse of the
  dependency's `geometricSection`. It is constructed, not chosen from existence.

Conclusion correspondence (all these fields are inside `Nonempty (Model e X a)`,
not extra hypotheses of the theorem):

- Exactness of ev_*: `evaluationLimits` and `evaluationColimits` give preservation
  of finite limits and colimits. Addition and zero are the underlying module-map
  addition/zero, recorded by the `...Additive` and `...Zero` fields for efficient
  elaboration of termwise complexes. They add no independent mathematical condition.
- The natural additive isomorphism γ is `Model.gamma`. Its invariant-codomain
  normalization is `restriction`: composing γ with the existing fixed-section
  inclusion is exactly `geometricRestriction`. This specifies restriction, rather
  than an unspecified isomorphism. `gluing` says every invariant section has a
  unique preimage under this restriction. Together with `restriction` and γ being
  an isomorphism, its inverse is exactly that unique sheaf gluing.
- Exactness of the specified a^* E_R^{-1} is `leftLimits` and `leftColimits`, with
  its original additive structure. Its underived adjunction is the dependency's
  actual `geometricAdjunction e a`, the composite adjunction with specified unit
  and counit. It is not replaced by an arbitrary adjunction.
- K-injective preservation is `geometricKInjective` and `invariantsKInjective`,
  instances of the existing `Functor.PreservesKInjectiveComplexes` definition.
- K-injective resolutions in the three categories are `sourceResolutions`,
  `condensedResolutions`, and `actionResolutions`. The original `rightDerivedFunctor`
  and `rightDerivedFunctorObjQIso` thus supply the ordinary total right derived
  functors and their canonical computation isomorphisms on I and F(I).
- The normalized comparison is the natural functor isomorphism `comparison` from
  RΓ_X to RF_R ⋙ RΓ_G ⋙ D(ev_*). `canonical` identifies it with the existing
  `rightDerivedFunctorNatIso gamma`, `rightDerivedFunctorCompMapDerivedCategoryIso`,
  and `rightDerivedFunctorCompIso`. These are the universal-unit normalized
  comparisons, not merely an existential derived isomorphism. For the specified
  adjunctions, their identification with the adjunction conjugate, including both
  units and counits, is exactly the imported
  `derivedCompositionAdjunctionNormalization` with identity left compositor.
- `NatIso.mapHomologicalComplex gamma (.up ℤ)` is C(γ). Its components are the
  asserted chain isomorphisms, since the mapHomologicalComplex composition
  comparisons here are the degreewise identities. `Model.resolution` states the
  localized chain formula for every M, every K-injective I and every quasi-isomorphism
  i:M→I. The two rightDerivedFunctorObjQIso factors on the right explicitly identify
  F(I) and Γ_G F(I) with RF(M) and RΓ_G RF(M). Exact singleton evaluation is then
  descended by its existing `mapDerivedCategoryFactors` comparison. No preservation
  of K-injectives by singleton evaluation is assumed or asserted.
- `comparison` is natural on all derived morphisms, and `resolution` quantifies
  over every resolution. Therefore its class intertwines the canonical coordinate
  changes (inverse first computation isomorphism, then the second). Taking the
  identity derived morphism gives changes of resolution and their cocycle. This is
  the requested resolution independence and naturality, not just chain-map
  naturality between a single chosen replacement functor's outputs.
- All complexes are `CochainComplex ... ℤ`. No boundedness, nontrivial ring,
  nonempty X, finite group, or finite cohomological dimension is required.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`: `IsSepClosure` and
  `IsSepClosure.exists_intermediateField_mem` (field convention).
- `Sheaf.Paper.ProfiniteTestObjectFunctor`: `profinite_test_object_functor` and
  existing `profiniteToProEtOf` (through the normalized geometric tests).
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`;
  `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and `Mod.forget`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`; its `UpperLowerStar.Defs`: actual `CondensedRing.lowerStar`,
  `upperStar`, and `upperStarLowerStarAdjunction`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Modules`, `ActionModule`,
  `Invariants`, its inclusion, injectivity/image and adjunction specifications.
- `Sheaf.Paper.GeometricSectionsAdjunction`: `NormalizedModules`, `geometricFunctor`,
  `geometricLeft`, `geometricAdjunction`, `geometricSection`, and geometric test
  normalization; `FieldActionToposCoefficients`: `FieldActionTopos.Normalization`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: recorded ordinary
  unbounded convention, with arbitrary quasi-isomorphic resolutions. On these
  Grothendieck categories we use the already-existing upstream `rightDerivedFunctor`,
  its universal unit, `rightDerivedFunctorObjQIso` and exact-postcomposition API.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `ringedSiteZerothHypercohomologyOfUniverses`, its Hom_R(R,-) global-section convention;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, Q,
  `HasDerivedCategory.standard`; `NatIso.mapHomologicalComplex`: termwise γ.
- Proof inputs are imported with their recorded modules: internal/section-module
  equivalence, ringed-site module category, sheaf epi/local-surjectivity,
  exact condensed-module pullback, adjoint K-injective preservation, Grothendieck
  K-injective resolutions, enough-K-injectives total derivation, exact derived
  factorization, arbitrary-resolution morphism computation and derived composition
  adjunction normalization. The field normalization and finite lowerStar are
  reexported by the public statement dependencies. No proof import cycle was found.

Searches performed:

- msearch.py leanfinder: `Exact singleton evaluation and normalized Galois geometric
  section comparison on unbounded K injective complexes` returned 8 unrelated hits:
  Nobeling exactness/injectivity, eval_section_injective_of_eventually_injective,
  an infinite-Galois extension construction and finite Galois category injectivity.
  No matching combined statement.
- msearch.py loogle: `Condensed, IsKInjective` returned 0 hits, with unknown identifier
  IsKInjective in the service's index (not evidence that the project lacks it).
- msearch.py grep: `singleton.*[Ee]xact|[Gg]alois.*[Kk][Ii]njective|pointEvaluation`
  returned 25 unrelated Mathlib hits, mostly substring matches in subsingleton proofs.
- Direct rg over `lean/WeilConjectures`, `lean/Sheaf`, and the Mathlib source for
  Galois/section/singleton/KInjective expressions found generic derived-composition
  machinery and other section models, but no normalized field-action statement.
  Direct node-id search in WeilConjectures returned no hits. Name checks for
  `GaloisKInjectiveSectionModel` and `galois_kinjective_section_model` in Mathlib,
  WeilConjectures and `dag/lean_names_upstream.json` returned no hits.

Sources checked: local Stacks derived.tex, lemma-adjoint-preserve-K-injectives
(Tag 08BJ), its exact-left-adjoint argument; local Bhatt--Scholze PDF pp.27–28,
Examples 4.1.9 and 4.1.10, including finite-surjection covers and exactness at
extremally disconnected tests; the current blueprint direct-images proof, paragraph (3).
The node accurately labels the combined normalized chain model as an agent refinement.

Edge cases: empty X still has the final pro-etale test and its actual section map;
no assumption excludes it. R=0 is allowed by CommMon with no nontriviality assumption.
Trivial G is allowed and FixedAll is still the recorded base-change condition.
The singleton is inhabited, so the cover-splitting argument applies even when the
cover contains empty members. No arbitrary profinite test is claimed to have exact
evaluation. Resolutions need not be bounded or monomorphic in Model.resolution;
identity resolutions and two different resolutions are both included. All localization
universes are explicit and compatible without changing the original small sites.

Validation: scompile.py compiles the sandbox and final module against the live
published library; the clean pass took 40.2s and 39.1s. Initial failures were repaired
by using the actual ring/module instance presentations, explicit localization
universes, and direct additive/zero witnesses inside the conclusion. Disabling the
unused structure SizeOf/injectivity generators avoids expensive generated auxiliary
work. The 60s limit is unchanged. Only the theorem proof is postponed.

## Second reading by Q32

Self-audit with the node, current dependency sources and final module open; this is
not claimed to be an independent worker review. The dispatcher explicitly prohibited
starting another agent, and the maintainer supplies the independent delivery review.

Checked each hypothesis and clause against the correspondence above. The initial
module's inferred derived Hom universes were inconsistent; all derived functors and
localizations now use u+2 explicitly, with the actual ring-object monoid instances.
The normalization is an equation after the existing invariant inclusion, so it cannot
be satisfied by rescaling an unrelated section isomorphism. Unique gluing is separately
stated. The derived comparison is fixed by existing canonical comparisons and has the
chain formula on every resolution, which also covers identity and arbitrary changes.
The fixed left adjoints and their normalized adjunctions remain those of e. No
hollow assumption, boundedness restriction, group finiteness, finite cohomological
dimension, or nontriviality condition was added. The theorem says exactly the original
node; no node fault or STATEMENT-DISPUTED flag remains.
