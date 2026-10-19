## Worker report

Q98, stage 2, item `lem-pur-support-localization-triangle`.

The item module is `Sheaf.AlgebraicGeometry.SupportLocalizationTriangle`.
It states the ordinary bounded-below localization theorem, with `sorry` proofs,
and supplies the actual canonical comparison maps needed to state its arrows.
The theorem is in `AlgebraicGeometry.ProEtale`, and its primary declaration is
`supportLocalizationTriangle`. All data definitions are real constructions.
The item statement, statement dependencies, proof and proof dependencies are unchanged.
There is no STATEMENT-DISPUTED claim or statement correction.

Sources read: the item and every statement-dependency node and its recorded declaration;
current blueprint `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/`
(the support-triangle definition, three-meanings definition, item, and its proof);
the corresponding older source pointers in the node; and the cited derived-category,
pro-etale, open-restriction and adjunction interfaces. The item docstring follows
all eight steps of the current DAG proof, including the quasi-compact complement
and same-category qualification on the right-adjoint identification.

Hypotheses and clauses are rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Schemes and closed/open pair | `{X Z U : Scheme.{u}}`, `s : Z ⟶ X`, `j : U ⟶ X`, `[IsClosedImmersion s]`, `[IsOpenImmersion j]`, `hPair : IsCompl (Set.range s) (Set.range j)` |
| Quasi-compact complement | `[QuasiCompact j]`; no finiteness or Noetherian condition on X |
| Finite commutative coefficients | `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`; no `Nontrivial Λ` |
| All constant-coefficient module sheaves on small pro-etale sites | `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`, exactly the fixed-scalar presentation used by the recorded `def-pur-flasque-support`; the categories are not constructible subcategories |
| Ordinary derived categories and bounded-below K | `DerivedCategory` and `K : DerivedCategory.Plus ...`; `IsSupportInjectiveModel` requires an existential integer lower bound and injective terms |
| Complex input and actual resolution arrow | `supportResolutionCone`: for a bounded-below complex K, an actual `r : K ⟶ I` with `QuasiIso r`, bounded-below injective I, and its specified distinguished cone |
| Sheaf exceptional inverse image | the recorded `finiteClosedUpperShriek Λ s j`, not ordinary closed restriction and not a transported constructible functor |
| Rs! computed on injectives | the existing `.rightDerivedFunctorPlus`; `supportShriekModelComparison` is built from `.rightDerivedFunctorObjQIso`, the image of the input comparison, and `.rightDerivedFunctorPlusCompatibility` |
| Exact termwise s_* | `supportClosedDerivedPlus` uses the existing `preservesFiniteColimits_lowerStar_of_isCompl`, together with right-adjoint left exactness, to form `.mapDerivedCategoryPlus` |
| Actual cone and distinguishedness | `supportInjectiveConeDistinguished` asserts short exactness and invertibility of the actual `supportConeQuotient`; `supportModelTriangle` is the cone triangle with boundary inverse-Q(q), negative shifted cone projection, then the localization shift comparison |
| Three triangle terms | the chosen comparison `eB : Q.obj I ≅ K.obj`, the explicitly constructed `supportFirstModelComparison` to s_*Rs!K, and `supportThirdModelComparison` to Rj_*j*K |
| Correct first two arrows | the last two equations in the model clause identify Q(inclusion) with `adj.counit.app K` and Q(open unit) with the unit of `derivedUpperStarLowerStarAdjunctionPlus` |
| Same ordinary unbounded Rj_* | `supportThirdModelComparison` explicitly uses the unbounded derived computation on the open injective model and the canonical `.rightDerivedFunctorPlusCompatibility`; it is not a different pushforward |
| Rs! right adjoint to this same s_* on D+ | `∃ adj : supportClosedDerivedPlus ... ⊣ (finiteClosedUpperShriek ...).rightDerivedFunctorPlus` |
| Any other right adjoint, compatible with counit | universally quantified G and `adj'` on those exact same D+ categories, followed by the unique natural isomorphism e satisfying `s_*.map (e.hom.app K) ≫ adj'.counit.app K = adj.counit.app K` |
| Independence of injective resolution | `SupportTriangleCanonicality`: equal derived model maps give equal first/third components, and an invertible derived comparison has invertible first/third components |
| Specified functoriality including the boundary | `SupportTriangleFunctoriality`: each chain map of injective models has the unique triangle morphism with Q(s_*s!f), Q(f), Q(j_*j*f) as components. A triangle morphism includes all three commutative squares. Component functor laws and uniqueness imply identity and composition, including comparison cocycles |
| Etale base change | `SupportTriangleEtaleBaseChange`: arbitrary cartesian closed/open squares over an etale v. The primed pair and the etaleness of vU are the properties automatically inherited by the base-changed pair; these impose no extra restriction on v |
| Canonical full base-change comparison | an isomorphism of the pulled-back short complex with the primed short complex, middle map identity, third map the actual pushforward base-change mate followed by the inverse-image composition comparison; an isomorphism of the full derived triangles with all three components fixed by this short-complex comparison and `.mapDerivedCategoryFactors`. The first component is thereby induced on the kernels, and the triangle isomorphism includes the signed boundary square |

Definitions are shared with the project: `supportedSectionsComplex` is reused from
`Sheaf.AlgebraicGeometry.PurSupportExact`; the sheaf kernel, kernel inclusion,
closed supported inverse image and supported-unit comparison are reused from
`ProEtaleSupportedSections` / `ProEtalePairFlasque`. The generic Mathlib
mapping cone and its signed triangle are reused without a second cone convention.
The cone's biproduct order is A[m+1] ⊞ B[m] in Mathlib, the canonical swap of the
blueprint's B[m] ⊞ A[m+1]; its differential and quotient are the same construction.

The fixed-scalar presentation is the one supplied by the support dependency itself.
The site has object universe u+1 and morphism universe u, with module values in u+1.
No equality of these universes is imposed. The imported coefficient comparison
`finiteCoefficientIntrinsicRealization_exact` identifies the usual ULift presentation
with modules over the intrinsic constant ring. The recorded site and operations
modules are imported, as is the normalized fixed/intrinsic transport module.
No new module category, coefficient identification, or derived operation is chosen.

Dependency declarations used (modules are listed without their `lean/` paths):

- `Sheaf.AlgebraicGeometry.ProEtalePairFlasque`: `finiteSupportedClosedComparison`,
  `finiteSupportedClosedComparison_isIso`, and the reexported
  `finiteSupportedSections`, `finiteSupportedSectionsι`, `finiteClosedUpperShriek`.
- `Sheaf.AlgebraicGeometry.PurSupportExact`: `supportedSectionsComplex` and
  `shortExact_sectionsWithSupport` (the latter is a proof dependency).
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`;
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded ordinary
  constant-ring operations and their reexported fixed-scalar realization.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`: the normalized realization
  and ordinary inverse-image/direct-image comparisons; fixed-scalar `upperStar`,
  `lowerStar`, `upperStarLowerStarAdjunction` are the existing upstream functors.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.Plus`;
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus` and its injective computation.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`:
  the cone-to-quotient and distinguished-triangle machinery;
  `CochainComplex.mappingCone`, `.descShortComplex`, `.triangle` are used directly.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`:
  `preservesFiniteColimits_lowerStar_of_isCompl` (also read through `scompile.py --source`)
  and the closed full-faithfulness proof dependency.
- `WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunctionPlus`;
  `WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale`:
  `baseChangeMap`; `upperStarComp` and `upperStarCongr` fix its quotient comparison.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `Functor.rightDerivedFunctorObjQIso`;
  `.PlusCompatibility`: `Functor.rightDerivedFunctorPlusCompatibility`;
  Mathlib/upstream exact-functor interfaces supply `.mapDerivedCategoryFactors`
  and `.mapDerivedCategoryPlusCompatibility`.
- The stated proof dependencies are imported for stage 3: ring-sheaf Grothendieckness,
  ringed open/closed recollement, termwise homotopy adjunction, exact derived functors,
  restriction of injectives, weakly etale localization, etale comparison, coefficient
  exactness, and the generic Mathlib enough-injectives, K-injective Hom and cone results.

Edge cases checked mathematically before finalizing the signatures:

- Zero ring and zero complex are allowed; no nontriviality hypothesis or nonzero
  boundary is asserted.
- Empty schemes, empty support, and full support are allowed. The formulas reduce
  respectively to the zero triangle, 0→K→K, or K→K→0, with the specified signed cone.
- The lower bound may be any integer, so negative shifts are not excluded.
- No constructibility, bounded-above, Noetherian, properness, or compactness
  assumption is introduced.
- Identity etale base change is included, as is an arbitrary cartesian presentation
  of the fibre products. Empty base changes are included.
- Quasi-compactness is required for the original complement and inherited by the
  primed complement; the non-quasi-compact counterexample in the support dependency
  is therefore not accidentally claimed.

Searches made for an existing exact statement:

- `msearch.py ... leanfinder`, query “For a bounded below complex of pro etale module
  sheaves the supported kernel cone gives a functorial localization distinguished
  triangle compatible with etale base change”: eight generic triangle/localization
  hits, including `DerivedCategory.mem_distTriang_iff`; none supplies this theorem.
- `msearch.py ... loogle`, query `CochainComplex.mappingCone, DerivedCategory.triangleOfSES`:
  no hits. Those generic constructions were subsequently located and read directly
  in Mathlib's short-exact and cone modules.
- `msearch.py ... leansearch`, query “Canonical pro etale support localization triangle
  compatible with etale pullback”: eight unrelated etale ring-localization hits;
  no exact statement.
- `msearch.py ... grep`, query `supportLocalizationTriangle|supportsShortComplex`
  under Mathlib/CategoryTheory: no hits.
- `rg` across Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: the named upstream support triangle is on the
  small etale site. The ambient pro-etale theorem
  `exists_proEtale_closedSupportTriangle` was opened in full: it assumes locally
  Noetherian compact X and does not give the model canonicality/base-change clauses,
  so it is not this node. The upstream transported constructible upper-shriek is
  likewise on a different category. Exact-name searches for the new helper names
  and primary theorem name in the ProEtale namespace found no existing declarations.

Validation uses only the prescribed `scompile.py` and `deliver2.py --no-push` wrappers.
The three delivered files are compiled separately in dependency order. No global
build, direct repository edit, or direct git command was used.

## Dependency modules

`def-pur-support-triangle`: the old record points to
`AlgebraicGeometry.Etale.supportLocalizationTriangle`, whose objects are small-etale
sheaves. `SupportTriangleConstruction.lean` instead constructs the specified
pro-etale cone using the recorded supported-kernel functor and supported complex.
It fixes the inverse-supported-unit inclusion, open unit, cone quotient, and the
negative shifted projection boundary. The only extra input to the triangle object
is a proof that its particular Q(q) is invertible; the item states that theorem for
injective models. The definition's chosen resolution is the argument I, and
`supportResolutionCone` supplies an actual resolution arrow for any complex input.
Only this dependency's `lean` field changes, with the required explanatory note.

`def-pur-triangle-meaning`: the old declaration accepts three arbitrary predicates
on an arbitrary type, so it does not define canonicality, functoriality or etale
base change. `SupportTriangleCompatibility.lean` defines them on this exact
pro-etale cone, with specified component maps and the canonical cartesian base-change
mate. It fixes the full short-complex and derived-triangle comparisons. Only this
dependency's `lean` field changes, with the required explanatory note.

## Earlier second reading (a previous round; superseded)

Pending the separate second worker specified by the dispatcher brief. This report
records the first worker's checks only; it does not claim an independent second reading.

## Second reading by Q98

I independently opened the three delivered modules, the three node records, every
statement-dependency record, and the declarations actually used. I read the current
blueprint's three source paragraphs and Stacks `proetale.tex`, labels
`section-morphism`, `lemma-closed-immersion`,
`lemma-closed-immersion-complement-retrocompact-exact`, `lemma-open-immersion`, and
`lemma-ses-associated-to-open`; `sites-cohomology.tex`,
`lemma-restrict-K-injective-to-open`; and `derived.tex`, the explicit cone-to-quotient
construction preceding `lemma-derived-canonical-delta-functor` and its proof.
The blueprint node has already made the quasi-compact-complement qualification
explicit. Stacks' retrocompact-open hypothesis is precisely quasi-compactness of j;
there is no global Noetherian, compactness, properness, or characteristic hypothesis.
No repair note exists for this item. No delivered node has `statement_change`.

My object/hypothesis/conclusion checklist, written from the node before comparison:

| Node object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| Schemes X, Z, U and closed immersion s | `{X Z U : Scheme.{u}}`, `s : Z ⟶ X`, `[IsClosedImmersion s]`: exact. |
| Complementary open immersion j | `j : U ⟶ X`, `[IsOpenImmersion j]`, `hPair : IsCompl (Set.range s) (Set.range j)`: exact; no chosen reduced structure on Z. |
| j quasi-compact | `[QuasiCompact j]`: exact. I read Mathlib's inverse-image-of-compact-open definition and the server's closed-direct-image exactness declaration. |
| Finite commutative coefficient ring | `Λ : Type (u + 1)`, `[CommRing Λ] [Finite Λ]`: exact, including the zero ring. |
| All constant-coefficient module sheaves on the small pro-etale site | `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)` and the corresponding Z/U categories: the recorded support dependency's fixed-scalar presentation; no constructible or completed subcategory. |
| Ordinary derived categories, bounded below K | `DerivedCategory` and `DerivedCategory.Plus`, respectively: exact. I opened Mathlib's localization and standard-t-structure subcategory definitions. |
| Input may be an actual bounded below complex | `supportResolutionCone` quantifies over K with `∃ n : ℤ, K.IsStrictlyGE n` and supplies a genuine `r : K ⟶ I`, `QuasiIso r`, and an injective model: exact. The cone definition takes that model as its explicit argument. |
| Sheaf s! is closed inverse image of the supported kernel | `finiteClosedUpperShriek Λ s j` is the existing `finiteSupportedSections Λ j ⋙ upperStar ... s`: exact. The kernel itself is of the natural open unit, not an arbitrary subsheaf. |
| Rs! is ordinary right derivation computed on bounded below injectives | `.rightDerivedFunctorPlus`; `IsSupportInjectiveModel` requires an integer lower bound and injective terms; `supportShriekModelComparison` is explicitly composed from the derived unit computation and bounded/unbounded compatibility: exact. |
| Exact s_* and its termwise induced functor | `supportClosedDerivedPlus` invokes `preservesFiniteColimits_lowerStar_of_isCompl` and then `.mapDerivedCategoryPlus`; left exactness comes from the existing adjunction: exact. |
| Triangle supplied by the specified injective cone is distinguished | `supportInjectiveConeDistinguished`, `supportResolutionCone`, and the model clause of `supportLocalizationTriangle`: exact. `supportConeQuotient` is Mathlib's actual `mappingCone.descShortComplex`; its localized inverse is an input proof, not chosen map data. |
| Three terms s_*Rs!K, K, Rj_*j*K | The model clause supplies `eB : Q.obj I ≅ K.obj`, with the defined `supportFirstModelComparison` and `supportThirdModelComparison`: exact identifications. The latter uses the existing ordinary unbounded Rj_* and its canonical D+ compatibility. |
| Actual first two triangle arrows | The two model equations carry Q(inclusion) to `adj.counit.app K` and Q(open unit) to `derivedUpperStarLowerStarAdjunctionPlus.unit.app K`: exact. |
| Actual fourth arrow | `supportModelTriangle` uses inverse Q(q), then Q of Mathlib's cone `mor₃`, then the shift comparison. I opened `mappingCone.triangle`: `mor₃` is the negative shifted `fst`, so this is the source's -p q⁻¹, with no sign reversal. |
| Rs! right adjoint to this exact s_* on D+ | The existential `adj : supportClosedDerivedPlus ... ⊣ finiteClosedUpperShriek.rightDerivedFunctorPlus`: exact, on these same categories. |
| Any other exceptional right adjoint is naturally identified compatibly with the counit | Universal G and `adj'` on those same D+ categories; the unique natural isomorphism e satisfies the displayed counit equation: exact. Adjoint uniqueness accounts for the uniqueness clause. |
| Resolution independence under derived comparison maps | `SupportTriangleCanonicality` says equal derived model maps induce equal first/third components and derived isomorphisms induce invertible components. Together with the specified triangle morphism and K-injective Hom bijection this is the required resolution comparison, including its cocycle: exact. |
| Functoriality in derived K | `SupportTriangleFunctoriality` fixes all three components for every model chain map. A triangle morphism includes the boundary square; its uniqueness and the three underlying functor laws give identities and composition. Canonicality removes the chain representative: exact. |
| Etale base change of the entire triangle | `SupportTriangleEtaleBaseChange` quantifies over arbitrary etale v and arbitrary cartesian presentations of both fibre products. Its short-complex isomorphism has identity middle component and the actual open base-change mate as third component; its triangle isomorphism fixes all three localized components, hence includes the boundary square: exact. |

Dependency-module reading (no new definition nodes are introduced):

- `def-pur-support-triangle`: I opened the old
  `AlgebraicGeometry.Etale.supportLocalizationTriangle` in
  `WeilConjectures/SixFunctors/OpenClosed/Supports.lean`. Its input really is
  `Sheaf X.smallEtaleTopology A`, so it cannot supply this pro-etale cone.
  The replacement uses `supportedSectionsComplex` from `PurSupportExact`, the
  inverse of `finiteSupportedClosedComparison`, the actual open unit, and the
  existing Mathlib cone. The quasi-compact pair is the context in which the
  node's asserted inclusion is supplied by its supported-sections dependency.
  It accepts the chosen resolution I explicitly; `supportResolutionCone` supplies
  the resolution arrow and injective property, rather than hiding them in data.
  The cone is additionally meaningful on any complex. Mathlib's summand order
  is A[m+1] then B[m]; the canonical interchange gives the source's displayed
  B[m] then A[m+1] and the same signed matrix. Verdict: usable repair, no duplicate
  pro-etale construction, and the `lean.note` explains the defective old record.
- `def-pur-triangle-meaning`: I opened `SupportTriangleMeaning.lean` and verified
  that its old declaration merely accepts arbitrary predicates on an arbitrary
  type. The replacement concretely fixes model maps, derived independence, and
  the cartesian base-change comparison on the actual cone. `Etale vU`, the
  primed immersion properties, quasi-compactness of j', and the primed complement
  relation are inherited from the cartesian squares. Their explicit binders do
  not exclude any base change in the source. The first comparison is forced on
  kernels by the short-complex isomorphism; it is not an arbitrary comparison
  between the same objects. Verdict: the dependency's three notions are supplied,
  and the old unusable declaration is not used as a substitute for them.

I also opened `ProEtaleSupportedSections`, `ProEtalePairFlasque`,
`PurSupportExact`, `ProEtaleDerivedCategory`, the intrinsic coefficient realization,
`SfIntrinsicRealizationTransport`, the finite ordinary star reexport, the ordinary
pro-etale derived-star module, and the generic right-derived injective computation
and PlusCompatibility modules. The recorded site has object universe u+1 and
morphism universe u. Module values have universe u+1; there is no extra equality
between site object and morphism universes. The support node already uses this
fixed-scalar category; the imported exact coefficient equivalence and normalized
transport identify it with intrinsic constant-ring modules. In particular these
signatures do not use the constructible exceptional inverse image on another
category. I read the current closed-immersion module using `scompile.py --source`
when it was absent from the shared checkout; its exactness theorem has precisely
the required complement hypotheses.

Edge cases: zero ring, zero complex, empty X, empty Z, and empty U remain admitted.
The last two support cases give respectively 0→K→K and K→K→0. No nonzero section,
nonempty scheme, fixed lower bound, nonnegative-degree restriction, or field
assumption enters the signatures. Degree zero and all negative shifts are allowed.
Identity etale maps, empty base changes, and arbitrary isomorphic fibre-product
presentations are included. There is no index-set hypothesis; the only degree
index is ℤ, with an existential arbitrary integer bound. The finite coefficient
ring has no characteristic restriction. All universe and object variables are
bound under `autoImplicit false`.

Independent searches, using words different from the first worker's queries:

- `msearch.py ... leanfinder`: “Pro etale closed support functor localization
  distinguished triangle bounded below injective complex etale base change”:
  eight results, principally t-structure and ring-etale-localization lemmas;
  no support-localization theorem.
- `msearch.py ... leansearch`: “Functorial localization triangle from the kernel
  of open restriction for bounded below complexes of sheaves on the pro-etale
  site”: generic `triangleOfSES`, mapping-cone, and localization results, already
  reused in the delivery; no exact pro-etale statement.
- `msearch.py ... loogle`: `CochainComplex.mappingCone, Triangle` reports unknown
  `Triangle`; the follow-up `CochainComplex.mappingCone` locates the generic cone
  API. I opened its source and signed triangle directly.
- `rg` in Mathlib, upstream `WeilConjectures`, and the shared `lean/Sheaf` for
  closed/support triangles and additive-kernel/model predicates: found the
  etale construction, etale six-functor localization results, and
  `exists_proEtale_closedSupportTriangle`. I opened that last signature: it
  requires locally Noetherian compact X and omits these specified comparison,
  functoriality, and base-change clauses. It cannot replace this item. No exact
  competing construction or compatibility definition was found.

Mismatch found and repaired: the main module relied on transitive imports for
nine Mathlib proof-dependency modules. I added explicit non-public imports for
EnoughInjectives, DerivabilityStructureInjectives, RightDerivedFunctorPlus,
KInjective, Adjunction.Unique, HomotopyCategory.ShortExact, DerivedCategory.Basic,
Morphisms.QuasiCompact, and DerivedCategory.ExactFunctor, as required by stage 2
§3(7). No definition, statement, or node dependency changed. I checked every
recorded `lean.statement` against its source signature: all three match verbatim.
All declarations have source/blueprint docstrings; every postponed proof is a
named theorem with a natural-language proof; no definition has sorry data.
The main theorem docstring follows all eight DAG proof steps. No line exceeds
100 characters. All three modules compiled separately and cleanly through the
prescribed `scompile.py` wrapper after the import edit (library passes 3.7 s,
4.4 s, and 5.9 s). No error or warning occurred. The dry-run and delivery results
are recorded by the prescribed delivery wrapper.
