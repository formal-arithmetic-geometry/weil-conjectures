## Worker report

This stage-2 delivery states the entire node in
`Sheaf.AlgebraicGeometry.NormalPrincipalOpenContinuousSections`, namespace
`AlgebraicGeometry.ProEtale`. It has five construction/evaluation helpers and seven
named theorem clauses. All seven proofs are `sorry`. Every helper has actual data.
The natural-language statement, proof and proof dependencies remain unchanged.

The live node's Q101 review is its completed stage-1 split; the live node has no
Lean attachment. This delivery supplies stage 2, without replacing that split.
No repair note for this item was present in the read clone.

Hypotheses and objects:

- A commutative ring Q is `(Q : Type u) [CommRing Q]`. Normality is exactly
  `hnormal : ∀ (p : Ideal Q) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧
  IsIntegrallyClosed (Localization.AtPrime p)`, the recorded inline normal-ring form.
  No `IsDomain Q`, `Nontrivial Q` or Noetherian hypothesis is imposed.
- The element is `(s : Q)`. Injective multiplication is
  `hs : Function.Injective (fun x : Q ↦ s * x)`.
- X is `Spec (.of Q)` and X_s is `Spec (.of (Localization.Away s))`.
  `normalPrincipalOpenInclusion Q s` is an abbreviation for the actual
  `Spec.map (CommRingCat.ofHom (algebraMap Q (Localization.Away s)))`.
  The existing localization-away open-immersion instance applies; there is no
  arbitrary supplied map or assumed localization isomorphism.
- E is `(E : Type u) [NormedField E] [IsUltrametricDist E]` with its norm metric
  topology. For a normed field, the ultrametric distance inequality is equivalent
  to the node's nonarchimedean norm inequality, by translation invariance and
  `dist a b = ‖a-b‖`. No completeness, local compactness or nontrivially normed
  assumption occurs. The trivial absolute value is allowed.
- A common ambient universe u is used for rings, fields and schemes. The actual
  small pro-etale site has object universe u+1 and morphism universe u; coefficients
  have carrier universe u+1. The site is not replaced by an equal-universe category.
- C_E is `Profinite.continuousCoefficientRingObj E`: continuous maps on all
  profinite sets with pointwise ring operations, with the standard section lift.
  This is the same underlying sheaf as the recorded
  `Profinite.continuousMapRingObjOfUniverse.{u,u} E`: both constructions have
  `ULift.{u+1} C(S,E)` as sections, the identical precomposition restrictions, and
  the ring-sheaf transported tensor multiplication and unit. The existing
  realization dependency is stated on `continuousCoefficientRingObj`, so this
  form uses that interface directly. It is not a second coefficient construction.
- The pulled-back ring is the recorded
  `condensedRingObj (Profinite.continuousCoefficientRingObj E) X`, whose bundled
  version is `coefficientRing X (Mon.mk (Profinite.continuousCoefficientRingObj E))`.
  `principalContinuousCoefficientSections` evaluates the existing
  `InternalAbelianSheafModule.presheafRings` after the monoidal sheaf-to-presheaf
  functor. Its carrier is exactly the coefficient sheaf's section group, and its
  multiplication/unit are reconstructed from the existing tensor ring object.
  Its internal `letI` supplies that existing functor's monoid structure; no
  file-local instance or new ring structure axiom is introduced.

Clause mapping:

1. `normal_principal_open_clopen_components` first asserts
   `Function.Bijective` for the function sending a `Clopens X` to its actual
   preimage under `normalPrincipalOpenInclusion Q s`. The subtype proof is the
   existing theorem that a continuous inverse image of a clopen is clopen.
   Its second conjunct supplies
   `h : ConnectedComponents X_s ≃ₜ ConnectedComponents X`, with
   `h (ConnectedComponents.mk x) = ConnectedComponents.mk (i x)` for every x.
   Mathlib's `ConnectedComponents` carries precisely the quotient topology.
2. `normal_principal_open_continuous_sections` supplies the normalized h and
   `r : C(X,E) ≃+* C(X_s,E)` with `r a = a.comp i.base.hom`.
   Thus it asserts a ring bijection for actual restriction. For each a on X_s,
   the next conjunct states existence and uniqueness of a continuous factor b
   on `ConnectedComponents X_s` with `a = b.comp q_Xs`.
   The final conjunct states, pointwise,
   `r.symm a x = a.continuous.connectedComponentsLift (h.symm (ConnectedComponents.mk x))`.
   This is exactly the inverse `bar a ∘ h⁻¹ ∘ q_X`; `connectedComponentsLift` is
   the canonical unique factor, and its continuity follows from the existing
   ultrametric total-disconnectedness instance.
3. `normal_principal_open_coefficient_sections` supplies a ring equivalence c
   between evaluation of C_E,X at `Scheme.ProEt.mk (𝟙 X)` and evaluation of
   C_E,Xs at `Scheme.ProEt.mk (𝟙 X_s)`. These are the terminal objects, so these
   section rings are the specified global sections. The first conjunct requires
   c to equal `principalContinuousCoefficientGlobalRestriction E i` on every section.
   This helper uses the actual `condensedPushforwardHom` (the mate of the
   canonical `condensedPullbackHom`) evaluated at the terminal object of X.
   Its target before terminal identification is evaluated at X ×_X X_s; the helper
   restricts along the canonical arrow X_s → X ×_X X_s given by
   `pullback.lift i (𝟙 X_s)`. Thus the map really is inverse-image restriction.
   The second conjunct is the realization square:
   `realization_Xs (c a) = (realization_X a).comp i.base.hom`.
   `principalContinuousCoefficientRealization` is evaluation of the existing
   `condensedFieldContinuousMapIso E X`, followed by removal of the standard lift.
   No isomorphism or map is chosen independently of the canonical normalization.
4. `normal_principal_open_coefficient_object_sections` quantifies over every
   `(Z : Scheme.{u}) (t : Spec (.of Q) ⟶ Z) [WeaklyEtale t]`.
   This is an arbitrary affine object of Z's small pro-etale site. Its principal
   open has structure morphism `i ≫ t`; weak etaleness follows from the existing
   open-immersion and composition instances. The theorem supplies a ring
   equivalence between actual evaluations at these two objects, normalized by
   `principalContinuousCoefficientObjectRestriction` on the over-morphism with
   underlying map i, and the corresponding realization/precomposition square.
   This helper is literally the original coefficient sheaf's presheaf map.
5. `normal_principal_open_continuous_sections_natural` quantifies over a second
   normal commutative ring Q', a regular s', and maps v and vs. The equations
   `i' ≫ v = vs ≫ i` and `v ⁻¹' Set.range i = Set.range i'` encode the restricted
   map and the exact preimage condition from the node. For every pair of ring
   equivalences r,r' normalized by the already asserted actual restrictions,
   it states both `r' (a.comp v) = (r a).comp vs` and
   `(r.symm a).comp v = r'.symm (a.comp vs)`. The normalization binders name the
   specified bijections; they add no hypothesis on the mathematical pairs.
6. `normal_principal_open_coefficient_sections_natural` uses exactly the same
   normal pairs and commuting square. The maps c,c' are constrained to be the
   actual global coefficient restrictions from clause 3. Its two conjuncts
   state the forward and inverse squares for the existing global coefficient
   pullback maps along v and vs.
7. `normal_principal_open_coefficient_object_sections_natural` gives both squares
   for evaluations in every common ambient Z. The over-morphisms f and fs are
   the maps v and vs over Z, and hv/hopen impose exactly the same pair conditions.
   Its c,c' are constrained to be the actual restrictions from clause 4. Both
   bijections and their inverses commute with the sheaf's presheaf maps.

Dependency declarations used (all signatures and relevant docstrings read):

- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain`; `Mathlib.RingTheory.Localization.AtPrime.Basic`:
  `Localization.AtPrime`. These render def-weil-pbc-normal-ring's recorded form.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `algebraMap` gives its canonical ring map. The ring localization instances are
  available through `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse` and its underlying ring object;
  the definitionally identical common-universe interface used by the realization
  is `Profinite.continuousCoefficientRingObj` in
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `condensedPushforwardHom`, `condensedPullbackHom` and
  `upperStarFromPoint`; these are the recorded pulled-back coefficients and maps.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.mk`
  and `Scheme.ProEt.topology`.
- `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`:
  `existsUnique_condensedFieldContinuousMapIso_of_totallyDisconnected`,
  `condensedFieldContinuousMapIso`, and `profiniteTestProjection`. The supplied
  comparison is uniquely determined by its profinite-test adjunct equations.
- The added, already landed statement dependency
  `def-weil-pbc-internal-abelian-sheaf-module-equivalence` supplies
  `InternalAbelianSheafModule.presheafRings` in
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`; it evaluates the
  existing ring object as ordinary section rings. The addition is permitted by
  brief-stage2 section 5's rule for already landed statement dependencies.

All already stated proof dependencies are imported as proof imports, including
`integral_totalFraction_mem_range_of_normal`, the Mathlib idempotent/clopen
correspondence, affine qcqs and spectral instances,
`isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage`, and
`ContinuousRingUniverse.comparison`. At inspection the proof-only nodes
lem-sfb-ultrametric-component-map-extension and
lem-sfb-normalized-continuous-set-comparison-coherence had no Lean attachment;
there is no nonexistent module imported for them. Their mathematical roles remain
in the theorem docstrings and the unchanged node proof. They are not missing
notions needed to type this statement.

Edge cases checked before and after writing:

- Q is the zero ring: it is allowed by `[CommRing Q]`; the prime-local normality
  condition is vacuous, and multiplication is injective on its singleton carrier.
  Both spectra and their component spaces are empty. Both clopen sets and all
  function/section rings are singletons; the ring equivalences still make sense.
- s=1: both restrictions are canonical identity-open identifications; the component
  inverse and all naturality squares specialize to identities.
- Normal rings with several components (for example k × k) are allowed. A regular
  element must remain regular in each factor; `(1,0)` is properly excluded.
- For the non-normal ring k[x,y]/(xy), s=x+y disconnects the two branches on the
  principal open, illustrating why normality is needed.
- Trivially normed E is included; the ultrametric instance gives its discrete
  topology. No completion is used anywhere.
- Arbitrary ambient Z is allowed, as are empty affine pro-etale objects and
  morphisms involving empty normal pairs. No condition on Z was introduced.

Searches (actual msearch.py records are in searches.jsonl in the sandbox):

- LeanFinder: "For a normal ring Q and nonzerodivisor s, restriction from Spec Q
  to Spec Q[1/s] induces bijections on clopens, connected components and continuous
  nonarchimedean field valued coefficient sections". Eight hits, including
  `PrimeSpectrum.toPiLocalization_bijective`, `basicOpenIsoSpecAway`, and the
  clopen-idempotent correspondence. None states this normal-ring restriction result.
- Loogle: `"ContinuousMap", "PrimeSpectrum"`. Zero hits.
- Mathlib grep:
  `(ContinuousMap|continuous).*(IsLocalization|nonZeroDivisors)|(IsLocalization|nonZeroDivisors).*(ContinuousMap|continuous)`.
  Two hits, both unrelated convenient-topology localization instances.
- LeanSearch: "Continuous nonarchimedean field valued functions and condensed
  coefficient sections restrict bijectively from the spectrum of a normal ring
  to a principal open defined by a nonzerodivisor". Eight hits about structure
  sheaf/localization maps; no match for these continuous coefficient sections.
- Project `rg` in both WeilConjectures and Sheaf for normal/principal/continuous
  combinations found `NormalGenericContinuousSections`: it assumes an integral,
  locally Noetherian base and concerns the generic fibre, so it is not this node.
  Searches for the new declaration names in both roots and dag/lean_names_upstream.json
  found no existing declarations. The required grep for this node id in
  WeilConjectures found none.

Sources opened: Stacks algebra.tex lemma-normal-ring-integrally-closed (034M),
lemma-disjoint-decomposition (00EE), topology.tex lemma-spectral-pi0 (0906);
Bhatt--Scholze PDF, Lemma 4.2.12; Hemo--Richarz--Scholbach PDF, page 6, Example 3.1
and the following scheme-pullback paragraph. These agree with the node's agent
consequence, including the absence of a Noetherian or domain hypothesis on Q.

No statement correction, new DAG node, dependency-module repair, hollow definition,
or statement dispute. The source and per-declaration natural-language proofs are
included in the module docstrings. Every postponed proof is a named clause of this
same DAG node and listed in lean.declarations.

Validation uses scompile.py only. The module has explicit universes and
`set_option autoImplicit false`, all lines at most 100 characters, no file-local
notation or instances, and only the permitted theorem-level sorries.

The final module passed both sandbox and named-module server compilation. The
prescribed deliver2.py --no-push run returned OK: preflight passed and the module
compiled cleanly. A local record check confirmed that the only node fields changed
are lean and the single added landed statement dependency; all 12 declarations are
recorded, exactly seven named theorem proofs are sorry, and maximum line width is 94.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
