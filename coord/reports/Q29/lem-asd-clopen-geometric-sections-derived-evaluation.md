## Worker report

Stage 2, Q29, 2026-10-17. Module:
`Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation`.
The node's natural-language statement, dependencies, proof and other fields are unchanged.
There are no new nodes or replacement dependency modules.

The prior worker's stale-dispatch conclusion confused the completed stage-1 split with
stage-2 completion. The base node has `reviewed` by NZ but no `lean` or `reviewed_lean`.
The NZ report is a seven-step natural-language split, not a Lean statement. This delivery
adds the missing stage-2 interface without splitting the node again.

Hypotheses and objects, matched individually:

- A commutative ring: `(A : Type (u + 1)) [CommRing A]`, without finiteness or torsion.
- An algebraically closed field: `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`.
- `P = Spec Ω`: local notation `P := Spec (CommRingCat.of Ω)`.
- An arbitrary scheme and morphism: `{V : Scheme.{u}} (r : V ⟶ Spec (.of Ω))`;
  no properness, separation, dimension or cohomological-dimension hypothesis.
- A finite set: `{I : Type u} [Finite I]`, with no nonemptiness assumption. This is
  the recorded scheme-coproduct size convention; finite sets of other sizes may be shrunk.
- The sections: `s : I → (P ⟶ V)` and `[∀ i, IsOpenImmersion (s i)]`.
- Closed images: `hclosed : ∀ i, IsClosed (Set.range (s i))`.
- Pairwise disjoint images: `hdisjoint : Pairwise (fun i k ↦ Disjoint
  (Set.range (s i)) (Set.range (s k)))`.
- Section identity: `hs : ∀ i, s i ≫ r = 𝟙 P`.
- The coproduct: `U := ∐ (fun _ : I ↦ P)`, with `t i := Sigma.ι _ i`.
- The union: `j := Sigma.desc s`, so `t i ≫ j = s i` is `Sigma.ι_desc s i`.
  `clopenGeometricSections_union` states that this actual union is open and closed,
  and `v := j ≫ r` is étale. These are conclusions of the node, not extra hypotheses.
- Coefficients and unbounded categories: `Sheaf T.smallEtaleTopology (ModuleCat A)`
  and its ordinary `DerivedCategory`; complexes are indexed by `ℤ`.
- Degreewise open extension: `E := D((j)_!open[ModuleCat A])`.
- The components: `Ki K i := (D((s i)^*[ModuleCat A])).obj (E.obj K)` exactly as in
  the node, not a silently substituted component object.
- The open complement: `Z := Scheme.openComplementOfIsClosedImmersion j`.
- Étale sum extension: `B := clopenEtaleDerivedSum A v hv`, which is literally
  `etaleLowerShriek (ModuleCat A) v hv` descended degreewise, with exactness from
  the existing exact left adjunction. No new sheaf functor is introduced.

Conclusions, in order in `clopenGeometricSections_derivedEvaluation`:

1. For every complex `J` on `V`, `J.IsKInjective` iff every point-component
   restriction and its complement restriction are K-injective. Restriction uses
   the recorded exact `upperStar` applied by `mapHomologicalComplex (.up ℤ)`.
   This is also the stated two-piece criterion on `j(U)` and its complement:
   apply the same finite component decomposition inside `U`.
2. Every degreewise extension of a complex `C` on `U` has a quasi-isomorphism `q`
   into a K-injective `J` with zero complement and K-injective point components.
   The resolution is expressed using the dependency record's `QuasiIso` and
   `CochainComplex.IsKInjective`, the two conjuncts of its resolution abbreviation.
   These are the component resolutions with zero complement required by the node.
   Restricting `q` gives their quasi-isomorphisms, since inverse image is exact.
3. `∀ K, IsZero (D(Z.ι^*).obj (E.obj K))` states the zero-complement normalization
   also on the derived objects themselves.
4. `∀ K, IsIso (clopenGeometricEvaluation A r s hs (E.obj K))` is the displayed
   evaluation isomorphism to the finite product. The map is REAL DATA:
   `Pi.lift` of `clopenSectionDerivedRestriction`; each component is the section
   identity comparison followed by the restriction of the actual derived counit.
   Thus this is invertibility of the canonical restriction map, not an arbitrary iso.
   The functor `R((r)_*[ModuleCat A])` is the recorded K-injective total derived functor.
   Its `rightDerivedFunctorUnit` computes it on the normalized resolutions in (2).
5. The following equation with `CategoryTheory.Limits.Pi.map` states naturality
   of this specific evaluation on every derived morphism `f : K ⟶ L`.
6. Global sections on `P` are an equivalence. Together with the imported
   `geometricPoint_pullback_stalk`, this is the exact equivalence with `ModuleCat A`.
   Its termwise descent uses the imported exact-functor comparison, so passage to
   module complexes introduces no new resolution or identification choice.
7. `e : ∀ K, B.obj K ≅ ⨁ (Ki K)` identifies the ACTUAL étale sum extension with
   the finite sum. Its inverse on every `biproduct.ι` is required to be
   `clopenGeometricSumInjection`, which is explicitly the restricted unit of
   the actual étale-sum adjunction, transported through the actual open-unit
   component isomorphism. This equation determines `e` uniquely.
8. The next equation states naturality of `e` with `biproduct.map`.
9. `δ : ∀ K, D(r^*).obj (B.obj K) ⟶ E.obj K` has component `i` equal to the
   canonical section identity followed by `(e K).hom` and `biproduct.π`.
   This is precisely the prescribed projection on each `s_i(P)`.
10. `D(Z.ι^*).map (δ K) = 0` is the specified zero on the complement.
    The component equations determine `δ` uniquely by the clopen cover; the
    existential witnesses here are fully characterized canonical maps, not
    unconstrained inputs or arbitrary choices. No definition chooses such a witness.
11. The next equation states naturality of `δ` for every derived morphism.
12. The adjunct is the actual `mapDerivedUpperStarLowerStarAdjunction.homEquiv`.
    Its composite with evaluation is required to be `(e K).hom` followed by
    `Pi.lift (fun i ↦ biproduct.π (Ki K) i)`, the canonical finite sum-to-product map.
    After the canonical finite biproduct identification, this is exactly identity.
13. The final clause explicitly states `IsIso` for that actual adjunct.

The seven helper definitions contain real compositions, functors, adjunctions and
isomorphisms. The two postponed theorems are
`AlgebraicGeometry.Etale.clopenGeometricSections_union` and
`AlgebraicGeometry.Etale.clopenGeometricSections_derivedEvaluation`.
Both are clauses of this same DAG node and have source/proof docstrings. They are
listed with all helper definitions in `lean.declarations`. No other theorem is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Limits`: coproduct instance, `sigmaOpenCover`,
  `disjoint_opensRange_sigmaι`; `Sigma.desc`, `Sigma.ι` and `Sigma.ι_desc` supply the
  actual chosen coproduct and union.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the ordinary
  `DerivedCategoryModule` encoding and Mathlib `DerivedCategory`.
  Its missing local source was read with `scompile.py --source`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`, `upperStarComp`, and exactness of inverse image.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`: `upperStarId`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek`, its adjunction and exactness; the derived unit is
  from `.Derived.OpenImmersionLowerShriek` and its fully faithful unit instance.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: recorded unbounded framework;
  its upstream `.Derived.UpperLowerStar` gives
  `mapDerivedUpperStarLowerStarAdjunction` and K-injective `rightDerivedFunctor`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective` and its public imports:
  `CochainComplex.IsKInjective`, `QuasiIso`, and the homotopy/derived Hom comparison.
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`, publicly including
  `GeometricPointPullbackStalk`: `geometricPoint_pullback_stalk` and the canonical
  `isIso_globalGerm_identity` refinement, for the exact module-valued equivalence.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `etaleLowerShriek`, `etaleLowerShriekUpperStarAdjunction`,
  `preservesFiniteLimits_etaleLowerShriek`, `injective_upperStar_obj_of_etale`.
- Proof imports: `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`,
  `Sheaf.CategoryTheory.KInjectiveTotalDerived`,
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
  `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`, and
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
  Their recorded declarations and docstrings were opened, including the last via
  `scompile.py --source`.
- The source of `Sheaf.AlgebraicGeometry.KInjectiveResolutions` was also read through
  `scompile.py --source`. Its convenience abbreviation is `QuasiIso q ∧ J.IsKInjective`.
  Its imports, and those of `KInjectiveResolutionsExist`, run through the retired
  duplicate `Sheaf.AlgebraicGeometry.DerivedCategories`. Following the launcher's
  duplicate-import rule, the statement uses the smaller Mathlib imports for the two
  recorded conjuncts, and the existing upstream Grothendieck-abelian K-injective
  resolution framework already imported by `UpperLowerStar`. No private K-injective
  predicate or resolution construction replaces the dependency.

Edge cases checked mathematically before writing:

- `I = ∅`: `U` is empty, extension and sum are zero; the empty product is zero in
  this additive derived category and its unique endomorphism is identity. No
  `Nonempty I` or positive-cardinality binder occurs.
- One section: the map is the section identity and the complement contributes zero.
- Empty complement: restrictions to it are zero; the full finite product remains.
- Empty `V`: only the empty section family is possible, and the same zero calculation
  applies; there is no imposed nonemptiness of `V`.
- Zero ring or zero complex: all displayed maps have zero components and satisfy
  the biproduct equations. No nontriviality assumption occurs.
- Arbitrary infinite coefficient ring and complexes unbounded in both directions:
  no finite-ring, boundedness, perfectness or constructibility assumption is used.
- The index and scheme universes follow the recorded coproduct convention. Coefficients
  and module values use the recorded `u+1` étale convention throughout, without
  equating object and morphism universes of a site.

Searches actually run:

- `msearch.py ... leanfinder`: “Unbounded derived direct image of extension by zero
  along finitely many disjoint clopen sections over an algebraically closed field,
  normalized by the finite sum to product adjunction map”. Eight hits, all unrelated
  Profinite Nobeling/locally-constant constructions; no matching statement.
- `msearch.py ... loogle`: “AlgebraicGeometry.Etale.upperStarComp,
  AlgebraicGeometry.Etale.upperStarId, CategoryTheory.Limits.biproduct”. Zero hits;
  service reports unknown identifier for the project's `upperStarComp`. This is
  recorded as an indexing limitation, not evidence that the comparison is absent;
  its actual upstream source was read and used.
- `msearch.py ... grep`: `clopen|Clopen`, under Mathlib `AlgebraicGeometry`. Four hits
  concern clopen singleton fibres in quasi-finite geometry; no derived evaluation.
- `rg` over upstream `WeilConjectures` and side `lean/Sheaf` for the node id,
  clopen evaluation and finite-clopen phrases. Relevant side hits include the
  abelian `EtaleSheafClopenProduct`, the pro-étale `ClopenSectionComponent`, and
  finite étale trace/splitting lemmas. None states the present unbounded étale
  constant-module result with its normalized adjunct.
- `grep -rn` of the exact item id in upstream `WeilConjectures`: no hit.
- `rg` of all seven proposed helper names and the main theorem name in Mathlib,
  upstream, side Lean and `dag/lean_names_upstream.json`: no hits.

Sources opened: the whole current node and every statement-dependency statement and
Lean/mathlib record; the relevant full declaration signatures/docstrings; Stacks
`derived.tex`, lemmas `lemma-K-injective-defined` and
`lemma-right-derived-exact-functor`; and the current main-20261015
`prop-asd-smooth-base-change` statement and full proof, especially coherence (iii).
The node is a non-unit finite-clopen calculation extracted from that proof; its
statement agrees with those sources. No STATEMENT-DISPUTED or correction is needed.

Validation: `scompile.py Q29 lem-asd-clopen-geometric-sections-derived-evaluation`
compiled the full module both as the sandbox module and at its intended module path,
with no errors or warnings. The last clean run took 16.0 seconds and 28.2 seconds
respectively, below the fixed 60-second per-file limit. Every universe and variable
is explicitly bound; all nine declarations have node/source docstrings and every
postponed theorem has its natural-language proof.

## Second reading by Q29

Author's final rereading, not an independent review: the dispatcher explicitly forbids
starting other agents, and independent review is assigned to the maintainer.
I reopened the current node and the final module. The field, coefficient ring,
finite index, geometric sections, closed images, disjointness and section identities
all match the section's explicit variables. I checked the directions of every
composition: section pullback comparison, derived counit restriction, open-unit
component iso, sum-unit injection, each projection of delta, and the actual homEquiv
adjunct. In particular `e.inv` is normalized by injections, while `e.hom` is used
before projections; no inverse or adjunction direction is silently swapped.
I checked all thirteen conclusion clauses above, both zero-complement clauses,
naturality on derived morphisms, and the empty-index case. Lean elaboration found
notation/field-resolution issues and a global `Pi.map` name collision, all repaired
before the clean compile. No mathematical statement change resulted. All definitions
have explicit real data, and neither existential family is unconstrained: the stated
component equations uniquely characterize it. No dependency wait, extra assumption,
new independent notion, or another agent's file is involved.
