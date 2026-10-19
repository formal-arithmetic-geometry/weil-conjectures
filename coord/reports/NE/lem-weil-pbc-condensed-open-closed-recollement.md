## Worker report

The module states ordinary bounded-below open/closed recollement for arbitrary
commutative condensed coefficients. Its only declaration is a theorem with `sorry`;
no new definition, dependency repair, or statement correction is introduced.

Hypotheses and objects, clause by clause:

- `universe u`, `Scheme.{u}`, `Profinite.{u}`, and `Ab.{u + 1}` retain the
  small-site size convention, including the different object and arrow universes.
- `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ]`, and
  `[IsCommMonObj Λ]` encode an arbitrary commutative condensed ring, using the
  coefficient node's internal ring-object encoding. No prime, field, discrete,
  torsion, completeness, or constructibility restriction is imposed.
- `i : Z ⟶ X`, `[IsClosedImmersion i]`, `j : U ⟶ X`, `[IsOpenImmersion j]`,
  `[QuasiCompact j]`, and the explicit `hij : Set.range j = (Set.range i)ᶜ`
  encode precisely the closed immersion and its quasi-compact open complement.
- `condensedRingObj Λ T` is the recorded coefficient ring `p_T^* Λ`.
  `Mod (Sheaf (Scheme.ProEt.topology T) Ab) (condensedRingObj Λ T)` is exactly
  the internal module category of the coefficient node. `DerivedCategory.Plus`
  means bounded below in cohomology, with no upper bound or completion.

Conclusions, clause by clause:

- `PreservesFiniteLimits` and `PreservesFiniteColimits` state exactness of
  `upperStar Λ j`, `openImmersionLowerShriek Λ j`, `upperStar Λ i`, and
  `lowerStar Λ i`. The existential closed exactness witness is a conclusion,
  used to elaborate the exact termwise derived closed direct image.
- The two `PreservesColimitsOfSize.{u + 1, u + 1}` clauses give all small
  sheaf colimits within the chosen size bound.
- `Full`, `Faithful`, and `Nonempty (lowerStar Λ i ⋙ upperStar Λ i ≅ 𝟭 _)`
  give closed full faithfulness and the stated restriction identity.
- `ishriek` is a sheaf right adjoint of the actual closed direct image.
  Its adjunction characterizes it up to unique compatible isomorphism, rather
  than choosing arbitrary data from a mere existence claim in a definition.
  Its additive and left exact structures allow the existing right derived functor.
- `aj`, `bj`, `ai`, `bi` are the four adjunctions on `DerivedCategory.Plus`.
  Equalities identify them with the existing open derived adjunction, the
  existing pullback/direct-image derived adjunction, the exact closed derived
  adjunction, and `ash.derivedPlus`, respectively. Naturality of all Hom
  bijections is part of `Adjunction`, not an extra hypothesis.
- Derived closed `Full`, `Faithful`, and invertible `ai.counit` assert the
  derived version of the closed identity.
- `K.IsGE a → (ishriek.rightDerivedFunctorPlus.obj K).IsGE a` gives exactly
  left t-exactness of `Ri^!`, for every integer bound.
- `δ` and `ε` are natural transformations, so their components supply natural
  connecting maps. The two `Triangle.mk ... ∈ distTriang _` clauses state
  the distinguished triangles with first two maps exactly `aj.counit`,
  `ai.unit`, and `bi.counit`, `bj.unit` in that order.
- The exact termwise derived functors already carry their canonical shift
  comparisons. The two right derived functors acquire shift comparisons;
  `Adjunction.CommShift` for all four adjunctions and `NatTrans.CommShift`
  for both connecting maps give the shift compatibilities of the functors,
  triangles and adjunction bijections. The imported signed shift instance
  uses `(-1)^(an)`, retaining the distinguished-triangle signs.
- The two final families, one for X and one for U, give, for each integer a,
  an actual functor `I` on bounded-below complexes and a natural augmentation
  `α`. On inputs with cohomology ≥ a this augmentation is a quasi-isomorphism;
  every output has injective terms and terms zero below a. Invertibility of
  the corresponding `rightDerivedFunctorPlusUnit` states that these very
  models compute the right derived functors. Thus a single functor serves a
  whole diagram with common bound a; no unbounded replacement is claimed to
  preserve a term bound without a truncation.

Sources opened: Stacks `proetale.tex`, labels lemma-closed-immersion (09AA),
lemma-closed-immersion-complement-retrocompact-exact (09BM),
lemma-open-immersion (09BN), lemma-ses-associated-to-open (09AH).
The Hemo--Richarz--Scholbach PDF was read as extracted text around (3.3),
(3.4), Lemma 3.4 and the proof of Lemma 5.3(2). The theorem docstring records
all nine steps of the DAG proof, including the explicit cone and the
common-bound good-truncation construction.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `DerivedCategory.Plus` is the cohomologically bounded
  below full subcategory, supplied by the derived-operation imports.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`
  and its Basic / UpperLowerStar dependencies: `condensedRingObj`,
  `coefficientPullbackIso`, `CondensedRing.upperStar`, `CondensedRing.lowerStar`,
  and `upperStarLowerStarAdjunction`, all from the coefficient node's recorded
  declaration family. Their full definitions and the ordinary/derived
  adjunction signatures were inspected in the read-only 51-module framework.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`:
  `derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus` and the recorded
  exact `openImmersionLowerShriek` construction.
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`:
  `Adjunction.mapDerivedCategoryPlusAdjunction`; its PlusAdjunction dependency:
  `Adjunction.derivedPlus` and its unit/counit normalization formulas.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`: the recorded
  `Scheme.proEtaleRingDerivedPullback`, plus the module operations and exactness
  it packages, imported as proof input. The statement uses the coefficient
  node's internal module presentation rather than privately redefining modules.
- Proof imports include `Scheme.proEtale_ringed_open_closed`,
  `SheafOfModules.localizedModule_adjunction_exact`,
  `CochainComplex.exists_functorial_bounded_injective_resolution`, the generic
  exact-derived, derived-adjunction, K-injective and triangle interfaces named
  in the node's proof dependencies.
- The remaining convention dependencies introduce no declaration; their
  universe and morphism-property meanings are written explicitly above.

Edge cases checked: empty U (the first triangle reduces to the closed identity),
empty Z (the second triangle reduces to the open identity), empty X, the zero
coefficient ring and zero complexes. No nonemptiness, Noetherianity, qcqs
assumption on X, upper cohomological bound or restriction on integer a is added.
Quasi-compactness is on j, as required by 09BM and 09AH. The closed subscheme
need not be reduced. Cohomological lower bounds are distinct from termwise lower
bounds, and the final models explicitly bridge them by a quasi-isomorphism.

Searches actually run:

- `msearch.py leanfinder`: “Open closed recollement distinguished triangles for
  condensed module sheaves on the proetale site” returned eight light-condensed
  Grothendieck/monoidal/solid-module results; none states this recollement.
- `msearch.py loogle`: `"recollement"` returned zero hits.
- `msearch.py grep`: `recollement|Recollement` returned zero Mathlib hits.
- `msearch.py leansearch`: “Open closed recollement derived category sheaves of
  modules” returned HTTP Internal Server Error; recorded as unavailable.
- `rg` over upstream WeilConjectures and project Sheaf found finite-coefficient
  recollement material and the condensed-continuity theorem's proof references,
  but no declaration of this arbitrary-coefficient recollement theorem.
  A search of upstream by the exact item ID also returned no hit.
- The framework inventory explicitly records that recollement has no complete
  matching upstream declaration. Existing open adjunction and derived-functor
  primitives are reused, not duplicated.

Validation: `scompile.py NE lem-weil-pbc-condensed-open-closed-recollement`
compiled both the sandbox view (8.2 s) and module view (9.5 s), with no warnings.
The delivery dry run is the final mechanical check. No direct repository edits
or Git commands were run.


## Second reading by NE

Independent second reader, 2026-10-15. Read the node, its nine proof steps,
the complete delivered module, the statement-dependency records and the actual
framework declarations. No mathematical mismatch was found; the Lean and node
are unchanged. This section adds the independent audit, searches and validation.
There are no new definition nodes, dependency modules or statement corrections.

The node's objects, hypotheses and conclusions, matched in order:

1. Size convention and scheme X: `universe u`, `{X U Z : Scheme.{u}}`,
   `Profinite.{u}` and `Ab.{u + 1}`. Verdict: matches the fixed small-site
   convention; the site retains object universe u+1 and arrow universe u.
   No equality of those universes is imposed. The scheme structure is Mathlib's
   locally affine locally ringed space, not a more restrictive scheme class.
2. Closed immersion and quasi-compact complementary open: `(i : Z ⟶ X)`
   `[IsClosedImmersion i]`, `(j : U ⟶ X)` `[IsOpenImmersion j]`
   `[QuasiCompact j]`, `hij : Set.range j = (Set.range i)ᶜ`.
   Verdict: exactly the node's geometry. Mathlib's morphism quasi-compactness
   is local on the target, so it says retrocompact complement, not compact U
   or compact X. The closed structure need not be reduced.
3. Arbitrary commutative condensed coefficient ring: `Λ : Sheaf
   (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ]`
   `[IsCommMonObj Λ]`. Verdict: internal unital commutative ring in abelian
   sheaves, equivalent to the node's sheaf of commutative rings. There is no
   field, prime, torsion, topology on a coefficient field, or completeness
   assumption. HRS section 3 explicitly allows any condensed commutative ring.
4. Coefficients Λ_T and D+(T,Λ): `condensedRingObj Λ T` and
   `DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
   (condensedRingObj Λ T))`. Verdict: the coefficient node records exactly
   this internal-module presentation. Read `Basic.lean`: `upperStarFromPoint`
   is point inverse image followed by the scheme structure inverse image;
   `condensedRingObj` is its value at Λ. Read Mathlib's derived Plus and IsGE:
   the bound is a cohomological bound, not an upper bound or a completion.
5. Exact sheaf functors j^*, j_!, i^*, i_*: the first existential `hclosed`
   supplies `PreservesFiniteColimits (lowerStar Λ i)`; the following finite
   limit/colimit conjuncts give exactness of all four named sheaf functors.
   Verdict: matches. In particular closed exactness is a conclusion, not an
   extra hypothesis. Read `UpperLowerStar/Defs.lean` and `LowerShriek/Defs.lean`:
   these use the canonical coefficient isomorphism and actual extension by
   zero, with underlying direct image/restriction/extension by zero as stated.
6. Small sheaf colimits: the two `PreservesColimitsOfSize.{u + 1, u + 1}`
   conjuncts for `upperStar Λ j` and `upperStar Λ i`. Verdict: all small
   diagrams within the fixed larger universe, not just finite/filtered ones.
7. Closed full faithfulness and restriction identity: `(lowerStar Λ i).Full`,
   `.Faithful`, `Nonempty (lowerStar Λ i ⋙ upperStar Λ i ≅ 𝟭 _)`, and the
   derived Full/Faithful conjuncts with `∀ K, IsIso (ai.counit.app K)`.
   Verdict: both sheaf and derived identities have the right orientation;
   the derived identity uses the actual adjunction counit.
8. The two chains of adjunctions: `aj`, `bj`, `ai`, `bi` have respectively
   j_! ⊣ j^*, j^* ⊣ Rj_*, i^* ⊣ i_*, i_* ⊣ Ri^! as functor types.
   Their equality conjuncts identify the existing canonical open adjunctions,
   `upperStarLowerStarAdjunction.mapDerivedCategoryPlusAdjunction`, and
   `ash.derivedPlus`. Verdict: units/counits are fixed by the sheaf adjunctions;
   these are not unrelated arbitrary adjunction structures. The existential
   sheaf `ishriek` is characterized by `ash : lowerStar Λ i ⊣ ishriek`;
   it is determined up to compatible unique isomorphism. No hollow definition
   or arbitrary functor is used in place of a canonical operation.
9. Left t-exact Ri!: `∀ K a, K.IsGE a →
   (ishriek.rightDerivedFunctorPlus.obj K).IsGE a`. Verdict: precisely the
   asserted cohomological lower bound, for every integer a.
10. First natural triangle: `δ` has type i_*i^* → j_!j^*[1], with functor
    composition written in Lean's left-to-right order. The first
    `Triangle.mk` uses `aj.counit.app K`, `ai.unit.app K`, `δ.app K`.
    Verdict: j_!j^*K → K → i_*i^*K → j_!j^*K[1], with the specified maps.
11. Second natural triangle: `ε` has type Rj_*j^* → i_*Ri^![1]. The second
    `Triangle.mk` uses `bi.counit.app K`, `bj.unit.app K`, `ε.app K`.
    Verdict: i_*Ri^!K → K → Rj_*j^*K → i_*Ri^!K[1], with specified maps.
    Both connecting arrows are natural transformations, not pointwise choices.
12. Shift compatibility: the two existential right-derived `CommShift`
    structures, `aj.CommShift` through `bi.CommShift`, and
    `NatTrans.CommShift δ`/`ε`. Verdict: encodes the functors, adjunction
    bijections and triangles commuting with shifts. Read the imported
    `Triangulated/TriangleShift.lean`: the target shift [1] uses the signed
    comparison `(a*n).negOnePow`, so the connecting arrows have the required
    anticommutation for odd shifts. No unsigned triangle claim is substituted.
13. Functorial bounded-below injective models: the two final `∀ a : ℤ, ∃ I α`
    families are on X and U, the domains of Ri! and Rj*. `α` is natural on
    chain maps; `K.obj.IsGE a → QuasiIso (α.app K)` gives the representing
    quasi-isomorphism on inputs with the common cohomological bound;
    `IsStrictlyGE a` and termwise `Injective` give zero terms below a and
    injective terms. Invertibility of each `rightDerivedFunctorPlusUnit` on
    these actual models says that they compute the right derived functor.
    Verdict: the node's common-bound models, without assuming an unbounded
    replacement preserves bounds. Allowing I to depend on a is essential;
    demanding quasi-isomorphism only for the corresponding cohomological
    range is exactly good truncation followed by resolution.

Source checks: opened Stacks `proetale.tex` at
`lemma-closed-immersion` (09AA),
`lemma-closed-immersion-complement-retrocompact-exact` (09BM),
`lemma-open-immersion` (09BN) and
`lemma-ses-associated-to-open` (09AH). The first and third require no global
finiteness; the second and fourth require the quasi-compact complement already
present. Independently extracted and read HRS section 3's standing conventions,
(3.3), (3.4), Lemma 3.4 and the proof of Lemma 5.3(2). The constructible closed
immersion there has retrocompact open complement. Ordinary bounded-below
categories and the detailed common-bound construction are the node's explicit
form of the recollement, using the Stacks inputs, not a claim about an unrelated
completed category. All nine proof steps are carried by the theorem docstring,
including the sheaf kernel construction, canonical truncation, cone fibre,
representing adjunction and signed shift descent.

Dependency checks: the coefficient framework imports and definitions were read
in this clone's `lean/WeilConjectures`, as required by
`coord/pefw-upstream-framework.md`, not inferred from the older source tree.
The actual open Plus adjunction is the exact termwise derived adjunction; the
actual upper/lower Plus adjunction has exact pullback on the left and the right
derived direct image on the right. Read their definitions, the exact-derived
adjunction signature and `PlusAdjunction.lean`'s exact-left-adjoint hypotheses.
Read `ProEtaleOperations.lean`: it handles arbitrary identified sheaves of rings
by genuine tensor pullback and direct image. It is a proof input here; the
statement uses the already recorded internal-module coefficient presentation,
not a private copy of that category. The convention-only dependencies introduce
no object to import or recreate. No unusable statement dependency was found.

Edge cases: empty X, empty U, empty Z, zero ring and zero complexes are all
allowed. The empty-open triangle reduces to the closed identity, and the
empty-closed case to open restriction. There is no Nonempty assumption on sites,
objects, or index types. There is no index set or natural-number degree n in the
statement to exclude its empty/zero case. Bounds and shifts range over all ℤ,
including zero and negative integers. Coefficient characteristic is arbitrary.
The size bound allows the whole chosen small site and all its small diagrams.
Every universe and variable is explicitly bound, with no file-local notation,
private definition or local instance in the delivered file.

Independent searches, using different words from the first worker:

- `msearch.py leanfinder`: “closed immersion open complement derived adjunction
  exceptional inverse image module sheaves” returned eight declarations about
  Zariski module restriction or scheme immersions; inspected returned types,
  none concerns condensed pro-etale coefficients or these two derived triangles.
- `msearch.py loogle`: `"open_closed"` returned six valuation closed-ball
  results, none a candidate.
- `msearch.py grep`: `exceptionalInverseImage|localizationTriangle|localisationTriangle`
  returned no Mathlib matches.
- Independent `rg` over Mathlib, upstream WeilConjectures and project Sheaf for
  `recollement|localizationTriangle|localisationTriangle|open_closed|openClosed`
  found existing etale localization triangles and the project's arbitrary-ring
  sheaf short exact sequence, but no complete condensed recollement statement.
  Opened `SixFunctors/OpenClosed/Derived.lean`'s
  `Etale.exists_distTriang_openClosed`: it is on `X.smallEtaleTopology` with
  constant category coefficients, and supplies only one pointwise triangle.
  It does not match this node. The project's condensed continuity file only
  cites this node in its proof plan. Framework primitives are reused.

Validation: `lean.statement` was compared by exact string equality against the
source from `theorem` to `:=`, and matches. The prescribed `scompile.py` compiled
this delivered module in sandbox view (8.3 s) and library view (9.4 s), with no
warnings or errors. One theorem and one `sorry` remain, as stage 2 requires;
there are no definitions with postponed data and no proofs added. Only this
second-reading report was changed.
