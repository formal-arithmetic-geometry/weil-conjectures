## Worker report

The main theorem is specialization_cospecialization_compatibility:
f : X → S, QuasiCompact f, QuasiSeparated f, G an abelian small-etale sheaf,
IsLocallyAcyclicRelative f G, algebraically closed fields Ω and Ω', s a geometric
point of S, and t any geometric point of its strict henselization. Its equality
is derived specialization followed by the t-fibre map and cospecialization,
equal to the closed-fibre map. There are no properness or torsion assumptions.
The coefficient is singleFunctor 0 G; inverse images, derived direct images,
derived exchange, exact stalks and global sections are existing project APIs.
The fibres are the specified iterated pullbacks. Degree-zero and inverse-image
composition isomorphisms transport to the precise coefficients of the statement.

Searches: msearch leanfinder "specialization and cospecialization commute with
derived etale fibre cohomology maps" returned eight Zariski structure-sheaf stalk
identities, not this result. Loogle "cospecialization" and Mathlib grep
"cospecialization|specialization.*derived" under AlgebraicGeometry returned zero
hits. LeanSearch for derived specialization/cospecialization arrows was unavailable
(Internal Server Error). Searches of WeilConjectures and lean/Sheaf found the
sheaf-level EtaleStalkSpecialization, DerivedGlobalGerm, derived exchange and the
inline derived-unit/Leray comparison; these are reused. DAG searches and
blueprint_refs.py search cospecialization found no existing definition of the
combined derived arrows.

Edge cases considered: the zero sheaf, empty X, arbitrary (not necessarily
algebraic over its residue field) t, the distinguished closed lift itself, and
absence of properness/torsion. The definitions use only the closed-unit
isomorphism supplied by local acyclicity and the identity-point germ isomorphism;
no specialization or fibre map is inverted. The main statement remains unchanged.

## New nodes

def-weil-pbc-specialization-cospecialization-arrows packages naturality and
the exact derived extension of the existing specialization map, the fibre maps
via derived exchange and the canonical identity-point derived global germ, and
cospecialization via inverse Leray, restriction, and the inverse closed-fibre unit.
Source: Stacks Tags 0GJ2, 0GJU, 0GJV. Every definition has actual data; the
naturality proof is a named postponed theorem with its proof in the docstring.
The new node explicitly states this naturality. All searches are recorded.

## Dependency modules

lem-weil-pbc-geometric-point-pullback-stalk: GeometricPointCanonicalGerm exposes
invertibility of the canonical globalGerm at the identity point of Spec Ω.
The previous record provided only Nonempty of an isomorphism and no canonical
map normalization. The old full equivalence, exactness, module and stalk
statements are preserved by public import. Its proof docstring explains the
pointed-section argument, or the strictly henselian sections-to-stalk theorem.

lem-weil-pbc-strict-henselization-functoriality: StrictHenselizationClosedLift
exposes the clause-(1) equality evaluationLift ≫ structuralMap = s, needed for
transporting the source of the closed fibre map. The old interface exposes the
canonical strict-local map but not this factorization. The original module is
publicly imported. Its proof is the cocone evaluation identity followed by
pointedness of any representative affine neighbourhood.

lem-weil-pbc-cohomology-pullback-derived-unit: CohomologyPullbackCanonicalArrows
names the actual canonical Leray isomorphism and the derived unit followed by
Leray as etaleDerivedRestriction. The original record spells them only inline;
the old comparison theorems are retained by public import. No arbitrary map or
isomorphism is chosen, and no mathematical hypothesis is changed.


Clause-by-clause correspondence (main node unchanged):

- A morphism of schemes is `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Quasi-compact and quasi-separated are `[QuasiCompact f] [QuasiSeparated f]`.
- The abelian étale sheaf is `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`;
  relative local acyclicity is `hG : IsLocallyAcyclicRelative f G`.
- The geometric points have explicitly bound fields, `Field` and `IsAlgClosed` instances,
  with `s : Spec (.of Ω) ⟶ S` and arbitrary
  `t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s`. Neither field extension
  is required to be algebraic over the residue field.
- `Scheme.strictHenselizationStructuralMap s` is the map from S' to S.
  `Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s))`
  is its canonical closed lift. `strictHenselizationClosedLift_over s` gives its
  composite with the structural map as s, used by `closedStrictBaseSheafFiberMap`.
- X' is `pullback f (Scheme.strictHenselizationStructuralMap s)`, p is its first
  projection, and f' is `strictBaseChangeMap f s`, its second projection.
  The two geometric fibres are `pullback (strictBaseChangeMap f s) t` and the same
  pullback at the closed lift. Their inclusions are `strictBaseFiberInclusion`.
- G' is `(upperStar AddCommGrpCat.{u + 1} p).obj G` and degree zero is
  `DerivedCategory.Plus.singleFunctor _ 0`. G_t is its exact inverse image under h.
  The canonical `mapDerivedCategoryPlusSingleFunctor` and `upperStarCompDerivedPlus`
  comparisons retain these precise coefficient objects in the fibre maps.
- β is `(upperStarLowerStarAdjunction _ h).derivedPlus.unit.app K'`.
  `etaleCospecialization` applies `(etaleLerayPlus h).inv.app`,
  `etaleDerivedRestriction i`, and RΓ of the inverse of the image of β under
  `(upperStar _ i).mapDerivedCategoryPlus`. Only this last image is inverted by
  local acyclicity, using the recorded closed-fibre-unit theorem.
- Derived stalks are `(Scheme.pointSmallEtale _).sheafFiber.mapDerivedCategoryPlus`.
  `derivedEtaleStalkSpecialization s t` derives exactly the existing pointed-germ
  map `etaleStalkSpecialization`, with the target at `t ≫ structuralMap s`.
- `etaleDerivedFiberMap` first uses `derivedGeometricPointStalkIso` inversely,
  then applies the identity-point exact stalk to `derivedBaseChangeMapPlus`,
  then inverts `derivedGlobalGerm` on Spec Ω. This is exchange followed by
  global sections and Leray: that global germ is defined as inverse Leray followed
  by the derived global germ at the point. `isIso_globalGerm_identity` fixes the
  canonical, rather than arbitrary, identification. The iterated-pullback version
  is `strictBaseSheafFiberMap`; the closed version transports its source over s.
- Diagrammatic composition `sp ≫ strictBaseSheafFiberMap ≫ etaleCospecialization =
  closedStrictBaseSheafFiberMap` is exactly cosp ∘ ρ_t ∘ sp = ρ_s.
  No invertibility of these four arrows is asserted.

Dependency declarations reused (the `AlgebraicGeometry.Etale` namespace is abbreviated):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`.
- `Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf`: `IsLocallyAcyclicRelative`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`,
  `Scheme.strictHenselizationScheme`; `StrictHenselizationCanonicalMap`:
  `Scheme.strictHenselizationMap_existsUnique` (retained by public import).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`; `UpperLowerStar.Stalk`: `upperStarCompSheafFiberIso`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlus` and the composition/degree-zero comparisons;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `Adjunction.derivedPlus`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded derived-category interface;
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `rightDerivedGlobalSections`,
  `cohomology`. Their bounded-below versions use `Sheaf.Γ.rightDerivedFunctorPlus`.
- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`:
  `derivedCohomologyPullback_eq_derivedUnit`, `lerayPlus_on_kInjective`,
  `lowerStar_isKInjective_boundedBelow`, all retained by public import.
- `Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit`:
  `isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`: `derivedBaseChangeMapPlus`;
  `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.sheafFiber`;
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`.
- `Sheaf.AlgebraicGeometry.EtaleStalkSpecialization`: `etaleStalkSpecialization`;
  `Sheaf.AlgebraicGeometry.DerivedGlobalGerm`: `globalGerm`, `derivedGlobalGerm`,
  `isIso_derivedGlobalGerm`. The scheme-conventions node is a convention record;
  its QuasiCompact and QuasiSeparated notions are the standard classes.

The named postponed theorems are the main compatibility theorem,
`etaleStalkSpecialization_naturality`, `isIso_globalGerm_identity`, and
`Scheme.strictHenselizationClosedLift_over`. Each has a source and full proof
plan in its docstring and is covered by its owning node statement. All definitions
have actual data; choosing unique strict-local restrictions is inherited, not a
choice from an undetermined existence proposition. The supplied helper instance
for additive geometric stalks is the existing `Point.sheafFiber_additive` value.
No mathematical statement correction or STATEMENT-DISPUTED flag is needed.

Repair of the earlier attempt: removed the obsolete compilation-tool objection,
used the now-authorized local-overlay wrapper, and wrapped the overlong derived
specialization comparison line. The independent second reading remains for the
second reader; this worker does not supply it.

Compiler repair: `geometricStalkCoefficientsAB5` supplies exactly
`AB5OfSize_shrink.{u, u, u + 1, u + 1} AddCommGrpCat.{u + 1}`. This is
the coefficient-size instance already used locally by DerivedGlobalGerm; exposing it
lets typeclass search find exactness of all stalks without restricting universes.
The specialization comparison also now uses a correctly parsed field projection.

`geometricSheafFiber_preservesFiniteLimits` applies Mathlib's existing finite-limit
instance directly in the fixed coefficient universe. The closed-fibre transport
binds its point and coefficient type explicitly to avoid an unresolved dependent
typeclass obligation under congrArg. Neither helper assumes an extra mathematical
hypothesis.

Validation: all five modules compiled individually through scompile.py in the
private side-project overlay. The first dry run caught a style warning in the
finite-limit helper; it was repaired by using an ordinary local proposition
binder. The new node's three grouped inverse/direct-image citations were expanded
to individual citations to match its dependency list exactly.

## Second reading by NH

Step 1 list and correspondence with the node/source:

- The morphism of schemes `f : X ⟶ S` is rendered by `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The hypotheses that `G` is an abelian étale sheaf and that `f` is locally acyclic relative to `G` are rendered by `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` and `hG : IsLocallyAcyclicRelative f G`.
- The geometric point `s : Spec Ω ⟶ S`, with Ω algebraically closed, is rendered by `[Field Ω] [IsAlgClosed Ω]` and `s : Spec (.of Ω) ⟶ S`.
- The strict henselization `S'`, its structural map, and the arbitrary geometric point `t` are rendered by `Scheme.strictHenselizationScheme s`, `Scheme.strictHenselizationStructuralMap s`, and `t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s`, with independent algebraically closed field Ω'.
- The pullback `X'`, its projection, and the two fibre inclusions are represented canonically by `strictBaseChangeMap f s` and `strictBaseFiberInclusion f s t` (and the same construction at the canonical closed lift).
- The pulled-back sheaf and degree-zero complexes are rendered by `upperStar ... p`, `DerivedCategory.Plus.singleFunctor _ 0`, and the corresponding `upperStar` along `h`; no arbitrary replacement complex is used.
- The derived adjunction unit β is the canonical `upperStarLowerStarAdjunction _ h` derived unit in `etaleCospecialization`; its inverse image at the closed fibre is inverted only under `hG` through the recorded local-acyclicity unit theorem.
- The Leray identification and derived restriction in cospecialization are the canonical `etaleLerayPlus` and `etaleDerivedRestriction` maps, with inverse Leray and inverse closed-fibre unit in the stated order.
- The fibre maps ρ at s and t are rendered by `strictBaseSheafFiberMap`; the specialization map is the derived `derivedEtaleStalkSpecialization`; the closed-fibre map is `closedStrictBaseSheafFiberMap` transported along `strictHenselizationClosedLift_over`.
- The additional quasi-compact and quasi-separated assumptions are exactly `[QuasiCompact f] [QuasiSeparated f]`, matching the source lemma's “in addition” clause. No properness or torsion assumption occurs, and no arrow is asserted invertible in the target theorem.
- The conclusion `cosp ∘ ρ_t ∘ sp = ρ_s` in `D⁺(Ab)` is exactly the Lean equality
  `derivedEtaleStalkSpecialization ... ≫ strictBaseSheafFiberMap ... ≫ etaleCospecialization ... = closedStrictBaseSheafFiberMap ...`; composition order is the categorical order corresponding to the displayed source square.

Edge cases checked: `G = 0`, empty X, the canonical closed-point lift (`t` equal to that lift), an arbitrary geometric t over the strict henselization, and degree zero (`singleFunctor _ 0`) are all admitted. No nonemptiness, properness, torsion, finite-type, or characteristic hypothesis was added; Ω and Ω' are independently quantified, and the universal `u` covers the source's scheme/coefficient universe. The statement does not invert specialization, cospecialization, or fibre maps.

Searches were rechecked with `rg` over `WeilConjectures/` and `lean/Sheaf`, Mathlib/LeanFinder searches recorded in `searches.jsonl`, and the Stacks source at Tag 0GJV. Only generic stalk-specialization identities were found; no existing combined theorem or canonical cospecialization declaration matches this node. Therefore the node is not marked existing.

Mismatches found: none in the main statement or dependency interfaces. The worker's five modules compiled together through `scompile.py`; no Lean repair was required in this second reading. The report's prior compiler repairs and dependency-module additions were checked against their node signatures and source places and remain valid.
