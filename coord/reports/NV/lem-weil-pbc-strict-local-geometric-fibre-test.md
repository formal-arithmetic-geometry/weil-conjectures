## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalGeometricFibreTest` states
`AlgebraicGeometry.Etale.strictLocalGeometricFibreTest`. All theorem proofs are `sorry`.
No change to the item's already-corrected mathematical statement is needed.

Hypotheses and clauses, matched individually:

- A morphism of schemes is `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The geometric point is `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, and
  `x : Spec (.of Ω) ⟶ X`. Its image is the composite `x ≫ f`.
- A and B are the existing `Scheme.strictHenselizationScheme (x ≫ f)` and
  `Scheme.strictHenselizationScheme x`; their structural maps are the existing
  `Scheme.strictHenselizationStructuralMap`. The new dependency interface exposes
  the unique canonical map as `Scheme.strictHenselizationMap f x`.
- The arbitrary separably closed field is `(K : Type u) [Field K] [IsSepClosed K]`.
  No algebraic extension or chosen algebra structure is assumed.
- The selected morphism is `u : Spec (.of K) ⟶ A`. The morphism t is written out as
  `u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f)`.
- The abelian etale sheaf is
  `F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The degree is `(q : ℕ)`, including zero.
- The first comparison is `cohomologyPullbackOver (strictLocalComparisonMorphism f x u)
  (pullback.snd ... ...) F q`. The scheme map is `pullback.map` induced by the canonical
  strict-local map and the identity of Spec K. Its source is B ×_S Spec K and target
  A ×_S Spec K. The coefficient on the target is the inverse image along its second
  projection. The coefficient on the source is the inverse image along the composite
  with that projection, which equals the second projection of B ×_S Spec K by
  `pullback.lift_snd` and `Category.comp_id`. The helper composes the recorded
  `cohomologyMap` with `Sheaf.H.map` of the inverse-image composition isomorphism,
  so these are the actual canonical maps, with canonically identified coefficients.
- Isomorphism of abelian groups is `Function.Bijective` on the additive homomorphism.
  The node's equivalence is `↔`.
- EVERY lift is `∀ v : Spec (.of K) ⟶ A`; the subsequent equality asserts that its
  composite to S equals t. There is no condition identifying v with the selected u.
- The fibre comparison is the recorded `cohomologyMap (pullback.snd h v) F q`.
  This is H^q(Spec K,F) to H^q(B ×_{A,v} Spec K,pr₂⁻¹ F).
- The stated particular implication for u follows directly by specializing the
  quantified right side to `v = u` and reflexivity of the composite equality.
- No smoothness, properness, finite-type, torsion, algebraicity, or characteristic
  hypotheses are present.

Dependency declarations read and used: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`
(`Mathlib.AlgebraicGeometry.Scheme`); `CategoryTheory.Limits.pullback`, its projections,
and `pullback.map` (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`);
`Scheme.SpecToEquivOfField` and the inline geometric point convention;
`Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme` and its canonical cone
(`Sheaf.AlgebraicGeometry.StrictHenselization`); `CategoryTheory.Sheaf` on
`Scheme.smallEtaleTopology`; `Etale.upperStar` and `Etale.upperStarComp`
(`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`);
`Etale.cohomology` (`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`), with the
existing cohomology node's recorded `Sheaf.H` presentation and stage-3 comparison;
`Etale.cohomologyMap`
(`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`);
`strictHenselizationResidue` and `strictHenselizationFunctoriality`
(`Sheaf.Paper.StrictHenselizationFunctoriality`); `IsSepClosed`
(`Mathlib.FieldTheory.IsSepClosed`). The two landed structural-map and point-evaluation
nodes are added to stmt_deps, as their definitions occur in the helper interface.
Every recorded proof-dependency module is imported; unstated proof prerequisites are
not duplicated. The full seven-step natural-language proof from the node is in the
main theorem docstring.

Edge cases: q = 0 uses the unit comparison, not an assumed positive-degree vanishing;
the zero sheaf is allowed; empty X has no geometric point and hence contributes no
excluded instance; the set of lifts is nonempty because u itself is a lift, but v need
not equal u. Arbitrary characteristics and nonalgebraic K are retained. All site
objects and fields use one common size universe u with abelian coefficients at u+1;
no equality of distinct site object/morphism universes is imposed.

Searches for an existing statement:

- msearch LeanFinder, query `etale cohomology strict localization comparison geometric
  fibres separably closed field`: eight hits about etale algebra/localization,
  no strict-local cohomology comparison.
- msearch Loogle, query `cohomologyMap`: zero hits, unknown identifier.
- msearch grep, query `strictHenselization|cohomologyMap`, directory
  `AlgebraicGeometry`: zero Mathlib hits.
- msearch LeanSearch, query `etale cohomology strict localization geometric fibre
  comparison`: service unavailable (Internal Server Error).
- rg in upstream WeilConjectures and project lean/Sheaf for the item id and
  `geometric.fibre.test|strict.local.*fibre`: related fibre comparison modules only;
  none states this equivalence. The upstream `cohomologyMap` was read in full and reused.
- rg for definitions involving `strictHenselization` in lean/Sheaf found the existing
  ring, scheme, structural map and point evaluation, but no canonical functorial
  map definition. The dependency's residue-parametrized theorem was read in full.

Source checked: local `literature/stacks-project/etale-cohomology.tex`,
`lemma-check-stalks-better` (Tag 0EZV). The node already records the correction of the
source's single-selected-lift claim to every lift. This delivery preserves that
correction and proof verbatim. This is an inherited stage-1 correction already present
on the base; there is no stage-2 `statement_change` record and this delivery makes no
further mathematical statement correction.

Validation: both delivered files compiled separately, in dependency order, through
scompile.py on the server, nice 19, two threads, 60 seconds per file, without errors
or unexpected warnings. Canonical-map adapter: 1.4 s; main theorem: 9.4 s.

## Dependency modules

`lem-weil-pbc-strict-henselization-functoriality`: the recorded theorem supplies a
local homomorphism after callers supply residue identifications and their complete
pointing equations. It is mathematically adequate, but does not expose the canonical
scheme morphism needed here without those auxiliary choices. The adapter
`Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap` publicly imports and retains
both original statements (all four clauses), states the equivalent unique pointed
morphism interface, and defines `Scheme.strictHenselizationMap` from that uniqueness.
The property tying the choice to evaluation is part of the existence-uniqueness
statement, so this is not an arbitrary morphism or a choice from mere Nonempty.
Its structural-square theorem is a named postponed consequence of that same DAG
node. The dependency copy changes only lean; lean.note explains the repair.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader assigned by the dispatcher. This worker has
not performed or claimed an independent second reading. This section reserves the
required report location for that reader; this is a dry run only, with no delivery.


## Second reading by NV

Independent reading of the node, the two delivered modules, the dependency node,
and the actual recorded dependency sources. I did not write these statements.

Objects, hypotheses and conclusions, checked item by item:

1. Arbitrary schemes X and S and a morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   These are Mathlib schemes and scheme morphisms, without separation, finiteness,
   smoothness or properness instances. Verdict: exact.
2. A geometric point of X and its image in S: `{Ω : Type u} [Field Ω]
   [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)` and `x ≫ f`. This is the recorded
   inline geometric-point convention, not a rational-point restriction. Verdict: exact.
3. A and B: `Scheme.strictHenselizationScheme (x ≫ f)` and
   `Scheme.strictHenselizationScheme x`. I read StrictHenselization.lean: their rings
   are the small representative affine pointed-etale coordinate-ring colimits and
   the schemes are their spectra. Their structural maps are the existing
   `Scheme.strictHenselizationStructuralMap`, characterized by the limit legs.
   Verdict: the dependency objects, not alternate strict-local constructions.
4. The canonical h: `Scheme.strictHenselizationMap f x`. The adapter's unique
   witness is characterized by BOTH the structural square and the equation on
   the specified geometric-point evaluations. PointEvaluation.lean constructs
   those evaluations by `colimit.desc`; its data is not postponed. Pointedness
   forces the closed point to the closed point, so the corresponding ring map is
   local. Under the residue identifications in `strictHenselizationResidue`, its
   evaluation equation is precisely the prescribed residue inclusion of clause
   (3). Verdict: canonical h, not an arbitrary morphism over S.
5. Arbitrary separably closed K: `(K : Type u) [Field K] [IsSepClosed K]`.
   I read `IsSepClosed.splits_of_separable`; neither algebraic closedness nor an
   algebraicity condition relative to a residue field is imposed. Verdict: exact.
6. The selected u and t: `u : Spec (.of K) ⟶ A`, with t written as
   `u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f)`. The common base map is
   used on both fibre products. Verdict: exact; no independent incompatible t.
7. Abelian etale coefficients: `F : Sheaf (Spec (.of K)).smallEtaleTopology
   AddCommGrpCat.{u + 1}`; this is the recorded abelian-sheaf encoding. Cohomology
   uses the recorded `Sheaf.H` presentation of the cohomology node, with the
   recorded `cohomologyMap` for the actual canonical pullback. Verdict: exact.
8. All nonnegative degrees: `(q : ℕ)`, including zero. Verdict: exact.
9. The first comparison: `strictLocalComparisonMorphism f x u` is `pullback.map`
   with h and identities. Its domain is B ×_S Spec K and codomain A ×_S Spec K.
   The square supplied by `strictHenselizationMap_over` is correctly oriented.
   `cohomologyPullbackOver` first applies the existing `cohomologyMap`, then
   `Sheaf.H.map` of `(upperStarComp ...).inv.app F`. I read the upstream signatures:
   `upperStarComp` goes from composite inverse image to iterated inverse image,
   so its inverse has exactly the required direction. The resulting source
   coefficient is pr₂⁻¹F on A ×_S Spec K; the target coefficient is inverse image
   along p ≫ pr₂, canonically pr₂ on B ×_S Spec K. Verdict: correct canonical map
   and coefficients, not just isomorphic abstract groups.
10. Isomorphism: `Function.Bijective` on each displayed additive homomorphism.
    For abelian groups this is exactly invertibility. Verdict: exact.
11. Every lift over the same t: `∀ v : Spec (.of K) ⟶ A, v ≫ structuralMap =
    u ≫ structuralMap → ...`. The equality fixes the composite only; it does not
    identify v with u. Quantification follows the fixed F and q. Verdict: exact.
12. The fibre comparison is `cohomologyMap (pullback.snd h v) F q`; its domain
    is H^q(Spec K,F) and codomain is H^q(B ×_{A,v} Spec K,pr₂⁻¹F).
    The outer `↔` gives both implications. Specializing its forward implication
    to v = u gives the node's “in particular” clause without an additional
    theorem. Verdict: all conclusion clauses are covered.

Dependency-module reading (H13): I opened the dependency node and both existing
signatures in Sheaf.Paper.StrictHenselizationFunctoriality. Clause (1), including
strict henselianity, the closed point, separably closed relative residue field and
unique pointed residue identification, remains in `strictHenselizationResidue`.
`strictHenselizationFunctoriality` retains clauses (2), (3), (4): the inclusion,
local homomorphism, structural and residue equations, uniqueness, and compatibility
with every pair of pointed neighbourhoods. Both remain available through the
adapter's public import. The new unique pointed scheme-map formulation packages
clause (3) with the canonical evaluation from clause (1). It supplies the missing
caller interface without changing any mathematical hypotheses or losing clauses.
Its docstring explains how to extract it and recover uniqueness. I checked the
source at Tags 04HX, 03PS (including the following functoriality paragraph) and
04GU: no extra scheme hypotheses are assumed there. The chosen map comes from
unique existence; all three new postponed theorems serve this same DAG statement
and have source, blueprint and proof docstrings. No new definition node is needed.

Source and inherited correction: I read Tag 0EZV, lemma-check-stalks-better, in
etale-cohomology.tex. Its single-lift formulation and its last displayed limit
identification incorrectly treat the K-algebra splittings as A-linear. The base
node already replaces that with every lift; this delivery preserves that node
verbatim. Its seven-step proof is carried into the theorem docstring, including
clopen stalks, exact conservative sections, degree-zero units and positive-degree
vanishing. There is no new stage-2 correction to audit. I searched the DAG for
all citers: there is exactly one, lem-weil-pbc-smooth-local-acyclicity, so no second
citer exists to open. Its step 4 uses only the forward implication followed by
specialization to the selected lift; holds: true. No target statement is changed.

Edge cases: q = 0 is included and uses the unit, not positive-degree acyclicity.
The zero sheaf is allowed. An empty X cannot carry x, and an empty S cannot carry
x ≫ f, so their absence of instances is intrinsic, not an added nonemptiness
hypothesis. The lifts cannot form an empty set since u is one; other lifts remain
unrestricted. No index set occurs in the statement, and no characteristic is
excluded. All schemes and fields live in the recorded common ambient universe u;
this universe is arbitrary and can be enlarged to contain given input data.
Coefficients have the recorded size u+1; no independent site universe is equated
with another just to obtain an instance. All binders and universes are explicit.

Independent H4 searches (different queries from the first reader):

- LeanFinder: `ind etale profinite base cohomology detected at all fibres` returned
  eight etale algebra/morphism results, none this comparison.
- Loogle: `"strict", "cohomology"` returned the integral Hilbert 90 statement,
  which is unrelated.
- LeanSearch: `Strict localization etale abelian cohomology pullback detected on
  geometric fibers` was unavailable (Internal Server Error); no absence claim
  is based on that failed service.
- rg in Mathlib, upstream WeilConjectures, and project lean/Sheaf for
  `cohomologyPullbackOver`, `strictLocalComparisonMorphism`,
  `strictHenselizationMap`, `ind.etale.*cohomolog`, `cohomolog.*ind.etale`,
  `0EZV`, and `strict.local.*[Ff]ib` found only the existing residue-parametrized
  map theorem and distinct strict-local restriction/fibre lemmas. I opened the
  actual map and inverse-image composition definitions instead of inferring
  their behavior from names. No duplicate of either delivered interface found.

Mismatches and changes: no mathematical signature mismatch found. The worker
report incorrectly claimed an existing `statement_change` record; the base node
has none, because the every-lift correction was already landed in stage 1. I
corrected that report sentence. I also corrected the main docstring's claim that
this report contains the old nodal counterexample: it now points to the inherited
stage-1 correction instead. All mathematical signatures, definitions, node
statements and proofs remain unchanged. Each node's lean.statement was checked
verbatim against its declaration signature. No hollow data, private definition,
local notation, extra instance assumption or proved theorem was introduced.


I additionally opened the inherited stage-1 report
coord/reports/NC/lem-weil-pbc-strict-local-geometric-fibre-test.md and checked its
explicit nodal normalization example: the selected branch fibre is Spec K, while
the other clopen branch of A ×_S Spec K contributes a nonzero degree-zero section
killed by restriction to B ×_S Spec K. This explains the source discrepancy and
why the every-lift condition is necessary. The f = identity edge case also gives
two identity comparisons, as expected.
