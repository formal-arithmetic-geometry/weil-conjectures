## Worker report

The item is stated as `AlgebraicGeometry.Scheme.pbcFilteredRetractDescent` in
`Sheaf.Paper.PbcFilteredRetractDescent`. Its statement is unchanged. The statement
uses the actual PBC raw rational coefficient categories, not arbitrary categories
or a Karoubi envelope. The delivery now contains only this theorem module, with its proof postponed.
It reuses the published concrete pair category and introduces no definitions.

Hypothesis and clause correspondence:

- The prime and fixed algebraic closure are `(l : ℕ) [Fact l.Prime]`,
  `(Ω : Type c) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
  `T : Scheme.{u}`, `[IsNoetherian T]`, `hdim`, and `hl` are precisely the standing
  noetherian, finite-dimensional, invertible-prime assumptions explicitly stated
  in the pair-category dependency. They are not extra assumptions on the item.
- The finite coefficient fields are `Padic.FiniteCoefficientFields l Ω`, finite
  dimensional intermediate fields, ordered by inclusion. The scheme universe `u`
  and closure universe `c` remain independent: finite-dimensional fields are
  transported through the existing `Shrink.algEquiv`, rather than identifying
  those universes or restricting which intermediate fields occur.
- The categories C_E(T) are `pbcStageCategory l Ω T E`, an abbreviation for the
  published `PbcRationalCategory` at the canonical small coefficient field, its
  recorded integral datum and recorded uniformizer. It is raw scalar localization
  of the recorded bounded, constructible, intrinsically complete integral
  category, retaining compatible etale origins. It is not its idempotent completion.
- The hypothesis for EVERY E is `hC : ∀ E, IsIdempotentComplete
  (pbcStageCategory l Ω T E)`. The optional reference to
  `thm-weil-pbc-finite-stage-karoubian` is not used: the item assumes exactly the
  conclusion that theorem would supply. There is no extra assumption that an
  arbitrary representative already splits at its original stage.
- The pair-category completeness conclusion is
  `IsIdempotentComplete (PbcFiniteStagePairCategory l Ω T hdim hl)`.
- Every idempotent is quantified explicitly by `∀ (X : ...) (e : X ⟶ X),
  e ≫ e = e → ...`. Lean's `≫` means first the left map and then the right map.
- One finite field for the splitting is the SINGLE existential binder `P`,
  together with `h : X.stage ≤ P`, an object `B : pbcStageCategory ... P`, and
  maps `i : B ⟶ X.toStage h` and `r : X.toStage h ⟶ B`.
  Their stage equations are `i ≫ r = 𝟙 B` and
  `e = StageSystem.PairCategory.mkHom P h h (r ≫ i)`.
- The last two equations spell out that the descended maps split the given
  idempotent, not a different endomorphism. The pair object is `(ι P).obj B`;
  the maps are `(ι P).map i ≫ (isoToStage X h).inv` and
  `(isoToStage X h).hom ≫ (ι P).map r`. Their composites are its identity and e.
  Thus object, both arrows, and both equations use the same P. These are the
  source's finite-stage splitting equations, written with the framework's
  canonical object-identification isomorphism explicitly visible.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`:
  `Padic.FiniteCoefficientFields`, `finiteCoefficientCompositum`,
  `finiteCoefficientFields_properties` (the directed intermediate-field index).
- Live `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`,
  `pbcRationalization`, and the actual integral field datum/uniformizer it imports.
  The live source was read using `scompile.py --source`; the older local node
  copy had no usable record for this dependency.
- `Sheaf.Paper.BoundedConstructibleComplete` and its imported completion/tensor
  interfaces: `PbcBoundedConstructibleComplete`, `PbcIsBoundedConstructibleComplete`,
  `pbcIntegralDatum`, `pbcUniformizer`, `pbcAdicRings`, `pbcAdicCompletion`,
  `pbcAdicProjection`, `pbcLevelConstantComparison`, `pbcDerivedExtend`,
  `pbcExtend`, `pbcTensorSection`, `pbcComplexCounit`,
  `pbcDerivedScalarAdjunction`, and `pbcDerivedRestrictComp`. These are the
  canonical normalized sheaf/tensor constructions, including K-flat derived
  tensor, not arbitrary natural isomorphisms or unspecified functors.
- `WeilConjectures.CategoryTheory.StageSystem.Basic`, read from the shared
  51-module framework: `StageSystem`, `StageSystem.PairCategory`, its
  `PairCategory.mkHom`, `toStage`, `ι`, and `isoToStage`. The framework supplies
  the actual equivalence relation and common-stage category structure. The published
  specialization fixes its coefficient categories and every transition.
- `Mathlib.CategoryTheory.Idempotents.Basic`: `IsIdempotentComplete` (read its
  full signature); `Mathlib.Algebra.Algebra.Shrink` and `Field.Shrink`:
  `Shrink.algEquiv` and the transported field/algebra structures.

The full item source and the pair-category/scalar-extension blueprint sources
were read in the local blueprint archive under
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`.
The item's unit is the CBC statement, not this auxiliary retract proposition.
No source-based correction or disputed statement was necessary.

Edge cases checked: zero and identity idempotents; repeated coefficient fields
(the transition is literally identity, with normalized unit associators);
the base coefficient field; an idempotent representative whose equation holds
only after further extension (the witness P is not forced to be its first stage);
ramified extensions (maximal-ideal powers map into, not necessarily onto, target
powers, and the filtrations are cofinal); the empty scheme; independent closure
and scheme universes. Finite means vector-space finite-dimensional, not a finite
underlying set. No additional separability, flatness, algebraic-closure-universe
equality, or countable-coproduct hypothesis is imposed.

Existing-statement searches:

- `msearch.py ... leanfinder`: “A filtered colimit of idempotent complete
  categories is idempotent complete and every splitting is represented at a
  single finite stage”. Eight results concern Karoubi envelopes, the definition
  of idempotent completeness, splitting criteria, and functor/simplicial
  categories; no exact filtered common-stage descent theorem.
- `msearch.py ... loogle`: `CategoryTheory.IsIdempotentComplete`.
  Twelve definitions/criteria, none stating the present descent conclusion.
- `msearch.py ... grep` in CategoryTheory:
  `(filtered|Filtered|directed|Directed).*(IsIdempotentComplete|[Kk]aroub)|[Kk]aroub.*(filtered|Filtered)`:
  no exact match.
- `rg` of upstream `WeilConjectures`, shared `lean/Sheaf`, and the exact item id:
  no existing declaration of this statement at the original worker search. Read the generic StageSystem full
  interface; it constructs the quotient but does not state this theorem.
- Inspected current server sources and read-only delivery branches for the
  missing concrete pair/scalar-extension interfaces. The Q30 branch's arbitrary
  categories with unspecified Prop fields do not give the node's construction;
  the Q18 branch specializes to a different finite-field datum. Neither was
  substituted. The actual raw rational category is published and is imported.

## Dependency modules

`def-weil-pbc-finite-stage-pair-category` is repaired by an existing declaration
record for `AlgebraicGeometry.Scheme.PbcFiniteStagePairCategory` in
`Sheaf.Paper.FiniteStagePairCategory`. The former generic `StageSystem.PairCategory`
record does not itself fix the concrete PBC stages and transitions. The published
module supplies exactly those stages, canonical scalar functors, associators,
common-stage quotient and preadditive operations. The scheme and closure universes
remain independent. No dependency implementation is included in this delivery.
Only the dependency node's `lean` field changes, with `existing: true`, the exact
module and names, and an explanatory note.

The item's ordinary proof import `Sheaf.Paper.CommonStageCalculus` supplies the
now-recorded `AlgebraicGeometry.Scheme.commonStageCalculus`. Its signature and
proof docstring were read. The scalar-extension proof node still has no standalone
recorded module; the concrete functors and associators are already available
through `FiniteStagePairCategory`. The finite-stage Karoubian theorem is an
optional motivation for the explicit hypothesis `hC`, not an unstated prerequisite.

## New nodes

There are no new nodes or coefficient-map modules in the repaired delivery.
`def-weil-pbc-finite-completed-coefficient-map` and
`Sheaf.Paper.PbcFiniteCompletedCoefficientMap` are already published and remain
cited in the item's `stmt_deps`. Their canonical completed coefficient map is
used transitively by the reused finite-stage pair category.

## Repair of returned delivery

The maintainer's return identified 32 declarations in the former sandbox module
`Sheaf.Paper.PbcFiniteStagePairCategory` that already exist in
`Sheaf.Paper.FiniteStagePairCategory`. I inspected the existing module's complete
interfaces and replaced the item's import with that exact module. I removed the
duplicate Lean file from the sandbox and recorded the dependency as existing.
All supporting names in the returned list are reused without renaming. The item
statement and its recorded signature remain unchanged.

The repair also refreshes the proof imports to the current recorded dependency
and removes obsolete report claims about delivering the dependency construction.
The earlier second-reading text described the superseded three-module delivery;
it has been removed so the next independent reader can review this repair.

Validation: the direct `scompile.py NG prop-weil-filtered-retract-descent`
check against the reused module passed (15.9 s for the sandbox check and 12.8 s
for the library artifact), with no warnings. The final dry run also checks every
reused dependency declaration and the current ordinary proof import.

## Second reading by NG

I independently opened the node, its blueprint source place, the Lean module,
the recorded finite-stage pair-category declaration, the `StageSystem.Basic`
framework, and the common-stage calculus. The item source is the blueprint node
at order 1541; its Stacks citations (09SG, 09SH, 05QV, 05QW, 09P8, 09SF) are
nearest Karoubian and filtered-colimit references rather than a statement of
this descent. No additional standing hypothesis is supplied by those sources.

The node-to-Lean correspondence is as follows, with every verdict **holds**:

1. The prime, fixed closure, and algebra structures are rendered by
   `(l : ℕ) [Fact l.Prime]`, `(Ω : Type c) [Field Ω]`,
   `[Algebra (Padic l) Ω]`, and `[IsAlgClosure (Padic l) Ω]`; these are exactly
   the fixed coefficient data of the node.
2. The scheme and standing geometric assumptions are rendered by
   `(T : Scheme.{u}) [IsNoetherian T]`,
   `hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m`, and
   `hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)`; they are the pair-category
   assumptions and introduce no stronger finiteness, separation, or flatness
   condition.
3. The index set of finite coefficient fields is
   `Padic.FiniteCoefficientFields l Ω`, the actual finite intermediate fields
   in the fixed algebraic closure. Its base and compositum, read in
   `FiniteCoefficientFields.lean`, cover nonemptiness and directedness.
4. The finite stage category `C_E(T)` is rendered by
   `pbcStageCategory l Ω T E`, the abbreviation for the published raw
   `PbcRationalCategory` at the canonical datum and uniformizer. It is not a
   Karoubi envelope and its object set is retained.
5. The hypothesis that every finite stage is idempotent complete is rendered
   exactly by `hC : ∀ E, IsIdempotentComplete (pbcStageCategory l Ω T E)`.
   The cited finite-stage Karoubian theorem is only the node's “for instance”
   motivation and is not silently assumed.
6. The pair category in the conclusion is exactly
   `PbcFiniteStagePairCategory l Ω T hdim hl`, the concrete specialization of
   `StageSystem.PairCategory`; the first conjunct is
   `IsIdempotentComplete` of that category.
7. The splitting clause quantifies an arbitrary `X`, an endomorphism `e`, and
   the idempotent equation `e ≫ e = e` in that order. The existential has one
   field `P`, one inclusion proof `h : X.stage ≤ P`, one stage object `B`, and
   `i : B ⟶ X.toStage h`, `r : X.toStage h ⟶ B`, all over that same `P`.
8. The finite-stage equations are rendered as `i ≫ r = 𝟙 B` and
   `e = PairCategory.mkHom P h h (r ≫ i)`. Since Lean composition reads left
   arrow first, these are respectively the source's `p i = 1` and `i p = e`.
9. The first expanded pair-category equation uses
   `(ι P).map i ≫ (isoToStage X h).inv ≫ (isoToStage X h).hom ≫ (ι P).map r`;
   `isoToStage X h : X ≅ (ι P).obj (X.toStage h)`, so this is an endomorphism of
   `(ι P).obj B` and is the identity. The second uses the reverse canonical
   identification and is exactly `e`. These clauses make “represented over one
   field” explicit without changing its content.

The edge cases remain covered: the base field witnesses a nonempty index,
composita handle repeated or incomparable stages, identity and zero
idempotents satisfy the same equations, an equality may first become true only
after a larger `P`, and `u` and `c` stay independent. Empty schemes and no
underlying-set finiteness are allowed. No characteristic, separability,
countability, or extra universe equality was added.

For the one-definition-per-notion check I ran `msearch.py` with LeanFinder,
Loogle, and grep queries for filtered/direct limits and idempotent completeness,
and searched both the upstream `WeilConjectures` tree and shared `lean/Sheaf`.
LeanFinder returned only generic `IsIdempotentComplete`, Karoubi, and functor
category results; Loogle returned the definition and fixed-category splitting
criteria; grep found no filtered-colimit descent theorem. The exact item name
also has no existing declaration. The dependency search confirmed that
`AlgebraicGeometry.Scheme.PbcFiniteStagePairCategory` already exists in
`Sheaf.Paper.FiniteStagePairCategory`; the old private duplicate was removed
and the dependency node records that existing declaration. No new definition
node or dependency module is needed.

I found no mismatch in the statement, hypotheses, quantifier order, object
notions, universes, edge cases, or dependency interfaces, so no Lean or node
repair was required in this second reading. The existing module compiles with
the required `scompile.py` wrapper and only the expected postponed theorem
proof remains.
