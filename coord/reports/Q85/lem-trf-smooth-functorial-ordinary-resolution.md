## Worker report

The theorem `AlgebraicGeometry.exists_smooth_functorial_ordinary_resolution` in
`Sheaf.AlgebraicGeometry.SmoothFunctorialOrdinaryResolution` states
`Nonempty (SmoothFunctorialOrdinaryResolution.{u})`, with proof `sorry`.
The new definition module `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule` supplies the
actual data types for the single simultaneous rule. There are no postponed definitions,
choices of arbitrary maps, auxiliary sorry lemmas, or statement corrections.

Clause-by-clause correspondence:

- All reduced finite-type Q-schemes: `RationalResolutionInput` has `scheme : Scheme.{u}`,
  `structureMap : scheme ⟶ Spec (.of (ULift.{u} ℚ))`, `IsReduced scheme`,
  `LocallyOfFiniteType structureMap`, and `QuasiCompact structureMap`. The lift only places
  Q in the scheme universe. No separation, fixed dimension, connectedness, nonemptiness,
  or equidimensionality condition is imposed. Every morphism over Q is admitted through
  the commuting structure-map equation. A Q-scheme has a unique rational structure map,
  so this equation does not restrict the smooth maps of the statement.
- One rule on every input, including finite disjoint unions: the single structure field
  `tower : ∀ S : RationalResolutionInput.{u}, OrdinaryBlowupTower S.scheme` is inside the
  existential `Nonempty`, rather than existentially choosing a tower separately for each
  input. A finite disjoint union is an input to the same function; comparisons with its
  smooth inclusions retain its synchronization. No componentwise independent algorithms
  are substituted.
- A finite tower: `length : ℕ`, levels `Fin (length + 1)`, the initial isomorphism to the
  input scheme, and all `transition` maps. `transition_id` and `transition_comp` specify
  precisely the composites of the adjacent maps; they impose no additional geometric
  hypothesis. The initial isomorphism encodes S_0=S without demanding equality of chosen
  presentations of schemes.
- Ordinary blowups and their ideals: `center i : (level i.castSucc).IdealSheafData`,
  `blowupIso i : level i.succ ≅ (center i).blowup`, and `blowup_fac` identify the transition
  with the ordinary structure map `(center i).blowupMap`. No normalization is present.
- Each center is coherent (locally finitely generated): `(A.center i).ofFiniteType` in
  `OrdinaryBlowupTower.IsRegularResolution`. It uses the existing upstream predicate for
  finite generation on every affine open. All levels are finite type over Q (finite type
  of the input and finite-type ordinary blowups), hence locally Noetherian; on these
  levels quasi-coherent locally finitely generated ideals are coherent.
- Nonempty center: `Set.Nonempty ((A.center i).support : Set (A.level i.castSucc))`.
- Nowhere dense center: `IsNowhereDense` on that same support, which is V(I), not the
  nonvanishing locus of the ideal regarded as a module.
- Regular center: `IsRegularScheme (A.center i).subscheme`, including its scheme structure.
- Regular final scheme: `IsRegularScheme (A.level ⟨A.length, Nat.lt_succ_self A.length⟩)`.
  `resolves : ∀ S, (tower S).IsRegularResolution` enforces all five conditions on every input.
- Every smooth h:T→S: the `comparison` field quantifies all inputs and all h with `[Smooth h]`,
  and the over-Q equation. There is no requirement on constant relative dimension or
  surjectivity in this field.
- Canonical pullback of the whole tower: `OrdinaryResolutionComparison.levelMap` and
  `cartesian` identify `B.level (count i)` with the fiber product `T ×_S A.level i` for
  every original level i, including repeated levels at deleted stages. `naturality` fixes
  the transition maps. Thus this is the actual cartesian pullback, not an arbitrary tower
  admitting maps to the target. Blowup rigidity over reduced schemes and the nowhere
  dense centers make these compatible maps canonical, as in ILO 2.1.1 and 2.3.4.
- Deletion of exactly unit-ideal stages: `deleted_iff_unit` is an iff; a deleted stage has
  `count i.succ = count i.castSucc` by `deleted_level`, so its transition is the identity.
  For retained stages `count_before` and `count_after` increment the level count exactly
  once. `count_zero` and `count_last` cover the endpoints, so no other levels are inserted
  or omitted.
- Original order: `retainedStage : Fin B.length ↪o Fin A.length` is an order embedding;
  it lists every source center in the original order. `count` is an order homomorphism.
- Extended ideals: `retained_ideal` equates the actual `IdealSheafData.comap` of the
  target center with the source center after its index equality transport. This keeps
  the ideals themselves, not only their closed sets or their blowup schemes.
- Identities: `identity_count` and `identity_map` specify the actual counts and maps,
  including the necessary equality transport of levels.
- Composition: `composition_count` identifies the composite contraction with the
  composite counts, while `composition_map` identifies the composite level maps with the
  direct comparison, after index transport. The count and ideal equations also force the
  retained ordered subsequence to be precisely the twice-retained subsequence; a unit
  ideal stays unit after extension.
- Surjective h deletes no stages: `surjective_no_deletion` under `[Smooth h] [Surjective h]`
  states `Function.Surjective comparison.retainedStage`. Since this map is an order
  embedding, its range is then every original stage.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`: the node's
  sections-wise reduced condition, equivalent to the local-ring condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`:
  together finite type, as required by the dependency's recorded interface.
- `WeilConjectures.Blowup.Gluing`, `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and
  `.blowupMap`: the glued ordinary blowup and its structural map.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`:
  `IsLocallyNoetherian X ∧ IsRegular X`, exactly the recorded regular-scheme interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`:
  smoothness without a fixed relative dimension.
- `WeilConjectures.Compactification.FiniteTypeExtension`,
  `AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType`: finite generation on all affine
  opens. The module source and `ofFiniteType_iff` were read.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`, `IdealSheafData.comap`, and the basic
  and subscheme modules: the actual extended ideal, its closed support, and its closed
  subscheme. `comap` is the kernel of the pullback closed immersion, so it is extension of
  an ideal; it is not ring-theoretic contraction of an ideal.
- `CategoryTheory.IsPullback` specifies cartesian comparison squares. `Fin`, order maps,
  and order embeddings encode finite stages and the ordered retained subsequence.

Published proof-dependency imports are retained for stage 3:
`WeilConjectures.Compactification.StrictTransformBlowup`,
`WeilConjectures.RingTheory.StandardSmoothQuotientLift`,
`Mathlib.RingTheory.Smooth.StandardSmoothCotangent`,
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`,
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`WeilConjectures.Blowup.FlatBaseChange`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`.
The last green/live source of `WeilConjectures.Blowup.FlatBaseChange` was read through
`scompile.py --source`; its `.blowupFlatBaseChange` and `.blowupFlatBaseChangeIso` are
available even though this older local source checkout has no such file.
The embedded-resolution dependency has no recorded declaration yet, so there is no
module for that proof-only dependency to import. Nothing in the statement needs its data.

Source checked: ILO VIII 2.1.4–2.1.9 and 2.3.1–2.3.5, printed pp.87–88,91–92,
and Theorem 2.3.10 with Remark 2.3.11, p.93. The PDF was read with `pdftotext -layout`.
The theorem gives ordinary resolution on all reduced quasi-excellent Q-schemes, functorial
for regular maps, with regular centers. The item is exactly its finite-type-Q/smooth
restriction, with the explicit tower conventions in those paragraphs.

Edge cases checked mathematically before finalizing:

- Length zero: `Fin 0` has no centers, `Fin 1` has the single initial/final level, and
  the only remaining geometric condition is regularity of the input.
- Empty scheme: a nonzero length would demand a nonempty center on an empty scheme,
  so the tower has length zero. An empty source can delete every target stage; a
  surjective morphism with empty source has empty target as well.
- Regular inputs: the trivial tower is allowed. No artificial requirement of positive
  length or a nonempty singular locus occurs.
- Smooth open restriction avoiding a center: its extended ideal is top and exactly that
  stage is deleted. An invertible but nonunit ideal is retained, even though its blowup
  morphism is an isomorphism; the deletion criterion is the ideal, not `IsIso`.
- Several consecutive deletions and all stages deleted: equal neighboring counts and
  cartesian repeated levels encode these cases. The two endpoint axioms cover n=0 too.
- Mixed-dimensional finite unions and non-separated inputs: the input imposes neither
  a relative dimension nor separatedness. Resolving the whole union gives shared labels.
- Surjective smooth maps meet every nonempty center at each cartesian level, hence have
  a surjective retained-stage embedding. Identity comparisons transport to literal
  identity maps; direct and iterated comparisons agree in their domains and codomains.
- The universe `u` is explicit everywhere; `ULift.{u} ℚ` fixes only size. There are no
  auto-bound implicit variables, local notations, local instances, or hidden let binders.

Searches for an existing statement or definition (all broker queries are recorded in
`searches.jsonl`):

- LeanFinder: `Resolution of singularities by finite blowup towers functorial for smooth
  morphisms`; eight smoothness results, no resolution rule or tower.
- LeanFinder: `Finite ordinary blowup towers and canonical resolution functorial for smooth
  maps deleting unit ideal stages`; eight smoothness/standard-smooth results, no tower.
- LeanSearch: `finite ordered towers of blowups and contraction of unit ideal stages under
  smooth pullback`; six ideal-contraction results and two smoothness results, no tower.
- Loogle: `"blowup"`; no hits. Loogle `"IsPullback"` returns the general cartesian-square
  interface used in the definition, not a blowup-resolution notion.
- Broker Mathlib grep: `BlowupTower|desingulari[sz]|FunctorialResolution`; no hits.
- Direct `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for
  `OrdinaryBlowupTower|SmoothFunctorialOrdinaryResolution|RationalResolutionInput|
  OrdinaryResolutionComparison`: no existing declaration. Direct upstream search for
  the item's id: no result. Ordinary blowup and log-blowup APIs were inspected separately.
- DAG statements searched for `resolution rule`, `blowup tower`, `blow up tower`,
  `blow-up tower`, and `ordinary resolution`. The relevant nodes describe embedded
  resolution, normalized toric towers, log towers, and this existence theorem; none is a
  definition of this ordinary rule or contracted comparison. `tools/blueprint_refs.py
  search 'resolution rule'` returns zero blueprint nodes. The ancestor command names
  `lem-trf-local-term-locality`.

Validation: both delivered files compiled separately with `scompile.py`, in dependency
order. The definition has no sorry; the only postponed proof is the assigned theorem,
whose docstring reproduces all seven proof steps and their named dependencies.
No mathematical statement is disputed and no node correction was needed.

## New nodes

`def-trf-ordinary-resolution-rule` defines the finite ordinary blowup tower, regular-resolution
condition, exact contracted cartesian comparison preserving extended ideals, and the single
smooth-functorial rule with identity, composition and surjectivity laws. Its source is ILO
VIII 2.1.4–2.1.9, 2.3.1, 2.3.4–2.3.5(i), printed pp.87–88,91–92. The four broker searches
and the direct DAG/upstream/project searches listed above found no existing definition.
All scheme, ideal, regularity, smoothness and ordinary blowup notions are reused. Each
structure has real fields; `toBase` and `IsRegularResolution` have explicit bodies. The new
node has the same five definition dependencies as the item and is cited by the item.
Its six declarations are listed in `lean.declarations` and have source/blueprint docstrings.

## Second reading by Q85

Author's second reading, not an independent review: I reopened the node, ILO source, and
both modules, and checked the correspondence above against the actual field types.
`Nonempty` encloses the complete global rule, so the statement does not exchange its
quantifiers. Coherence uses locally finite generation of a quasi-coherent ideal on the
Noetherian levels, regularity is the recorded locally-Noetherian scheme notion, and the
support is V(I). The count endpoints and before/after/deleted equations prevent arbitrary
subsequences. `retained_ideal` transports the source ideal along the equality from its
counted level to its own level; the direction is correct. The iff on top ideals is stronger
than merely requiring an isomorphism at deleted stages, and matches the stated rule.
Cartesian squares and naturality compare every level, not just the last one. The
composition transport runs from the direct composite count to the iterated count before
composing the two comparison maps; identity transport runs from the original index to
the identity-comparison index. Their directions and domains were rechecked. The final
surjectivity axiom ranges over all original stages. No missing hypothesis or clause was
found. I moved the theorem from the draft `TraceFormula` directory to the topic directory
`AlgebraicGeometry` and added the published flat-base-change and smooth-flat proof imports.
The maintainer's independent review remains the independent mathematical check.
