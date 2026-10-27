## Worker report

The module `Sheaf.AlgebraicGeometry.DMEtaleAtlasCalculus` states all clauses of
`lem-sfb-dm-etale-atlas-calculus` in four named theorems, all with `sorry` proofs.
There are no new definitions, dependency repairs, statement corrections, or disputed claims.

Clause and hypothesis correspondence:

- The base scheme is `{S : Scheme.{u}}`. Stacks over S are the existing
  `BasedCategory.{vᵢ, wᵢ} (Over S)` objects, with separate, explicit object and morphism
  universes for each stack. No equality of those universes is imposed.
- The three DM hypotheses are `hX`, `hY`, `hZ : IsDeligneMumfordModuliStack ...`.
  The two arbitrary morphisms in the fibre-product assertion are `f : BasedFunctor X Z`
  and `g : BasedFunctor Y Z`. No representability, smoothness, étaleness, or
  surjectivity hypothesis is imposed on those two maps.
- `dm_twoFiberProduct` concludes
  `IsDeligneMumfordModuliStack (moduliTwoFiberProduct f g)` for the actual recorded
  2-fibre product. Its conclusion includes stack descent, algebraic-space diagonal,
  and existence of a surjective étale scheme atlas, exactly as the existing definition
  spells out. Atlas existence is not replaced by a scheme representative of the product.
- Representable-by-algebraic-spaces étaleness is the existing `IsEtaleModuliMap`:
  for every scheme base change it requires `HasSpaceBaseChange` with
  `SpaceMapIsEtale`. The latter uses the recorded scheme `Etale` on all étale scheme
  charts of the resulting algebraic space. Representability is included in this
  predicate, rather than supplied by an unrelated premise.
- `dm_etale_baseChange` assumes `hf : IsEtaleModuliMap f`, lets `g` be arbitrary,
  and concludes that `moduliTwoFiberFst g f` is representable étale. The reversal
  of the two inputs is intentional: this first projection maps `Y ×_Z X` to Y.
- In its second conjunct, `dm_etale_baseChange` assumes precisely that every scheme
  base change of f has an actual space presentation with `SpaceMapIsSurjective`.
  It concludes the identical condition for the base-changed map. `SpaceMapIsSurjective`
  asks for a point in an étale scheme chart above each point of the test scheme.
  The existential presentation is tied to this map by `HasSpaceBaseChange`.
- `dm_etale_comp` assumes both `hf` and `hg`, and concludes representable étaleness
  of the actual `f.comp g`. Its second conjunct requires the same scheme-test
  surjectivity for both maps and gives it for their composite. Surjectivity is not
  required for the first conjunct. Both permanence theorems range over arbitrary
  DM stacks and maps, so apply in particular to the DM products of the first theorem.
- In `dm_relative_etale_chart`, the stacks X and Y have precisely their DM hypotheses;
  the bottom map f is arbitrary. The schemes U,V over S, maps a,b, and `p : U ⟶ V`
  render the full square. The based-functor isomorphism
  `e : a.comp f ≅ (discreteModuliMap (yoneda.map p)).comp b` is its specified
  2-commutativity, including compatibility over the base. The chart hypotheses are
  only `ha : IsEtaleModuliMap a` and `hb : IsEtaleModuliMap b`.
  The conclusion is representable étaleness of the existing canonical comparison
  `moduliTwoFiberLift a (discreteModuliMap (yoneda.map p)) e` into `X ×_Y V`.
  Neither chart is assumed surjective and f is not assumed étale.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the recorded
  `Limits.pullback`, `pullback.fst`, and `pullback.snd`, used in the proof route's
  scheme-product construction and imported as the statement dependency requires.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsDeligneMumfordModuliStack`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`,
  `discreteModuli`, `discreteModuliMap`, `HasSpaceBaseChange`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`, with their actual full definitions read before writing.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and its existing representable scheme-chart conventions.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`:
  `IsEtaleModuliMap` and `moduliTwoFiberLift`. Its owning, already landed node
  `def-sfb-moduli-chart-normalization` is added to `stmt_deps` under the rule
  allowing statement dependencies to gain landed nodes. No notion is duplicated.
- Plain proof imports are the recorded modules of every stated proof dependency:
  `DMIsomSpaceUnramified`, `AlgebraicSpaceFibreProductsEtaleCovers`,
  `ChartwiseEtalePermanence`, `EtaleSmoothZeroDimensionalFibres`,
  `EtaleSmoothAtlasFppfDescent`, `StackChartwiseSmoothEtaleCalculus`, and
  `EnlargedEtaleRingedSite` (owner of `AlgebraicSpace.schemeSpace`). The two
  definition dependencies also occurring among proof dependencies are public imports.

Source and edge-case checks:

Read the local Stacks source at algebraic.tex `lemma-2-fibre-product-general`
and `lemma-2-fibre-product` (04TF/04T2), and spaces-morphisms.tex
`lemma-etale-permanence` (05W3). The first constructs the atlas through an
algebraic space, not necessarily a scheme; the second proves cancellation for any
map between spaces étale over a common base. These match the node's detailed
five-step proof, which is reproduced in the relevant declaration docstrings.
The supporting recorded stack-calculus source was read as well, including its
surjectivity comparison and scheme-test conventions.

The empty scheme, empty source stack, empty charts, and identity maps are included:
no nonemptiness, quasi-compactness, separatedness, finite-type, or characteristic
premise is introduced. Surjectivity over an empty scheme is vacuous as required;
an empty chart of a nonempty stack is allowed in the final clause. Choosing both
charts to be identities recovers the identity comparison over a scheme. Arbitrary
base changes and maps f in the last clause are allowed. Automorphisms and the
specified comparison isomorphism are retained by the existing iso-comma construction.

Searches for existing statements and notions:

- `msearch.py ... leanfinder "Deligne Mumford stacks fibre products etale atlases
  etale relative chart map"`: 8 hits, concerning scheme étaleness, scheme étale
  categories, and scheme base-change/composition instances; no stack statement.
- `msearch.py ... leansearch "Deligne Mumford stacks fibre products etale atlases"`:
  8 hits, concerning schemes and their étale topologies; no matching stack theorem.
- `msearch.py ... loogle '"Etale", "comp"'`: 12 hits, ring and scheme étale
  composition/cancellation; no matching stack theorem.
- `msearch.py ... grep 'DeligneMumford|IsEtaleModuli|moduliTwoFiber' CategoryTheory`:
  0 Mathlib hits.
- `rg` in `lean/WeilConjectures` for the node id, DM stacks, étale atlases,
  `DeligneMumford`, and `moduliTwoFiberProduct`: no relevant upstream statement.
- `rg` in `lean/Sheaf` found the existing predicates in StablePointedModuliGroupoids
  and ModuliChartNormalization, their uses in later modules, and the general
  algebraic-stack calculus. Reused these definitions. The general calculus does
  not assert DM closure or the final relative-chart theorem.
- `rg` for the four proposed full declaration suffixes in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no clashes.

Validation: `scompile.py NQ lem-sfb-dm-etale-atlas-calculus <module>` compiled both
its sandbox and library module names cleanly (3.5 seconds each), with no errors or
unexpected warnings. Every variable and universe is explicitly bound; module mode
and public/private import visibility follow the stage rules.

## Second reading by NQ

The dispatcher forbids starting another agent; this section records a separate
self-review of the node against the completed file, not an independent worker review.
The maintainer's independent review remains the delivery review required by the brief.

Re-read all statement clauses after the successful compile. The first result uses
all three DM hypotheses and no property of f,g; expanding the DM conclusion supplies
its atlas clause. The base-change projection has the correct orientation (first
projection for inputs g,f); its surjectivity implication has the same actual-map
scheme tests on both sides. The composition result binds f:X→Y and g:Y→Z and tests
their surjectivity over Y and Z respectively. The chart result uses both actual
scheme charts and the specified based 2-isomorphism, and has no surjectivity premise.
All three stack universe pairs remain independent. No clause or hypothesis mismatch
was found; no statement change was needed. The extra dependency is the existing
owner of the two definitions used, rather than a new copy of either notion.
