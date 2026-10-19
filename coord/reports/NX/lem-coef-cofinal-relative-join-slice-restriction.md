## Worker report

Module: `Sheaf.CategoryTheory.CofinalRelativeJoinSliceRestriction`.
Main declaration: `SSet.Enhanced.cofinal_relative_join_slice_restriction`.
The only postponed proof is that named theorem, whose docstring carries all seven
steps of the DAG proof. Definitions have actual simplicial-map data; their proof
fields establish only structural well-definedness and naturality.

Hypotheses and clauses, in the order of the node:

- Small quasicategories and coherent functors: `A B C D : SSet.{u}` with the four
  `Quasicategory` instances; `j : A ⟶ B`, `p : C ⟶ D`, `f : B ⟶ C` are actual
  simplicial maps. The single arbitrary universe is the common small universe;
  there is no extra universe equality, cardinality or nonemptiness hypothesis.
- A full subcategory inclusion: `[Mono j]` gives degreewise injectivity, and `_hj`
  identifies `Subfunctor.range j` with `fullSubcomplex B (Set.range (j.app (op ⦋0⦌)))`.
  Thus its simplices are precisely all simplices with vertices in the selected set.
  This allows a relabelled full inclusion, not only a literal subtype presentation.
- The outgoing comma condition is
  `∀ b, IsContractible (comma A B j b false)`. The dependency's `false` orientation
  has source the constant vertex `b` and target `j(a)`. Both endpoint equations hold
  on entire simplices, so these are coherent arrow commas.
- The inner-fibration hypothesis is `_hp : InnerFibration p`, using Mathlib's
  inner-horn lifting class, reexported by the recorded fibration dependency.
- The specified coslices are the dependency's `coherentJoinCoslice`: in degree `n`
  their only data is a map `B ⋆ Δⁿ → C` restricting exactly to `f`. Their operators
  precompose on the simplex block. `relativeCosliceRestrictionMap p j f` is the
  existing `pullback.lift` of restriction and postcomposition, with target exactly
  `C_{fj/} ×[D_{pfj/}] D_{pf/}`. No arbitrary comparison map is quantified.
- The first conclusion is `modelCategoryQuillen.I.rlp` of that map. `I` consists
  of all boundary inclusions, for every natural-number dimension. `rlp` gives a
  filler with both triangle equalities, hence exact preservation of the prescribed
  boundary and base simplex. Dimension zero is included, so vertex surjectivity
  is part of the conclusion rather than an omitted auxiliary requirement.
- The left-adjoint special case is the second conjunct: existence of
  `R : B ⟶ A` with `MappingBifunctorsEquivalent R j` implies the outgoing comma
  condition. This existing definition is an equivalence over `B × A` of the whole
  correspondences for `Map_A(R(-),-)` and `Map_B(-,j(-))`. It retains coherent
  naturality in both variables, as required by the node, and does not assume a
  separately chosen unit or counit beyond the stated mapping-space equivalence.
- The dual comma condition is `∀ b, IsContractible (comma A B j b true)`:
  the dependency's `true` orientation consists of arrows `j(a) → b`.
- The dual restriction is `relativeSliceRestrictionMap p j f`. Its domain is the
  recorded `joinSlice f`, whose simplices are the maps `Δⁿ ⋆ B → C` extending `f`.
  `coherentSliceRestriction` precomposes with `id ⋆ j`, preserving the initial
  simplex; the existing canonical `relativeLimitSlicePostcomp` postcomposes both
  the extension and initial simplex with `p`. Their actual commuting square defines
  the canonical map into `relativeSliceRestrictionPullback`. That target is exactly
  `C_{/fj} ×[D_{/pfj}] D_{/pf}`. The third conjunct asserts `I.rlp` for this map.
- One initial object per component is the antecedent of the fourth conjunct.
  `∀ b, ∃! a, π₀.mk (j.app _ a) = π₀.mk b` selects exactly one vertex of `A` in
  every component of `B`. For each selected `a`, the second part requires
  `IsContractible (mappingSpace B (j.app _ a) b)` for every `b` in its component.
  This is exactly initiality in that component, without requiring maps to other
  components. Mathlib's `π₀` is the edge-zigzag quotient, which gives the components
  of realization. Fullness supplies all the higher simplices on these vertices.
  The conclusion is the dual comma hypothesis, so the third conjunct applies.
- `IsContractible` is the recorded weak homotopy equivalence to the point, including
  the bijection on components. No limit or colimit existence assumption occurs.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex`,
  `comma`, `IsContractible`, `mappingSpace`; their definitions and docstrings were
  read, including the two comma endpoint orientations.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: `joinSlice`, `JoinSliceSimplex`,
  `joinStandardFunctor`, `orderedJoinInl`, `orderedJoinInr`, and their constructors.
  `joinSlice_right_fibration` explicitly states uniqueness of the stored initial
  restriction for each join map, so no extra mathematical data is imposed.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` reexports
  `Sheaf.CategoryTheory.InfinityFibrations` and Mathlib's `SSet.InnerFibration`.
- `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`:
  `SSet.modelCategoryQuillen.I`, with `CategoryTheory.MorphismProperty.rlp`;
  `SSet.boundary` and `boundary_zero` were checked in their source. This is the
  exact `mathlib_match` of `def-weil-pbc-trivial-kan-fibration`; no redundant
  specialized definition was created.
- Added already-landed statement dependency `lem-cbc-relative-coslice-left-fibration`:
  `Sheaf.CategoryTheory.RelativeCosliceLeftFibration`, specifically
  `coherentJoinCoslice`, `cosliceInclusionsNatural`, `relativeCosliceRestrictionMap`.
- Added already-landed statement dependency `lem-coef-infinity-pointwise-adjoint-criterion`:
  `Sheaf.CategoryTheory.InfinityPointwiseAdjointCriterion`, specifically
  `MappingBifunctorsEquivalent`. This was already a proof dependency.
- Mathlib `SSet.π₀.mk`, `Subfunctor.range` and their definitions give the component
  and full-image conditions directly.
- Stated proof dependencies are imported non-publicly: `EnhancedFunctorConeCalculus`,
  `AnodyneCocones`, `RealizationCylinder`. Their recorded main signatures were read.
  `lem-coef-infinity-cofinal-mono-right-anodyne` has no recorded declaration yet:
  it is used only by the future proof, so there is currently no module to import.
  The new statement dependencies were checked for a path back to this item; neither
  creates a DAG cycle.

Edge cases checked mathematically:

- `B = ∅` forces `A = ∅` under `[Mono j]`; the comma conditions and component
  selection condition are vacuous and both restrictions are identities.
- `A = ∅`, `B` nonempty: every comma is empty, and `IsContractible` fails on the
  component condition. The initial-component selection also fails. Thus an empty
  selected category never supplies a false cofinality hypothesis.
- `j = id`: both relative restriction maps are canonical isomorphisms and lift
  every boundary. No diagram-extension assumption appears.
- `{1} ⊂ Δ¹`: the outgoing commas are contractible and the forward coslice
  restriction has the expected orientation. `{0} ⊂ Δ¹` instead satisfies the
  incoming condition and initial-component special case. The reverse comma in
  each example is empty at the other endpoint.
- Several components: uniqueness is tested separately by `π₀.mk`; no global
  initial object or maps between different components are assumed. Nontrivial
  higher simplices in the full subcategory are retained.
- Dimension zero is present in `I`; dimensions one and above prescribe every
  boundary face and the entire base extension. Empty target or source is allowed
  whenever the bound maps exist. No existence of cones, limits or colimits is assumed.

Searches for existing declarations:

- `msearch.py leanfinder`: "Restriction of relative join coslices along a cofinal
  full inclusion is a trivial Kan fibration". Eight hits: Quillen fibration
  primitives, horn fillers and general categorical constructions; no matching theorem.
- `msearch.py loogle`: `SSet, CategoryTheory.HasLiftingProperty`. Four hits on
  Quillen all-horn lifting and quasicategory inner-horn lifting; none is this theorem.
- `msearch.py leansearch`: "Cofinal inclusion of quasicategories induces a trivial
  Kan fibration on relative join slices". Eight hits, including ordinary-category
  join finality and general model-category lifting; none matches the assertion.
- `msearch.py grep`: `relativeCoslice|coherentJoinCoslice|joinSlice|cofinal.*[Rr]estriction`
  in `AlgebraicTopology`: zero hits.
- `rg` in `WeilConjectures` and `lean/Sheaf` for join slices, relative restrictions,
  full inclusions, initial components and the proposed declaration names; also the
  literal item id in upstream. Upstream has no matching declaration; the side
  project has the reusable coslice interface and joinSlice, but no cofinal trivial
  Kan assertion or general dual restriction maps. `dag/lean_names_upstream.json`
  has no matching cofinal-relative-join declaration.

Sources inspected: HTT Proposition the project server, printed pp. 62--63, explicitly gives
trivial Kan lifting under right-anodyne restriction and an inner-fibration target
(https://people.math.harvard.edu/~lurie/papers/HTT.pdf); Kerodon 02NZ gives both
arrow-comma criteria (https://kerodon.net/tag/02NZ), and 01BZ spells out the two
canonical relative restriction maps (https://kerodon.net/tag/01BZ). The HA source
is the September 18, 2017 edition cited in the node. No statement correction or
statement dispute is needed.

Validation: `scompile.py NX lem-coef-cofinal-relative-join-slice-restriction` compiled
this file both as the isolated sandbox module and under its final library module
name, cleanly (9.9 s and 10.3 s). All universes and variables are explicitly bound;
all lines are at most 100 characters. Independent second reading is pending.

## Second reading by NX

I read `dag/nodes/sec-six-functors/lem-coef-cofinal-relative-join-slice-restriction.json`,
its four statement dependencies, the source declarations, and the cited source places before
checking the Lean signature. The node's objects, hypotheses, and conclusion clauses match as
follows.

1. The node's small quasicategories and maps are rendered by
   `{A B C D : SSet.{u}}`, the four `[Quasicategory ...]` instances, and maps
   `j : A ⟶ B`, `p : C ⟶ D`, and `f : B ⟶ C`. Verdict: exact common-universe
   presentation; no extra universe, size, or nonemptiness assumption.
2. The full inclusion is rendered by `[Mono j]` together with
   `_hj : Subfunctor.range j = fullSubcomplex B (Set.range (j.app (op ⦋0⦌)))`.
   Reading `Subfunctor.range` and `fullSubcomplex` confirms that this says precisely
   degreewise injectivity and all-and-only simplices whose vertices lie in the image.
   Verdict: exact encoding of the node's full subcategory inclusion.
3. The outgoing comma hypothesis is the first antecedent,
   `∀ b : B _⦋0⦌, IsContractible (comma A B j b false)`. The dependency's comma
   definition has endpoint zero constant at `b` and endpoint one `j(a)` for `false`.
   Verdict: exact `b → j(a)` orientation, with all higher compatibility data.
4. The inner-fibration hypothesis is `_hp : InnerFibration p`, using Mathlib's
   inner-horn lifting class as required by `def-coef-infinity-fibrations`. Verdict: exact.
5. The first conclusion is
   `modelCategoryQuillen.I.rlp (relativeCosliceRestrictionMap p j f)`. The imported
   relative coslice module defines the canonical restriction/postcomposition pullback
   with target `C_{fj/} ×[D_{pfj/}] D_{pf}`. Mathlib's `I` is exactly the family of
   all boundary inclusions, including `boundary 0`. Verdict: exact trivial-Kan boundary
   lifting, including dimension zero and exact base and boundary preservation.
6. The left-adjoint special case is the second conjunct,
   `(∃ R : B ⟶ A, MappingBifunctorsEquivalent R j) → ...`. The dependency's
   `MappingBifunctorsEquivalent R j` is an equivalence over `B × A` between the complete
   mapping correspondences for `(1_B,R)` and `(j,1_A)`, so it states the node's coherent
   mapping-space adjunction without extra unit/counit hypotheses. Verdict: exact.
7. The dual comma hypothesis is the third antecedent,
   `∀ b, IsContractible (comma A B j b true)`. Reading `commaSubcomplex` confirms
   `true` has endpoint zero `j(a)` and endpoint one constant `b`, hence arrows
   `j(a) → b`. Verdict: exact dual orientation.
8. The dual map is `relativeSliceRestrictionMap p j f`, whose domain is the recorded
   `joinSlice f` of maps `Δⁿ ⋆ B → C`. Its restriction map and canonical pullback
   target are explicit, and the postcomposition component now uses the existing
   `relativeLimitSlicePostcomp` declaration. Verdict: exact `C_{/f} →
   C_{/fj} ×[D_{/pfj}] D_{/pf}` map and no arbitrary comparison map.
9. The fourth antecedent is the conjunction of
   `∀ b, ∃! a, π₀.mk (j.app _ a) = π₀.mk b` and
   `∀ a b, π₀.mk (j.app _ a) = π₀.mk b →
   IsContractible (mappingSpace B (j.app _ a) b)`. Verdict: exactly one selected
   vertex in each component and contractible outgoing mapping spaces within that
   component; no maps between components are imposed. The conclusion is precisely the
   dual comma hypothesis, as the node states.
10. No additional conclusion clause is present: the conjunction order and all
    quantifiers agree verbatim with the node. No limit, colimit, characteristic, or
    finiteness hypothesis occurs.

I checked edge cases: empty `B` forces empty `A` under `Mono j` and makes the quantified
comma/component clauses vacuous; nonempty `B` with empty `A` cannot satisfy the comma
hypotheses; `j = 𝟙` gives canonical isomorphism restrictions; `{1} ↪ Δ¹` tests the outgoing
orientation while `{0} ↪ Δ¹` tests the incoming orientation; multiple components are handled
by the `π₀` equality separately; and `modelCategoryQuillen.I` includes dimension zero.
The common universe does not exclude any of these cases.

I repeated the three required duplicate searches. LeanFinder/Loogle/LeanSearch and grep in
Mathlib, `WeilConjectures`, and `lean/Sheaf` found no theorem matching the cofinal relative
restriction assertion. I did find one exact existing helper that the worker's broad search
missed: `SSet.Enhanced.relativeLimitSlicePostcomp` in
`Sheaf.CategoryTheory.RelativeLimitJoinBoundary`, with the same type and canonical
postcomposition data as the worker's `coherentSlicePostcompose`. This was an H4 mismatch.
I deleted the duplicate definition, imported `RelativeLimitJoinBoundary`, and replaced both
uses by `relativeLimitSlicePostcomp`; the node's `lean.declarations` list now contains only
the declarations actually defined in this module. No new definition node or dependency module
is needed, and no statement correction is needed.

The module and node retain the required source/blueprint docstrings and the theorem proof
steps. The repaired module compiles cleanly through `scompile.py`; no variables or universes
are unbound and no line exceeds 100 characters.
