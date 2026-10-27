## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCoherentLimitPreserving` states
`AlgebraicGeometry.AlgebraicSpace.CoherentModuli.limit_preserving`, with its
proof `sorry`. It gives exactly the three explicit clauses in the node, rather
than replacing the groupoids by sets of isomorphism classes. The only other
declarations, `CoherentModuli.Fiber` and `CoherentModuli.Lift`, are abbreviations
for Mathlib's `Functor.Fiber` and the subtype of actual arrows satisfying
`Functor.IsHomLift`. Their data are real; there is no postponed construction.
Only the item's `lean` field changes. No statement correction, new node or
dependency module is needed.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. The two spaces are
  `{X B : AlgebraicSpace S}`, and `f : X ⟶ B` is the given S-morphism.
  Universe `u` is explicit; sites retain their inherited object universe `u+1`
  and module carriers remain in `u`. There is no imposed equality of site and
  coefficient universes. `I : Type u` is the required small index set.
- Finite presentation of f is `_hf : ProperQuotFinitePresentation f`.
  Its existing definition is local finite presentation, quasi-compactness and
  quasi-compact diagonal. Neither separatedness nor flatness of f is assumed.
- Local finite presentation of B over S is
  `_hB : ∀ U : B.EtaleSite, LocallyOfFinitePresentation U.obj.left.hom`.
  Here `U.obj.left` is the actual S-scheme chart and `.hom` is its structure
  map to S. This is the usual etale-local definition on the source of the
  morphism B -> S. One atlas suffices by etale locality, and local finite
  presentation persists on every etale chart. Thus this is exactly the source
  hypothesis, with no choice of an arbitrary map or a scheme assumption on B.
- The existing `CoherentModuli f` has `base : ProperQuotTest B`, a scheme T
  over S and its actual map b to B. Its `module` lives on `properQuotFibre f
  base`, the existing sheaf fibre product X times_B T.
- `quasiCoherent` and `finitePresentation` are precisely Mathlib's
  `SheafOfModules.IsQuasicoherent` and `IsFinitePresentation`: local cokernels
  of maps of sums of the structure sheaf, finite sums for finite presentation.
- `flat` quantifies over every etale scheme chart and applies the recorded
  `Scheme.Modules.IsFlatOver` to its Zariski restriction and actual map to T.
  For these quasi-coherent modules that affine-local predicate is equivalent
  to stalk flatness over the base local rings. It is the item's chart convention,
  not an unmentioned replacement by geometric-stalk flatness.
- `properSupport` is the existential Z, closed immersion i, proper map to T,
  finite type quasi-coherent G, and `Nonempty ((moduleDirectImage i).obj G ≅ M)`
  already used in `ProperQuotient`. It is not an extra supplied support or an
  assumption about annihilator ideals commuting with arbitrary base change.
- `CoherentModuli.Hom` retains a map of tests over B and the actual isomorphism
  `v_X^* M₁ ≅ M`. `identity` uses `moduleTensorPullbackId`; `composition` uses
  `moduleTensorComposition` with its pure-tensor normalization. The fibre
  category retains every module automorphism and equality of base maps.
- `[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]` expresses an arbitrary
  nonempty directed preorder. `D : Iᵒᵖ ⥤ Over S` is the inverse system;
  `_haff` says every stage is affine and `_htrans` says every transition is
  affine. `c : Cone D` and `_hc : IsLimit c` give the specified limit in S-schemes.
  No separate affine hypothesis is imposed on the limit (it follows).
- First conjunct: every `x : Fiber f c.pt` has an index i, a stage object xi,
  and an actual `Lift (c.π.app (op i)) x xi`. Such a lift includes the tensor
  isomorphism identifying xi's restriction with x, including its base map.
- Second conjunct: for stage objects xi, yi and specified restrictions px, py,
  EVERY arrow a between their limit restrictions descends. The j, hij, xj, yj,
  qx, qy, rx, ry and b are the common later stage, restricted objects, their
  specified restriction lifts and the descended isomorphism. The equations
  `rx.val ≫ qx.val = px.val`, `ry.val ≫ qy.val = py.val` and
  `a.val ≫ ry.val = rx.val ≫ b.val` ensure that it is exactly a that descends.
  Objects initially at different stages can first be moved to a common stage,
  since directedness supplies a common upper bound and tensor pullback preserves
  their conditions. Thus the common-stage presentation loses no eventual arrow.
- Third conjunct: if stage arrows a and b agree after precomposition by their
  specified limit restriction px, then at a later j their composites with qx
  agree. Equality is of actual total-category arrows, including their module
  maps. Since these arrows are cartesian pullback isomorphisms, this is exactly
  equality of their restricted fibre arrows. Conversely equality at a stage
  persists by functorial pullback. These are precisely the eventual-arrow
  relation and faithfulness. The first two clauses give essential surjectivity
  and fullness, hence the natural eventual-arrow comparison is an equivalence.

Dependencies read and used (full declarations and docstrings were opened):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-size-convention`: its record is explicitly metatheoretic, with no
  declaration or import; explicit universes implement it here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`; the `properQuotFibre` uses this exact object.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  Mathlib `SheafOfModules.IsQuasicoherent`; the same predicates are used in
  `CoherentModuli` rather than a private copy.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotTest`,
  `properQuotFibre`, `properQuotSnd`, `properQuotFibreMap`,
  `ProperQuotFinitePresentation`; its `ProperQuotient` fixes the identical
  four target conditions used by the coherent-family category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, `MapIsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- The already recorded definitions `CoherentModuli`, `CoherentModuli.Hom`,
  `identity`, `composition`, `category` in
  `Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral` supply exactly the category
  defined in the item's own text. Their definitions work for every f; the
  separatedness hypothesis belongs only to `coherent_stack_general`, which is
  neither invoked nor an assumption here. These declarations are already in
  that node's `lean.declarations`; creating a second definition node or category
  would duplicate them. No DAG dependency on the downstream algebraicity
  THEOREM is introduced.
- `Mathlib.CategoryTheory.FiberedCategory.Fiber`: `Functor.Fiber` and
  `Functor.IsHomLift` specify the exact fibre and base arrow.

Proof imports include all currently recorded project proof-dependency modules:
`SpaceModuleBaseChangeFlatProperSupport`, `AlgebraicSpaceFlatProperFpLocality`,
`SpaceFlatDirectImageBaseChange`, `SpaceChangeBase`,
`SpaceFinitePresentationModuleLimit` and the already public quasicoherent-module
module. The remaining proof nodes have no current project Lean module to import.
The available module-continuity declaration is
`finitePresentation_module_descent_affineLimit`, whose three clauses are read
and followed in the proof docstring. The proof docstring includes all seven
steps of the reviewed split, especially both uses of the flat-chart test.

Import-cycle advisory for the maintainer: `SpaceCoherentStackGeneral` currently
contains both the reusable category definitions and its algebraicity theorem.
It does NOT import this delivery. Per stages/2-statements.md section 3 rule 7,
its future proof import of `SpaceCoherentLimitPreserving` must be omitted while
those definitions share that module: that reverse import would create a cycle.
This is an import-packaging issue, not a mathematical dependency on algebraicity.
No live source is edited in this delivery. An eventual upstream refactoring can
move the shared definitions into a definition-only module.

Edge cases checked against the source and the actual types: a one-element
system; preorders with distinct equivalent indices; empty X, empty T or empty
stages; the zero module and empty proper carrier; non-Noetherian bases; a base
B that is not a scheme or not quasi-separated; nonseparated finitely presented f;
and different original descent indices. No nonzero-rank, finite-type base,
Noetherian, separated, flat-transition, nonempty-space or scheme-B hypothesis
has appeared. The empty index system is excluded exactly as in the node.

Searches performed:

- `msearch.py ... leanfinder "The groupoid of finitely presented quasi-coherent
  modules flat over the base with proper support is limit preserving on affine
  schemes"`: 8 hits, affine transition limits and scheme flatness, no groupoid
  continuity statement.
- `msearch.py ... leansearch "The category of finitely presented quasi-coherent
  modules flat over a scheme with proper support and arrows tensor pullback
  isomorphisms"`: 8 hits, module pullback/adjunction and local finite-presentation
  predicates, no such category or continuity theorem.
- `msearch.py ... leanfinder` with that same category query: 8 hits on flatness
  and local presentations, no such category or continuity theorem.
- `msearch.py ... loogle "SheafOfModules.IsFinitePresentation,
  AlgebraicGeometry.Scheme.Modules.IsFlatOver"`: 0 hits; the latter project
  identifier is unknown to the Mathlib service.
- `msearch.py ... grep "Cohstack|coherent.*limitPreserv|proper.*support.*descen"`
  and `"CoherentModuli|Cohstack|coherent.*limitPreserv"`: 0 Mathlib hits.
- `rg` of the project Lean directories for coherent categories, limit preservation,
  and `CoherentModuli` found the exact category in `SpaceCoherentStackGeneral`;
  the scheme-only `FlatCoherentModuli` has different objects. Neither project
  directory has this limit-preserving theorem. Searching the item id in
  `lean/WeilConjectures` found none.
- `rg -l CoherentModuli dag/nodes` found the category's existing declaration
  record in `lem-sfb-space-coherent-stack-general`, reused without copying.
  `python3 tools/blueprint_refs.py search 'coherent families'` found no blueprint
  node duplicating this statement. The current blueprint's direct-image proof
  (3) and Stacks quot.tex Situation 08KB and Lemma 08KD were read locally.

Validation: `scompile.py Q39 lem-sfb-space-coherent-limit-preserving <module>`
compiled the sandbox and library-named file cleanly, each in 3.3 seconds.
No STATEMENT-DISPUTED flag or source correction is needed.

## Second reading by Q39

This is a separate self-check of the opened node and final file, not a claim
that another worker read them; the dispatcher expressly forbids starting other
agents and assigns independent review to the maintainer. I checked every
hypothesis and clause against the correspondence above. In particular, the
category's definition has no separatedness requirement (only its separate
algebraicity theorem does), the support is a proper closed carrier, flatness
uses the chart convention, arbitrary base maps to B are retained, and all three
factorization equations in arrow descent are present. The third clause asserts
actual eventual equality. The index is a nonempty directed preorder in the
scheme universe, and the limit is specified by an IsLimit witness. No mismatch
was found and no statement or dependency node was changed. The existing category
is reused; the reverse proof-import cycle must be omitted as documented above.
