## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyQuasiFinitePseudoTorsor` states
`AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_of_pseudoTorsor` with `sorry`.
The natural-language statement is unchanged. I read Stacks `spaces-groupoids.tex`,
`definition-pseudo-torsor` (04TW), and `lemma-pseudo-torsor-implications` (0DSK),
including its proof. The conclusion is exactly part (2).

The correspondence with every hypothesis and clause is as follows:

- Scheme and size convention: `{S : Scheme.{u}}`, with an explicit universe `u`.
  Test schemes are `Over S`, with scheme universe `u`, as in the recorded
  algebraic-space interface. No independent smaller test universe is introduced.
- Base algebraic space: `(B : AlgebraicSpace S)` uses the existing full subcategory
  of fppf sheaves, including its representable diagonal and surjective etale atlas.
- Algebraic spaces over B: `(G X : Over B.obj)` give fppf sheaves and their actual
  structure maps `G.hom`, `X.hom`. The hypotheses `hG : IsAlgebraicSpace G.left`
  and `hX : IsAlgebraicSpace X.left` say that these sheaves are algebraic spaces.
  `ObjectProperty.homMk` makes their structure maps maps in `AlgebraicSpace S`.
  This is the same slice-of-sheaves encoding used by the landed free-action node.
- Group structure: `[GrpObj G]` is Mathlib's internal group object in this slice.
  `MonObj.mul`, `MonObj.one`, and `GrpObj.inv` supply the multiplication, identity,
  and inverse as morphisms over B. Their associativity, unit and inverse axioms
  are part of the structure. The slice unit is B and its product is the sheaf
  fibre product, by `groupSpaceOverCartesian` and `Over.cartesianMonoidalCategory`.
  On each scheme with a map to B these operations induce a group, naturally in
  that test scheme, as in Mathlib's `Hom.group` and `yonedaGrpObj` construction.
- Action: `[ModObj G X]` supplies `ModObj.smul`, an actual morphism over B,
  with `one_smul` and `mul_smul`, precisely the two stated action identities.
  Being morphisms of sheaves ensures naturality under all scheme pullbacks.
- Pseudo-torsor: `_hθ : IsIso (ModObj.leftSMul G X)` asserts invertibility of the
  canonical morphism. I read its definition in Mathlib's Cartesian/Mod module:
  it is `lift` of the action and the second projection. Thus it is exactly
  `(g,x) ↦ (a(g,x),x)` from G times_B X to X times_B X. An isomorphism in this
  slice is equivalent to an isomorphism of its underlying sheaves. No arbitrary
  comparison morphism, choice of trivialization, or surjectivity is supplied.
- G locally of finite type: `_hGft : MapIsLocally (@LocallyOfFiniteType) ...`
  applies the existing chart test to the structural morphism G to B.
- X locally of finite type: `_hXft` applies the same test to X to B.
- G locally quasi-finite: `_hGq : SpaceMapIsLocallyQuasiFinite ...` uses the
  existing chart test with `Scheme.Hom.IsLocallyQuasiFinite` from the recorded
  pqf-def-quasifinite module. It includes the Stacks finite-type requirement.
- Conclusion: `SpaceMapIsLocallyQuasiFinite` of the structural morphism X to B.
  Both chart predicates quantify over all compatible etale scheme charts of
  source and target, including nonsurjective charts, exactly as the node states.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme Hom.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace` and `AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`; it supplies the existing
  sheaf fibre-product interface and is public-imported for statement dependencies.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite` and `Scheme.Hom.IsQuasiFiniteAtPoint`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.SpaceMapIsLocallyQuasiFinite`.
- `Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient`:
  `AlgebraicSpace.groupSpaceOverCartesian`. Only its global slice cartesian
  instance is used; none of the quotient theorem's flatness, finite presentation,
  freeness or surjectivity assumptions is imported into this statement.
- Mathlib `CategoryTheory.Monoidal.Grp`, `Monoidal.Mod`, `Monoidal.Cartesian.Mod`,
  `Monoidal.Cartesian.Grp`, `Monoidal.Cartesian.Over`: `GrpObj`, `ModObj`,
  `ModObj.leftSMul`, and the slice product and unit descriptions. Their full
  structure signatures and docstrings were read.
- Proof imports: `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` and
  `Sheaf.AlgebraicGeometry.RepresentableLocallyQuasiFiniteCalculus` for
  `AlgebraicSpace.Point` and `CategoryTheory.representable_lqf_baseChange`.
  The other proof dependency, lem-sfb-space-quasifinite-locus-open, currently has
  no recorded Lean module; no import can be added for it. It is only needed by
  the postponed proof, whose full four steps appear in the theorem docstring.

The already-landed definition nodes def-sfb-space-morphism-properties and
def-sfb-dm-stack-morphism-properties are added to stmt_deps for their chart tests.
The new definition node def-sfb-space-slice-cartesian owns the existing cartesian
instance. The item cites this definition node, rather than the quotient theorem.
No dependency record or mathematical statement correction is needed.

Edge cases checked before writing: X empty is allowed because the action and
leftSMul still exist, with an isomorphism between empty products; no point,
section, nonemptiness, cover, or surjective structure map is assumed. The trivial
action torsor X = G has the expected invertible comparison. A pseudo-torsor
without a rational point is covered by the proof's field-valued representative
and base-change trivialization. Noncommutative and nonreduced groups are allowed:
GrpObj imposes neither commutativity nor reducedness. No separatedness,
quasi-compactness, finite presentation, flatness, finiteness of the total point
set, or characteristic restriction is imposed. The base B need not be a scheme.

Searches for an existing declaration:

- `msearch.py leansearch`, query "A locally finite type pseudo torsor under a
  locally quasi finite group algebraic space is locally quasi finite": eight
  results, including LocallyQuasiFinite.mk, LocallyOfFiniteType.mk and
  instLocallyQuasiFiniteOfIsFinite, all scheme/ring results, no matching theorem.
- `msearch.py leanfinder`, the same query: eight results including
  AlgebraicGeometry.LocallyQuasiFinite and LocallyQuasiFinite.of_comp;
  none concerns algebraic-space pseudo-torsors.
- `msearch.py loogle`, query `"PseudoTorsor", "LocallyQuasiFinite"`: zero hits.
- `msearch.py grep`, query `pseudo.?torsor|GroupAlgebraicSpace|SpaceGroup`:
  zero Mathlib hits. Direct Mathlib source reading found `ModObj.leftSMul`, so
  the canonical comparison is reused instead of redefined.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, queries
  `PseudoTorsor|pseudo.?[Tt]orsor|GroupAlgebraicSpace` and
  `locally.quasi.finite.*torsor|torsor.*locally.quasi.finite`: no theorem match.
  Searching group-space interfaces found FreeFlatGroupSpaceQuotient and
  RegularGroupSpace; the latter requires commutativity and scheme base, so the
  general existing internal group object interface in the former is used.
- Direct node-id search in `lean/WeilConjectures`: no match. Search of
  dag/lean_names_upstream.json: no corresponding upstream declaration.
- Searching the chart-property interfaces found `MapIsLocally` and
  `SpaceMapIsLocallyQuasiFinite`, which are both reused.

Validation: scompile.py compiled the file as both sandbox and library module,
without errors or non-sorry warnings (4.0 and 4.5 seconds respectively).
There is no STATEMENT-DISPUTED issue. The prescribed compact-object example
module is withdrawn in the current checkout; its node points to the upstream
WeilConjectures.CategoryTheory.CompactObject, which was read for conventions.


## New nodes

`def-sfb-space-slice-cartesian` records the cartesian structure on the slice of
fppf sheaves over the algebraic space B. Its unit is the identity B to B and its
tensor is the sheaf fibre product over B, exactly the structure needed for the
group, action and leftSMul in Stacks 04TW. It has `existing: true`, module
`Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient`, declaration
`AlgebraicGeometry.AlgebraicSpace.groupSpaceOverCartesian`. I read its full
definition: its body is exactly `Over.cartesianMonoidalCategory B.obj`. Mathlib's
construction was also read: its chosen terminal object is `Over.mk (𝟙 B.obj)`
and its binary products come from pullback cones. The declaration is reused,
with no new module, no duplicate instance and no postponed proof. Empty sheaves
and arbitrary algebraic-space bases are allowed; no group structure, flatness,
finite presentation or nonemptiness is needed to define this cartesian category.

The node's mathlib_searches preserve the complete outputs of fresh LeanSearch,
Loogle and Mathlib grep searches. LeanSearch found eight results including
`CategoryTheory.Over.cartesianMonoidalCategory`; Loogle found twelve results,
including that construction and its unit and tensor descriptions; Mathlib grep
found the definition in Cartesian/Over.lean. Source grep found the already-landed
specialization and no upstream copy. DAG grep found its declaration listed only
inside the free-flat-quotient theorem node. The blueprint search `cartesian slice
sheaves` returned only lem-cbc-completed-extension-zero-comparison, a cohomology
comparison that does not define this slice structure. There was no independent
definition node for this notion. `blueprint_refs.py ancestor` returned None for
this item; the new node retains the item's null ancestor and its source route,
with the item prefixed to `via`.

## Returned delivery repair

H2/theorem-stmt_dep on immutable head eb998683bfdc: repaired by adding the
definition node `def-sfb-space-slice-cartesian` with existing ownership of
`AlgebraicSpace.groupSpaceOverCartesian`, and replacing the item's
`lem-sfb-free-flat-group-space-quotient` statement dependency with that definition.
The module import remains the same because the already-landed instance lives
there; no construction or assertion of the quotient theorem is used. This is
a dependency-ownership repair, not a re-push of the same packet. The retained
sandbox statement and proof were compared with current main and agree; the
item copy was refreshed from main before restoring its Lean attachment and
repaired statement dependencies. The original theorem signature, single sorry
and four-step proof docstring are unchanged, as all were accepted in the return.
Compilation and delivery preflight are repeated for the repaired packet, including
a real server check of the existing instance through the delivery wrapper.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
