## Worker report

Item: `lem-trf-devissage-pointed-restriction`. The delivery states
`AlgebraicGeometry.PointedAffineDevissage.pointed_devissage_baseChange_and_shrinking`
in `Sheaf.AlgebraicGeometry.PointedDevissageRestriction`. Its proof is the only
`sorry`. All helper definitions have actual data or an explicit propositional
formula. The node statement and proof steps are unchanged. The repair adds the three
landed definition dependencies named by the maintainer to `stmt_deps`.

Source read: `literature/stacks-project/flat.tex`, `lemma-base-change-one-step`
(05H7), `lemma-base-change-one-step-at-x` (05H8), `definition-shrink` (05H9),
`lemma-shrink` (05HA), `lemma-base-change-complete` (05HJ),
`lemma-base-change-complete-at-x` (05HK), `definition-shrink-complete` (05HL),
and `lemma-shrink-complete` (05HM). The support-dimension-free variant is the
one already defined by the statement dependency, not the stronger original
Stacks notion. The main theorem's docstring carries all eleven DAG proof steps.

The two explicit predicates `OneStepRestrictionProperties` and
`ChainRestrictionProperties` are conjunctions of the node's clauses. They are
not hypotheses or opaque propositions. The main theorem asserts their conjunction.
The comparison and result structures belong to the operations this item states;
they do not redefine one-step data, chains, or standard shrinkings.

Hypotheses and clause correspondence:

1. The input `s : PointedAffineOneStep f F x` uses exactly the recorded dependency.
   Its fields supply local finite type of `f`, finite-type quasi-coherence of `F`
   and `G`, affineness of all four schemes, the two maps over `B`, the closed
   finite-presentation immersion, the finite map, smoothness, geometrically
   irreducible fibres and their dimension, the pushforward presentation, the
   marked-point identities, singleton marked fibre and purely transcendental
   residue extension. Nothing is added to these input hypotheses.
2. For pointed base change, `B' : Scheme.{u}`, `[IsAffine B']`, `aB : B' ⟶ B`,
   `b' : B'`, `_hb : aB b' = f x`, and `_hk : IsIso (aB.residueFieldMap b')`
   render respectively the affine pointed base, its map and marked point,
   pointedness, and the specified residue-field isomorphism. There is no
   flatness, étaleness, or finite-type assumption on `aB`.
3. The first conjunct of `OneStepRestrictionProperties` produces `X'`, `f'`,
   `aX`, `x'`, and a new one-step datum for the actual tensor pullback of `F`,
   with `f' x' = b'`. `OneStepBaseChange.baseSquare`, `.closedSquare`,
   `.finiteSquare`, and `.smoothSquare` are Cartesian squares, so the new
   diagrams are the base-changed diagrams, up to their canonical identifications.
   `.moduleIso` identifies `G'` with the actual tensor pullback of `G`;
   `.presentationSquare` pins its presentation to `moduleBaseChangeMap`.
   `.markedX`, `.markedZ`, `.markedY` and `.uniqueX`, `.uniqueZ`, `.uniqueY`
   state that all new marked points are precisely the unique lifts above the
   old points and the new base point. `.dimension` keeps the old integer `d`.
4. The first conjunct of `ChainRestrictionProperties` has the same base-change
   hypotheses and produces a chain of the SAME length `n`. `ChainBaseChange`
   recursively records `OneStepBaseChange` and retains every finite rank `r`.
   `alphaSquare` is stated for every `k : ULift.{u} (Fin r)`. Its left side
   pulls back `SheafOfModules.ιFree k` and `α`, then applies the actual canonical
   `Scheme.Modules.moduleBaseChangeMap` and the pushforward of `moduleIso.hom`.
   Its right side is the forward `tensorPullbackObjUnitToUnit` followed by
   `SheafOfModules.ιFree k` and `α'`. No inverse or isomorphism theorem is used
   to form this statement. `eQ` identifies the next input with the tensor pullback of the
   old cokernel; `quotientSquare` says this is the induced cokernel comparison.
   The recursion ends with the actual `nil` constructor and its zero sheaf.
5. A prescribed principal base restriction is given by `a : Γ(B, ⊤)` and
   `_ha : f x ∈ B.basicOpen a`. The second conjunct of the one-step predicate
   first produces a standard shrinking with base image EXACTLY `D(a)` and all
   three remaining scheme images exactly its inverse images. The corresponding
   chain clause has exact base image `D(a)` and `BaseRestrictionImages`, which
   recursively gives the inverse images on the initial scheme and every `Z,Y`.
6. A principal target neighbourhood is `w : Γ(s.Y, ⊤)` with
   `s.y ∈ s.Y.basicOpen w`. Its clause produces `R : OneStepRestriction s`,
   with base image contained in the prescribed `D(a)` and target image
   `D(w) ∩ s.g ⁻¹' Set.range R.aB`. Since the maps are open immersions over the
   base, this says exactly `Y' = W ×_B B'`, as an open subscheme of `Y`.
7. An arbitrary initial neighbourhood is `U : X.Opens` with `x ∈ U`. The next
   clause produces a shrinking with `Set.range R.aX ⊆ U` and base contained in
   the prescribed `D(a)`. `OneStepRestriction.comparison` is the EXISTING
   `OneStepShrinking`: it keeps the maps, modules, presentation, dimensions,
   principal opens and marked points. The result package also records the
   Cartesian finite square used in the source's construction (`Z' = π⁻¹(Y')`).
   This makes restriction of finite pushforward the specified canonical
   comparison and supports the following assertion about any supplied basis map.
8. For the extra one-step map, `r : ℕ`, `α : free (ULift (Fin r)) ⟶ π_*G`, and
   `_hα : ∀ ξ : s.g.fiber (f x), IsGenericPoint ξ Set.univ →
   IsResidueFibreIso α (s.g.fiberι (f x) ξ)` are exactly the finite rank, the
   given map, and the generic residue-field isomorphism on `Y_b`. For each of
   the produced restriction packages, the next conjunct gives `α'`, `eQ`, the
   same generic residue isomorphism, the equation restricting `α` through
   `restrictionPushforwardMap` and `restrictUnitIso`, and the induced cokernel
   equation. Thus the new cokernel IS the restricted old cokernel.
9. For chains the second conjunct first handles exact principal base restriction,
   then an arbitrary initial open with base inside `D(a)`, then the last-target
   request. That last request is guarded by `0 < n`, and its open is specified
   by `w : Γ(lastScheme c, ⊤)` with `lastPoint c ∈ basicOpen w`.
   `targetImages R.comparison` recursively records each actual target image
   from the EXISTING `StandardShrinking` witness. Its `getLast?` must equal
   `some ⟨lastScheme c, D(w) ∩ lastStructureMap c ⁻¹' Set.range R.aB⟩`,
   asserting the required image equality on precisely the final target.
   That witness retains every α, rank, presentation and induced cokernel map,
   by its existing `alphaSquare` and `quotientSquare` fields.
10. Residue-field preservation is stated for every `OneStepShrinking` in the final
    one-step conjunct, including base, initial, source and target marked maps.
    The final chain conjunct uses `MarkedResidueIsos` to assert the same recursively
    on every component, ending with the initial/base maps in the zero case.
11. All chain quantifiers allow `n = 0`. In the recorded definition such a chain
    requires the finite-type quasi-coherent initial module to be zero and the
    initial scheme and base to be affine. Neither base change nor initial-open
    shrinking excludes this case. Only the last-target request requires `0 < n`.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.PointedAffineDevissage`:
  `AlgebraicGeometry.PointedAffineOneStep`, `IsResidueFibreIso`,
  `PointedAffineDevissage`, and, in its namespace, `OneStepShrinking`,
  `StandardShrinking`, `restrictionPushforwardMap`, `HasPrincipalRange`.
  I opened the full source and read each signature and docstring.
- `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`:
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap`, the adjunction-defined
  comparison used verbatim in the new squares.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `tensorPullbackObjUnitToUnit`, the plain adjoint-defined forward morphism,
  owned by `def-sfb-tensor-pullback-structure-sheaf-map`. Its isomorphism theorem
  is not referenced by this delivered statement.
- `def-sfb-module-base-change-map` owns the plain `moduleBaseChangeMap` above;
  its recorded public module is imported directly.
- `def-pc-module-pullback`, with public recorded module
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, owns the tensor
  pullback used in all of these comparisons. Its exact existing construction
  is retained; no second pullback is defined.
- The existing Mathlib `SheafOfModules.mapFree`, `Scheme.Modules.restrictUnitIso`,
  `IsPullback`, `cokernel`, `IsGenericPoint` and residue-field maps are used directly.
- Already recorded proof modules for affine pullback sections, affine pushforward
  base change, quasi-coherent cokernels/images, pullback stalks, the singleton-fibre
  neighbourhood lemma and the two dimension bridges are imported privately.
  Public geometry imports are already supplied by the one-step definition;
  their recorded proof dependency modules are also listed explicitly.

Edge cases checked before and during the second reading: identity base change;
arbitrary nonflat affine base change with the required residue isomorphism;
`d = 0`; `r = 0` (the source free sheaf is zero); the zero coefficient sheaf;
length zero and length one; the whole principal open `D(1)`; arbitrary rather
than principal initial open; and separate rather than simultaneous initial/target
requests. The marked points exclude an empty marked fibre; no additional
nonemptiness assumption is introduced. All schemes and their coefficient sheaves
use the SAME arbitrary universe `u` as the dependency, and every universe and
variable is explicitly bound with both auto-implicit options disabled.

Searches actually run:

- `msearch.py ... leanfinder "Pointed affine devissage base change preserves residue
  fields standard shrinking principal open neighborhoods"`: eight hits, headed
  by `Scheme.SpecToEquivOfField` and residue-field maps; no dévissage preservation.
- `msearch.py ... loogle '"devissage"'`: zero hits.
- `msearch.py ... grep 'devissage|Devissage|baseChangeMap' AlgebraicGeometry`:
  zero hits in that search service's Mathlib index.
- `msearch.py ... leansearch "Base change and principal open shrinking preserve
  pointed affine complete devissage chains"`: eight hits about individual
  morphism/ring-map properties stable under base change, not this statement.
- `rg` on the project's `lean/WeilConjectures` and `lean/Sheaf`, for `Devissage`,
  `devissage`, the item id and the comparison names: the recorded pointed affine
  definition is present, while the other hits concern different dévissage notions
  (constructible/torsion/adic). No existing declaration states this item.
- Read `mapFree` in Mathlib's `Algebra/Category/ModuleCat/Sheaf/Free.lean` and the
  upstream module-base-change and structure-sheaf-pullback definitions before
  constructing the comparison interface. No canonical map was copied privately.

No `STATEMENT-DISPUTED` or node fault. No new nodes or dependency repairs.

## Second reading by NE

This is the author's second pass with the DAG statement, the dependency module,
the delivered module, and Stacks 05HA/05HK/05HM open; the maintainer supplies the
independent review required by the direct-delivery brief.

I checked all three numbered clauses against the explicit conjunctions above.
The first pass exposed three issues that were repaired: final-target accessors
must descend through the recursive chain (including the final `nil`), base-only
chain shrinking must state the inverse-image condition at EVERY step, and the
extra α assertion must use the full inverse-image finite square of the constructed
shrinkings rather than assert a cokernel comparison for arbitrary unrelated opens.
The result package now records that square. The residue-field conclusion still
quantifies over ALL one-step standard shrinkings, and all chain standard
shrinkings are covered by the unrestricted chain restriction package.

I checked in particular that the chain comparison uses the canonical base-change
map and keeps the same ranks, that `eQ` is constrained by the actual cokernel
projection, that all original `d` fields are retained, that all marked lifts have
uniqueness conditions, and that the last-target guard is the only positive-length
restriction. The α generic condition uses the generic point of the FIBRE, mapped
into `Y`, rather than an arbitrary generic point of `Y`. No support-dimension
hypothesis, smooth dimension equality beyond the stored `d`, flatness, or extra
condition on the base map has been inserted. The source's allowed further base
shrinking is rendered by containment in the prescribed base open; the base-only
clause retains exact equality. The final-target image is an open-subscheme
presentation of the requested fibre product, not a freely chosen isomorphic target.

The recursive reading of shrinking witnesses uses `StandardShrinking.rec` directly.
This avoids expensive dependent pattern elaboration without adding assumptions or
changing the witness being read. Temporary tracing options and compiler probes
were removed. `ChainBaseChange` is proposition-valued: its constructor witnesses
still include the actual one-step comparisons, module identifications, basis-map
and quotient-map equations. No data is selected from a bare existence theorem.

## Repair of returned head ce392a383508

H2: added exactly the three landed nodes requested by the independent reviewer:
`def-sfb-module-base-change-map`,
`def-sfb-tensor-pullback-structure-sheaf-map`, and `def-pc-module-pullback`.
I read their current node records, and their declarations and docstrings in
`ModuleBaseChangeMapOpenRestriction.lean`, `TensorPullbackStructureSheaf.lean`
and `TensorPullbackSectionAdjunction.lean`. All three recorded modules are
public imports. The item copy was refreshed from the current read-only main
node and changed only in `stmt_deps` and `lean`; no inherited main metadata was
replaced. The delivery wrapper performs the authorized rebase and packaging.

Deleted `pullbackUnitInverse` completely, including its `lean.declarations`
entry, and removed the only reference to `tensorPullbackObjUnitToUnit_isIso`.
The base-change `ChainBaseChange.cons.alphaSquare` now says, for every basis
index `k`,

```
tensorPullback.map (ιFree k) ≫ tensorPullback.map α ≫
  moduleBaseChangeMap ≫ pushforward.map moduleIso.hom =
    tensorPullbackObjUnitToUnit aY ≫ ιFree k ≫ α'
```

Both sides have source the pullback of the old unit module and target the new
finite pushforward. This is the requested forward characterization of the
canonical basis comparison. It uses only the plain construction of the
structure-sheaf map. The cokernel equation and all other clauses are retained.
For `r = 0` the basis equation is vacuous, as appropriate for the zero free
module; the cokernel equation remains present. Length zero still uses the nil
constructor, and dimensions, unique marked lifts and the positive-length
last-target guard remain unchanged.

H9 advisory: the private imports that supply only the sorried proof are retained
as plain `import`, in accordance with stage 2 rule 7. None is used to add an
assumption to the statement. The three explicit definition dependencies are
public imports.

Second reading of the repair by NE: checked the changed constructor equation
against the review's exact forward formula, its source and target, every basis
index and the zero-rank case. Confirmed the deleted inverse helper has no
remaining declaration or reference, the node records the three direct owners,
and the item still has the same main theorem signature and exactly one sorry.
This author check supplements the maintainer's independent mathematical review.
