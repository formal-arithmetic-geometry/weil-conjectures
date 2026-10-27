## Worker report

This stage-2 delivery states `CategoryTheory.invariantClosedSubstackDescent` in
`Sheaf.AlgebraicGeometry.InvariantClosedSubstackDescent`. Its sole proof is `by sorry`.
Two new definition nodes supply the previously absent closed-substack and invariant-ideal
vocabulary. All definitions have explicit data; they contain no postponed proofs.

The inherited BLOCKED ending was a stage-1 split objection. The current node has an accepted
stage-1 split, no Lean record, and a stage-2 queue entry. The current brief-stage2 §0 explicitly
says that the accepted split is the input to stage 2 and is not an obstacle. Its statement,
proof, proof dependencies, source, status and review metadata have been preserved. Only `lean`
and the addition of the two new definition-node ids to `stmt_deps` change.

Source read: `literature/stacks-project/stacks-properties.tex`, the full statement and proof
of lemma-immersion-presentation (04YN), definition-substacks, lemma-substack-image (0506),
and lemma-substacks-presentation (0507), including the closed case. The node's six proof
steps are transcribed into the theorem's docstring. The source's definition includes
algebraicity in its closed-substack convention. The item's scheme-test convention instead
asks for algebraicity as a conclusion; the delivery follows that convention and concludes
`IsAlgebraicModuliStack W.category` rather than assuming it in the new definition.

Hypothesis and clause correspondence:

- Base scheme: `{S : Scheme.{u}}`. Schemes over it are `Over S`, not independent schemes
  without structural maps.
- Algebraic stack over S: `(F : BasedCategory.{v, w} (Over S))` and
  `(hF : IsAlgebraicModuliStack F)`. This is the recorded algebraic-stack predicate,
  including its étale stack, algebraic-space diagonal and smooth-atlas conditions.
- Scheme atlas U and map p: `(U : Over S)` and
  `p : BasedFunctor (discreteModuli (yoneda.obj U)) F`. All maps commute with the structural
  projection to schemes.
- Smoothness, surjectivity and representability of the atlas: `hp : IsSmoothModuliAtlas F U p`.
  This is precisely the recorded predicate: every scheme base change is an algebraic space
  with smooth surjective specified projection. No quasi-compactness or finite-type assumption
  is introduced.
- Closed substack: `ClosedModuliSubstack F` has an object predicate, stability under every
  arrow (every arrow is cartesian in a CFG), stack descent for the full subcategory, and
  projection-compatible scheme base changes by closed immersions. Stability under arrows
  includes closure under isomorphisms and their inverses, so the full category is strictly
  full. Its inclusion is the actual `fullModuliInclusion`, not an unrelated map. The closed
  scheme tests imply representability, as required by the item.
- Closed subschemes of U: `U.left.IdealSheafData` is Mathlib's existing quasi-coherent ideal
  sheaf data. Its `subscheme` and `subschemeι` give the closed subscheme and canonical
  immersion. The existing `IsClosedImmersion.overEquivIdealSheafData` and
  `IdealSheafData.ker_subschemeι` identify this encoding with closed subschemes as subobjects,
  including arbitrary non-finitely-generated ideals and nonreduced closed subschemes.
- Relation R and invariance: a scheme-valued arrow of `U ×_F U` is exactly two maps
  `a b : T ⟶ U` together with a 2-isomorphism between p composed with them. Thus
  `IsInvariantClosedAtlasIdeal p I` quantifies over every such T, a, b and 2-isomorphism and
  asks for `I.comap a.left = I.comap b.left`. Here `comap` is Mathlib's actual
  scheme-theoretic inverse-image ideal, with `comapIso` identifying its closed subscheme
  with the scheme fibre product. Equality on every scheme test is equality of closed
  subspaces of R. This retains nilpotent structure and is stronger than equality of point
  subsets in exactly the way required by the node. No presentation of R, or extra chosen
  relation or groupoid law, is assumed.
- Bijection: the existential `e : ClosedModuliSubstack F ≃ {I //
  IsInvariantClosedAtlasIdeal p I}` supplies both directions and both inverse identities.
  Every image is pinned to the actual pullback by the next clause, so the existential is a
  characterization of the canonical bijection and does not substitute an arbitrary bijection.
- Pullback identity `U ×_F W = Z`: `HasSchemeModuliBaseChange W.inclusion U p
  (closedAtlasScheme U (e W).val) (closedAtlasSchemeι U (e W).val)` says that the
  discrete groupoid of that precise closed subscheme is equivalent over S to the 2-fibre
  product, and that its first projection is 2-isomorphic to its specified closed immersion
  into U. It expresses equality of closed subobjects, whose presentations are only unique
  up to unique isomorphism, without demanding equality of arbitrary scheme representatives.
- Algebraicity of each descended substack: `IsAlgebraicModuliStack W.category` is a
  conclusion for every W. Surjectivity of e makes this apply to every invariant ideal's
  descended closed substack as well.
- Atlas `Z → W`: the existential q has domain exactly the scheme of `(e W).val`; its
  composite with the full inclusion is required to be 2-isomorphic to `Z → U → F`.
  `IsSmoothModuliAtlas W.category (closedAtlasScheme U (e W).val) q` supplies the
  representability, smoothness and surjectivity. Full faithfulness of the actual inclusion
  ensures that this lift is the projection of the already specified cartesian square up
  to unique 2-isomorphism. No unrelated atlas can satisfy the square in place of this one.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith` and `AlgebraicSpace.IsEtale`, through the existing
  algebraic-stack and smooth-atlas predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, through
  `SpaceMapIsSmooth` and `IsSmoothModuliAtlas`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `CategoryTheory.IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas` and `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `BasedCategory`/`BasedFunctor`
  from the re-exported Mathlib interface, `discreteModuli`, `discreteModuliMap`,
  `ModuliTwoIso`, `moduliTwoFiberProduct`, `moduliTwoFiberFst` and `IsModuliStack`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
  The Mathlib proof dependency `IsClosedImmersion.isStableUnderBaseChange` is already
  available through this import. All other theorem proof dependencies currently have
  no recorded declaration; no proof is written and no duplicate theorem is introduced.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `CategoryTheory.fullModuliSubcategory`
  and `fullModuliInclusion`. These existing general constructions are reused directly.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.IdealSheafData`, `Scheme.Hom.ker`,
  corresponding to `def-sbc-closed-immersion-ideal-sheaf`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `IdealSheafData.comap`; the existing
  `subscheme`, `subschemeι` constructions supply the actual ideal-defined closed scheme.

Edge cases checked mathematically before drafting: empty base and empty atlas are allowed;
zero and unit ideals give the whole and empty closed subscheme; no nonempty or nonzero
hypothesis appears. Nilpotent thickenings are distinguished by ideal equality, including
on nonreduced scheme tests. A noninvariant ideal does not enter the codomain subtype.
Nontrivial automorphisms are retained by the fibred groupoids and every 2-isomorphism is
included in the relation tests. No characteristic restriction, reducedness, Noetherian,
finite-presentation, or quasi-compactness hypothesis appears. Universe u is shared by the
schemes and all scheme tests; independent v,w describe the ambient total category and do
not restrict test-scheme size. No index set, geometric point or field test replaces a
scheme test. No `let`, `show`, local notation or private construction appears in a statement.

Searches made with the prescribed `msearch.py`, with their full machine-returned records
retained in both new nodes' `mathlib_searches`:

- LeanFinder: “Closed substacks of an algebraic stack correspond to scheme-theoretically
  invariant closed subschemes of a smooth atlas”: eight scheme closed-immersion hits,
  including `IsClosedImmersion.overEquivIdealSheafData`; no stack-descent theorem.
- Loogle: `"Subfunctor", "pullback"`: zero hits.
- Mathlib grep: `ClosedSubstack|closedSubstack|invariantClosed|IsClosedImmersion` in
  AlgebraicGeometry: existing scheme closed-immersion facts, no closed-substack interface.
- LeanSearch: “Closed substack as a strictly full subcategory with closed subscheme base
  changes”: scheme closed-immersion and full-subcategory hits, no closed-substack definition.
- LeanSearch: “Scheme theoretic invariant closed subscheme under the relation of a stack
  atlas equality of pullback ideal sheaves”: existing `IdealSheafData.comap`, `comapIso`,
  `subscheme`, `inclusion`, `ker_subschemeι`, and the closed-immersion/ideal equivalence.
  These ingredients are reused, and no compound invariant-atlas predicate was found.
- Direct rg of Mathlib, `lean/WeilConjectures` and `lean/Sheaf`: no occurrence of the proposed
  new declaration names; no theorem indexed by this item's blueprint id. Existing open
  substack machinery was read and its general full-subcategory constructions were reused.
- DAG definition searches for closed substacks and invariant atlas ideals found no
  corresponding definition node. `tools/blueprint_refs.py search 'closed substack'` returned
  zero blueprint matches; its `ancestor` command reports the inherited null ancestor.

Validation: all three delivered modules compiled individually through the prescribed
`scompile.py`, including their library-form names, in dependency order. No errors or
non-sorry warnings were reported. `autoImplicit` is false, all universes and binders are
explicit. The definitions contain no sorry; the only sorry is the named item theorem,
with its complete six-step proof docstring. No statement correction or disputed statement.

## New nodes

`def-sfb-closed-moduli-substack` supplies the missing closed-substack notion and a helper
`HasSchemeModuliBaseChange` retaining the test-scheme projection. The existing
`HasSpaceBaseChange` concerns a presenting algebraic space, whereas closedness here must
exhibit an actual closed subscheme of the given test scheme. `IsRepresentedByScheme`
alone does not retain that specified projection. The module reuses the already existing
full-subcategory/inclusion constructions and `IsModuliStack`, so no general CFG, stack,
full category, or scheme immersion is defined twice. Source: definition-substacks and
0507, with the item's explicit scheme-test convention. The three kinds of searches are
recorded above and in the node; they find scheme notions but no matching closed-substack
interface. Declarations: `HasSchemeModuliBaseChange`, `ClosedModuliSubstack`, and its
`category` and `inclusion`.

`def-sfb-invariant-closed-atlas-ideal` supplies the missing relation-invariance predicate
and the actual ideal-defined closed scheme over S with its canonical immersion. Source:
0507 and 04YN, where `s⁻¹Z=t⁻¹Z` is equality as closed subspaces. The definition tests all
scheme-valued arrows of the existing 2-fibre product and uses Mathlib's scheme-theoretic
ideal `comap`; it introduces no replacement inverse image or closed-subscheme construction.
Its searches find exactly those reusable Mathlib ingredients, not the invariant-atlas
predicate. Declarations: `IsInvariantClosedAtlasIdeal`, `closedAtlasScheme`,
`closedAtlasSchemeι`. Both new nodes are directly cited in the item's `stmt_deps`.

## Second reading by NV

No second worker was started: the dispatch brief prohibits subagents and assigns the
independent reading to the maintainer after delivery. This paragraph records a final
self-check, not an independent review. The actual file and the node were compared again:
all base, algebraicity and atlas assumptions are retained; ideal comap equality renders
scheme-theoretic invariance; the projection-compatible base-change condition pins the
bijection to pullback; the final q is pinned to the restricted p; smooth surjectivity and
algebraicity are conclusions. The two new definition nodes and each declaration's source
and blueprint docstrings were checked. No mismatch or statement change was found.

Dry-run repair: the current server schema (updated 2026-10-23) requires `import_flags`
on new definition nodes. Both new nodes now carry `import_flags: []`; no imported
proof or node statement was changed.
