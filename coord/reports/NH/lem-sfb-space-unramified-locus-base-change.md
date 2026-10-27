## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceUnramifiedLocusBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.exists_unramified_open_baseChange`, with its entire
proof postponed by `sorry`. No definition is introduced and nothing is proved.
The statement follows Stacks, Morphisms of Spaces, Tag 05W2,
`lemma-where-unramified`, with Z = Y (local source, lines 7577–7644), together with
the neighbourhood definition in Tag 03ZH. No statement correction is needed.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `X Y : AlgebraicSpace S` and `f : X ⟶ Y`
  are arbitrary algebraic spaces and their natural transformations over that base.
- The sole finite-type hypothesis is `hf : MapIsLocally (@LocallyOfFiniteType) f`.
  `MapIsLocally` quantifies over every compatible pair of representable etale scheme
  charts and applies the scheme predicate to the top scheme map. Thus it is precisely
  the node's etale-local interpretation, with no representability assumption on f.
- `∃ (U : AlgebraicSpace S) (j : U ⟶ X)` and
  `IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) j.hom.hom` display the
  open subspace. The node defines an open subspace as exactly this kind of inclusion.
  Its literal subfunctor is Mathlib's `Subfunctor.range j.hom.hom`; no second
  `OpenSubspace` definition is made. Scheme tests force this map to be a monomorphism:
  after pulling back two scheme sections, they factor through an open immersion,
  which is monic. Thus the range retains precisely the displayed open inclusion.
- `MapIsLocally (@AlgebraicGeometry.IsUnramified) (j ≫ f)` states unramifiedness of
  the restriction. The scheme predicate is exactly locally finite type plus an
  open-immersion diagonal, reused from the recorded dependency. Applying the existing
  chart-test predicate gives the same all-compatible-chart condition as the existing
  `SpaceChartwiseUnramified` (SpaceUniversalConormal.lean:62); no copy is defined.
- The first `∀ (V ...) (i ...)` ranges over every open subspace with unramified
  restriction and asserts `Subfunctor.range i.hom.hom ≤ Subfunctor.range j.hom.hom`.
  This is largestness in the inclusion order of open subfunctors, including U itself.
- `∀ x : Point X.obj.obj, x ∈ pointImage j.hom.hom ↔ ∃ V i, ...` identifies the
  underlying point set with points having an unramified open neighbourhood. The
  conjunction inside that existential repeats exactly openness, unramifiedness of
  the restriction, and membership of x in its point image.
- The final universal clause takes every `Y' : AlgebraicSpace S` and `h : Y' ⟶ Y`,
  with no condition on h. `X', p, f'` and `IsPullback p.hom f'.hom f.hom h.hom`
  specify its sheaf fibre product and its projections. This permits the chosen
  fibre product as well as any isomorphic presentation; the universal property
  transports all displayed conditions, so this changes no mathematical strength.
- Its existential `U', j'` has open inclusion and unramified restriction, followed
  by the same largestness condition for f'. Thus it is U(f'), not an arbitrary
  unramified open that might be smaller. The final equality
  `Subfunctor.range j'.hom.hom = (Subfunctor.range j.hom.hom).preimage p.hom.hom`
  is equality of open subfunctors, not merely equality of point sets. The preimage
  is the fibre product open because its sections are precisely those whose images
  under p belong to the range of j. Largestness also makes both subfunctors unique.
  The point-locus characterization upstairs follows directly from its largestness
  and unramifiedness, by the same neighbourhood definition already expanded below.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`; the final clause uses `IsPullback` on these sheaves.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`, with `Point`
  from its public dependency `AlgebraicSpacePointClasses`.
- `Mathlib.CategoryTheory.Subfunctor.Image`: `Subfunctor.range`, and subfunctor
  `preimage` from its public dependency `Subfunctor.Basic`.

The two landed owning definition nodes `def-sfb-space-morphism-properties` and
`def-a1-space-point-topology` are added to stmt_deps to cite these already existing
interfaces. No existing dependency record changes and no new nodes are needed.
All stated proof dependencies are imported (non-public unless also needed in the
signature). `lem-sfb-unramified-etale-compatible-charts` has no Lean attachment yet,
so has no import; its accepted proof step is retained in the declaration docstring.

Edge cases checked before writing: for empty X the empty open is largest, the point
clause is vacuous and every base-changed source is empty. For an everywhere unramified
f, U is the whole source; for the identity f this is again the entire source. For an
empty unramified locus U is the empty open. The base-change quantifier includes empty
Y', identity maps, nonsurjective maps and nonflat maps: no extra assumption removes
any case. An empty base permits only empty spaces. All schemes, test fields and spaces
use the existing u-universe convention; point classes remain `Type (u + 1)` as defined
upstream. No universe equality, separation, quasi-compactness or nonemptiness is added.

Searches (2026-10-24):

- msearch leansearch, `unramified locus locally finite type algebraic spaces arbitrary
  base change`: 8 hits, concerning unramified algebras, scheme base-change stability,
  and ring unramified loci; no algebraic-space locus theorem.
- msearch leanfinder, `The unramified locus of a locally finite type morphism of
  algebraic spaces is open and commutes with arbitrary base change`: 8 hits, including
  `Algebra.isOpen_unramifiedLocus` and scheme formally-unramified declarations; no match.
- msearch loogle, `"unramifiedLocus"`: 6 ring-level hits, no algebraic-space theorem.
- msearch grep, `unramifiedLocus|Unramified.*Locus`: 14 Mathlib hits in ring theory,
  no algebraic-space result.
- rg in WeilConjectures and Sheaf for `unramifiedLocus`, `Unramified`, chart tests and
  the item id: existing scheme theorem `unramifiedLocus_baseChange`, the recorded
  `MapIsLocally`, and `SpaceChartwiseUnramified`; no duplicate of this statement.
  Exact names `SpaceUnramifiedLocus`, `IsUnramifiedOnOpen` and
  `space_unramified_locus` yielded no existing declaration. The node-id search in
  WeilConjectures yielded no hit. All used notions are reused directly.

Validation: scompile.py compiled this module both as a sandbox file and at its library
module path, cleanly (3.2 s and 3.6 s). Expected sorry is the sole postponed theorem.
No statement dispute or known node fault.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
