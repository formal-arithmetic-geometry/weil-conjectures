## Worker report

The module `Sheaf.AlgebraicGeometry.DmPointStabilizer` states
`CategoryTheory.fieldPoint_factors_dmOpen_iff_unramified_automorphismSpace`, with
one postponed proof. It also defines `CategoryTheory.IsModuliAutomorphismSpace`,
an explicit representation predicate for the automorphism sheaf occurring in this
very node. This helper has real data, no choice and no postponed theorem.

The item has a stage-1 split reviewed by Q04, but no Lean record in the base.
The previous worker's unchanged-node rejection did not constitute a stage-2
statement delivery. This packet adds the theorem and its Lean record.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the stack is
  `F : BasedCategory.{v, w} (Over S)`. Its stack condition is `hstack`, its
  representable diagonal is `hdiag`, and its smooth surjective scheme atlas is
  `hatlas`. The latter retains `HasSpaceBaseChange`, the actual map `p` to each
  test scheme, `SpaceMapIsSurjective`, and smoothness on every etale scheme
  chart. This is the same atlas interface as the published
  `unramifiedModuliDiagonal_iff_etaleAtlas` theorem, written inline to avoid
  introducing another definition of algebraicity.
- The full open substack is `U : OpenModuliSubstack F`; `hU` says its relative
  diagonal is unramified. `hmax` says every full open with that property is
  contained in U. Together they express exactly the given largest open.
- `K : Type u` and `[Field K]` bind an arbitrary field. The morphism
  `a : Spec (.of K) ⟶ S` specifies its S-structure. The based functor `x`
  from the discrete representable of `Over.mk a` is the map from Spec K to F.
  There is no algebraic-closedness, perfectness or characteristic assumption.
- `G : AlgebraicSpace S` with `p` to the representable of `Over.mk a` is an
  algebraic space over Spec K, viewed over S with its specified structure map.
  `hG : IsModuliAutomorphismSpace ...` identifies its sections over EVERY
  scheme V with a map V -> Spec K with vertical natural automorphisms of the
  restriction of x. These are automorphisms in the fibre by fibred Yoneda.
  The last clause of the definition identifies restriction along every W -> V,
  component by component, so the identification is natural, rather than an
  unrelated collection of bijections. Natural set-valued representation
  suffices: composition, identity and inverse transport the canonical group
  structure uniquely; the theorem only asks about the underlying space map.
- The left side of the conclusion is an actual lift `y` to `U.category` and a
  vertical 2-isomorphism of its composite with the full inclusion to `x`.
  This is factorization through U, including the ordinary up-to-2-isomorphism
  convention for stack morphisms. The right side is
  `SpaceMapIsUnramified G (Over.mk a) p`, exactly scheme unramifiedness on all
  etale charts of the source space over the specified field spectrum.
- Both directions are retained by `↔`. There is no added assertion that a
  largest open or an automorphism representation exists: both are given in
  the informal statement.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsModuliStack`, `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`,
  `SpaceMapIsSurjective`, `discreteModuli`, `discreteModuliMap`, `ModuliTwoIso`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`,
  through the existing chartwise definition, not an inline replacement.
- `Mathlib.Algebra.Field.Defs`: `Field` (the mathlib-match dependency).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicGeometry.AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `CategoryTheory.OpenModuliSubstack`, its `category` and `IsContainedIn`,
  `fullModuliInclusion`, `HasUnramifiedModuliDiagonal`, `SpaceMapIsUnramified`.
  The corresponding already-landed definition node
  `def-sfb-open-moduli-substack` is added to `stmt_deps` without changing the
  informal statement. No new definition node or dependency repair is needed.

All four proof dependencies have no Lean or Mathlib record in the base; none
is needed to type the statement. Thus no imports of non-existent modules are
invented. Their six-step atlas/descent argument is retained completely in the
main theorem docstring for subsequent proof work.

Source and edge cases:

Read Stacks `stacks-morphisms.tex`, Tag 0DSN, including its proof and the preceding
largest-DM-open lemma. The theorem explicitly says its part (1) is proved by the
same atlas construction as part (2). The relative-base convention is Tag 050N(1).
The full open-substack predicate and the unramified relative-diagonal interface
were read in their owning module and DAG node. This packet changes no statement.

Checked mathematically: schemes (trivial inertia, full DM open); a classifying
stack of a smooth positive-dimensional group (the criterion fails at its field
point); a finite etale group (the criterion holds); mu_p in characteristic p
(nonunramified inertia, so the point does not lie in the DM open); imperfect
fields (no separability or perfectness assumed); empty stack/open (no field
point exists in the empty stack); and nonreduced test schemes (not discarded by
the representation predicate). The auxiliary `v,w` are independent category
universes; scheme tests and fields use the fixed geometric universe u, with no
extra equality between these universes.

Searches before writing:

- `msearch.py`, LeanFinder: "An algebraic stack field point lies in its Deligne
  Mumford open locus if and only if its automorphism group algebraic space is
  unramified". Eight hits concern algebraic unramified loci, scheme formal
  unramifiedness and scheme etaleness. None states the stack criterion.
- `msearch.py`, Loogle: `"AlgebraicStack"`, zero hits.
- `msearch.py`, Mathlib grep: `AlgebraicStack|DM.*[Ll]ocus|stabilizer.*unramified`,
  five unrelated hits (number-field stabilizers, scheme Zariski main theorem,
  module equality loci and separated maps).
- `rg` of `lean/WeilConjectures` for the item id: no hits; concepts
  `AlgebraicStack|automorphism.*[Ss]pace|DM.*[Ll]ocus` only found unrelated linear
  automorphisms in zeta/Fourier files.
- `rg` of `lean/Sheaf` found the existing open-substack and unramified-diagonal
  interfaces, reused here; `DMGeometricInertiaTrivial` assumes DM and trivial
  geometric inertia, a different statement; `ProperCurveAutomorphismScheme`
  handles a specific curve's automorphisms, not a general stack object.
- DAG searches for open-substack and automorphism-space notions found the
  existing `def-sfb-open-moduli-substack`, reused. `tools/blueprint_refs.py search`
  for "open substack" and "automorphism space" each returned zero matches.

Validation: every delivered module is compiled separately using `scompile.py`,
and the prescribed `deliver2.py --no-push` preflight is run before delivery.
No `STATEMENT-DISPUTED` issue, new node or corrected statement is introduced.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
