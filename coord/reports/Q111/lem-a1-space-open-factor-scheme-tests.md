## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests` states the
item in three named theorems, each with its whole proof postponed by `sorry` and a
source/proof docstring. No definition, new node, dependency repair, or statement
correction is needed. The original node is unchanged except for `lean`.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `X Y G : AlgebraicSpace S` and arrows
  `f : Y ⟶ X`, `g : G ⟶ X` are objects and morphisms of the recorded full
  subcategory. One common universe follows the existing scheme-test convention.
- `J : OpenSubspace X` is exactly the recorded subfunctor with representable
  open-immersion inclusion `J.val.ι`. This represents the node's `j : J ↪ X`;
  maps to its underlying presheaf are precisely the natural transformations of
  the node. No separate arbitrary open map is substituted for this inclusion.
- `openSubspace_preimage_schemeTests` is universally quantified in `G,g`, so
  specializing to `Y,f` gives the first assertion, and leaving `G,g` arbitrary
  gives the assertion about `J_G`. `J.val.preimage g.hom.hom` is Mathlib's literal
  inverse-image subfunctor, the fibre product with the monomorphism `J.val.ι`.
  Its scheme-test property is
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) … .ι`.
- The point-image formula is expressed on every `a : PointRepresentative G.obj.obj`:
  `Quot.mk _ a ∈ pointImage (J.val.preimage g.hom.hom).ι ↔
  Quot.mk _ (a.map g.hom.hom) ∈ pointImage J.val.ι`.
  Every point class has such a representative by the definition of `Point` as
  `Quot`; this is exactly the inverse-image equality, without another point-map
  construction. The topology and point classes are the recorded dependencies'.
- The containment hypothesis in `openSubspace_factor_schemeTests` is precisely
  `hf : pointImage f.hom.hom ⊆ pointImage J.val.ι`. Its first conclusion,
  `IsIso (J.val.preimage f.hom.hom).ι`, says that the pullback projection to `Y`
  is invertible; this is the asserted isomorphism over `Y`.
- The existential `fJ : Y.obj.obj ⟶ J.val.toFunctor` with
  `fJ ≫ J.val.ι = f.hom.hom` states the factorization. The following universal
  equality `k ≫ J.val.ι = f.hom.hom → k = fJ` states uniqueness.
- Every scheme over the open is encoded by `T : Over S` and
  `t : yoneda.obj T ⟶ J.val.toFunctor`. The comparison is an isomorphism
  `e : Limits.pullback fJ t ≅ Limits.pullback f.hom.hom (t ≫ J.val.ι)`.
  The two equations on `e.hom` say it preserves the `Y` and `T` projections.
  These characterize the canonical comparison uniquely by the pullback universal
  property; thus this is the canonical isomorphism over `T`, not merely an
  unrelated isomorphism between the two objects.
- `IsEtale f.hom.hom → IsEtale fJ ∧ (…)` expresses representable étaleness
  of the factor conditional on that of `f`. In that implication, full point
  image `pointImage f.hom.hom = pointImage J.val.ι → IsSurjective fJ`
  expresses surjectivity on every scheme base change using the recorded definition.
- `openSubspace_pullback_image` assumes the full-image equality, with no
  étaleness hypothesis on `f`, and identifies
  `pointImage (Limits.pullback.snd f.hom g.hom).hom` with
  `pointImage (J.val.preimage g.hom.hom).ι`. This is the node's last equality.
  `g` has no étaleness, flatness, surjectivity, or finite-type hypothesis.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  schemes are locally ringed spaces with local affine neighborhoods, arrows are
  locally ringed space morphisms. Publicly available through the dependency imports.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`. The latter two quantify over
  all scheme tests, with scheme projections respectively étale and surjective.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, with
  precisely the subfunctor inclusion and representable-open-immersion property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `PointRepresentative.map`, `pointTopologicalSpace`; its imported
  `AlgebraicSpacePointClasses` supplies `Point` and `PointRepresentative`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme` were read. The first gives the algebraic-space
  status and universal property of the sheaf fibre products used here.
- Mathlib's `Subfunctor.preimage`, `Subfunctor.ι`, `Subfunctor.fromPreimage`,
  `Limits.pullback`, its projections and categorical isomorphisms provide the
  already existing constructions. No private copy is introduced.

The proof-only node `lem-a1-space-point-open-calculus` has no recorded Lean
module on the read base, so there is no module to import for that dependency.
Its mathematical uses are recorded in the proof docstrings. It is not needed
to elaborate any of the signatures. All recorded statement-dependency modules
are public imports (directly or through their recorded dependency modules).

Source checked directly in `literature/stacks-project/spaces-properties.tex`:
`lemma-factor-through-open-subspace` (03IE), `lemma-etale-image-open` (06NF),
and `lemma-points-cartesian` (03H4). They give respectively the open pullback and
full-image factorization, the monomorphism comparison on scheme tests, and the
common-field lifting argument for arbitrary pullbacks. No correction is needed.

Edge cases checked before writing: the empty open forces `Y` empty under
containment; all scheme tests of the empty open and the unique empty factor
remain covered. For `J = X`, the projection and factor reduce to the identity
restriction. Proper containment requires no surjectivity. Full image without
étaleness still gives the last arbitrary-pullback image equality; scheme-test
surjectivity is requested only inside the representable-étale implication.
An empty base-change space, a nonflat closed-point base change, and the identity
base change are included because `G,g` are unrestricted. Scheme tests have the
same universe as `S`, avoiding vacuous smaller-universe test quantifiers.

Searches for an existing statement:

- `msearch.py … leanfinder`: “For an open subspace J of an algebraic space X a map
  Y to X with point image in J factors uniquely and has the same scheme base
  changes”. Eight hits, including `AlgebraicGeometry.IsOpenImmersion.lift`,
  `lift_uniq`, and corresponding ringed-space declarations; all concern schemes
  or ringed spaces, not these algebraic-space presheaves.
- `msearch.py … leanfinder`: “Open subspace factorization algebraic spaces
  identical scheme pullbacks”. Eight scheme pullback/open-immersion hits; none
  has the required objects.
- `msearch.py … loogle '"AlgebraicSpace", "open"'`: zero hits.
- `msearch.py … grep 'AlgebraicSpace|OpenSubspace|factor.*open.*subspace'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for open-factor terms,
  `OpenSubspace` and the item id: no exact existing declaration. The previously
  landed parent module `AlgebraicSpaceEtaleOpenImage` was read: its
  `etale_open_image` asserts existence of an open image under étaleness, not
  unique factorization for any specified open and arbitrary map, nor the full
  canonical scheme-test comparison here. Its preimage convention agrees with
  this delivery. No module defines the present combined statement.

Validation: prescribed `scompile.py` compiled the file in sandbox and library
module modes with no errors or warnings. Maximum line width is 91 characters;
all variables and universes are explicitly bound.

## Second reading by Q111

A second pass with the unchanged JSON statement and the final Lean file open
checked all clauses above. This is a same-worker check: the dispatcher explicitly
prohibits starting other agents; the maintainer's independent review remains the
independent reading. The base, arbitrary spaces and morphisms, fixed open
subfunctor, containment versus equality hypotheses, uniqueness, both comparison
projections, scheme-test definitions of étaleness and surjectivity, and arbitrary
g were checked individually. The first theorem supplies both occurrences of the
open pullback and its inverse-image formula. The second theorem retains an
explicit invertible pullback projection rather than only an existential factor.
The third theorem keeps the full-image equality independent of étaleness.
No mismatch or node fault was found and no statement fields changed.
