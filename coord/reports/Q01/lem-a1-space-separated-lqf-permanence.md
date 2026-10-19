## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.space_separated_lqf_permanence`
in `Sheaf.AlgebraicGeometry.SpaceSeparatedLqfPermanence`. Its only proof is `sorry`.
No definition, axiom, statement correction, or new node is introduced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme `S` is `{S : Scheme.{u}}`. Schemes `T,B` over `S` are `(T B : Over S)`;
  `(b : B ⟶ T)` is exactly an `S`-morphism. All scheme tests use the same universe `u`
  as the existing algebraic-space definition, without an independent smaller test universe.
- `X : AlgebraicSpace S` is the dependency's full subcategory of fppf sheaves with
  representable diagonal and a representable surjective etale scheme atlas.
- The `S`-morphism `f : X → T` is a sheaf map
  `f : X.obj ⟶ (Scheme.fppfTopology.over S).yoneda.obj T`.
  A sheaf map is a natural transformation, exactly the algebraic-space morphism in the node.
  Subcanonicity supplies the actual representable fppf sheaf of `T`, with underlying
  presheaf `yoneda.obj T`; no unspecified representing map is chosen.
- `hqf` quantifies over every `V : Over S` and every natural transformation
  `a : yoneda.obj V ⟶ X.obj.obj`, assuming `IsEtale a`. This is representable etaleness
  on every scheme test; it does not assume the chart surjective, affine or quasi-compact.
  Its conclusion is `Scheme.Hom.IsLocallyQuasiFinite
  (yoneda.preimage (a ≫ f.hom)).left`. Yoneda's fully faithful preimage gives precisely
  the scheme composite `V → T`, with its structural map over `S` retained until `.left`.
- `hsep` is `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
  (pullback.diagonal f.hom)`. This is the closed-immersion condition on every scheme
  base change of the actual relative diagonal, not an absolute diagonal over `S`.
- The first conclusion is `IsAlgebraicSpace
  (Limits.pullback f ((Scheme.fppfTopology.over S).yoneda.map b))`.
  This is the chosen sheaf fibre product `X_B`, not an arbitrary object satisfying an
  existence predicate. `pullback.snd` is its actual map to the representable sheaf of `B`.
- The second conclusion applies the same chartwise quantifier to that sheaf fibre
  product and its second projection. This states local quasi-finiteness of `X_B → B`.
- The third conclusion tests the relative diagonal of the second projection by
  `IsRepresentableWith` and `IsClosedImmersion`, giving separatedness of `X_B → B`.
- The fourth conclusion quantifies over every algebraic space `O` and every sheaf
  map `j : O.obj ⟶ X_B`. Its sole additional hypothesis is
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom`, precisely the
  definition of an open subspace given by the node. It does not assume that `O` is a scheme.
- Its first conjunct quantifies over every representable etale scheme chart of `O`
  and asserts the Stacks local-quasi-finiteness predicate for its composite with
  `j` and the second projection. Its second conjunct tests the relative diagonal
  of `j.hom ≫ (pullback.snd ...).hom` by closed immersions. These are exactly the two
  requested properties of `O → B`.
- Its final conjunct quantifies over every `Z : Over S` and every isomorphism
  `e : yoneda.obj Z ≅ O.obj.obj`. The scheme map is the Yoneda preimage of
  `e.hom ≫ j.hom ≫ (pullback.snd ...).hom`. `IsSeparated` and
  `Scheme.Hom.IsLocallyQuasiFinite` on its underlying scheme morphism are precisely
  the final scheme clause. Requiring an isomorphism here expresses the conditional
  scheme-representable case, and does not add a hypothesis on the preceding clauses.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, with `Over S` and
  its over-category morphisms encoding the structural maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `AlgebraicSpace.IsRepresentableWith`,
  `AlgebraicSpace.IsEtale`; full signatures and docstrings read.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite` and its underlying `IsQuasiFiniteAtPoint`;
  full definitions and docstrings read. This includes local finite type, which the
  Mathlib `LocallyQuasiFinite` predicate alone does not include.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `Limits.pullback`, `pullback.fst`, `pullback.snd` and the universal property;
  `Mathlib.CategoryTheory.Limits.Shapes.Diagonal`: `pullback.diagonal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` and the two associated etale-cover statements;
  the dependency module is publicly imported. The fibre product is taken in sheaves,
  so its algebraic-space property is a conclusion rather than assumed structure.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the recorded dependency module
  supplying `IsSeparated`, whose definition says the scheme diagonal is closed.
- `Mathlib.CategoryTheory.Sites.SubcanonicalOver`: subcanonicity on `Over S`, so the
  canonical representable sheaf is available via `(Scheme.fppfTopology.over S).yoneda`.

The stated proof-dependency modules are imported as the stage-3 plan:
`SeparatedLqfBaseChange` (`separated_lqf_base_change`), Mathlib's `Etale` (open
immersions etale and etale composition/cancellation), and `OpenImmersion` (monomorphy).
`lem-a1-scheme-lqf-etale-source-locality` has no Lean record or Mathlib match on this
base; it is mentioned in the proof docstring but is not an import or a statement
prerequisite. No missing declaration is needed to type this delivery's statement.

Source checks: read the node's six proof steps and the Stacks source in
`literature/stacks-project/spaces-morphisms.tex`: 03KL (relative diagonal base
change), 03KQ (composition), 03XJ (local quasi-finiteness), 03XK (composition),
03XL and its 0ABM input (arbitrary base change). The docstring carries all six
steps, including the comparison of arbitrary charts via a surjective etale atlas,
monomorphy of an open inclusion, the equality-locus identification of relative
diagonal tests, and the identity-chart recovery of the scheme case.

Edge cases checked before drafting: the empty space and empty open subspace;
the whole open subspace (identity inclusion); the identity base change; arbitrary
nonreduced and non-flat base change; non-affine and non-quasi-compact scheme charts;
and every choice of a scheme representing `O`. No nonemptiness, Noetherian,
affineness, finite-presentation, quasi-compactness, or condition on `b` was added.
The open and closed conditions concern schemes obtained by every scheme base
change, so an open subspace has not been silently assumed represented by a scheme.
These checks reveal no false or disputed statement and require no correction.

Searches for existing statements and definitions:

- `msearch.py ... leanfinder "Separated locally quasi-finite algebraic spaces remain
  separated and chartwise locally quasi-finite after base change and open restriction"`:
  eight scheme-only hits including `IsSeparated.isStableUnderBaseChange` and
  `instIsStableUnderBaseChangeSchemeLocallyQuasiFinite`; none states this theorem.
- `msearch.py ... loogle '"AlgebraicSpace"'`: zero hits.
- `msearch.py ... grep 'AlgebraicSpace|algebraic space' AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch "Base change and open restriction preserve separated
  locally quasi-finite algebraic spaces"`: eight scheme/ring hits, no space theorem.
- `rg` over upstream `WeilConjectures` for the item id: no hits. The broader search
  for `IsSeparatedPresheafMap`, `IsLocallyQuasiFinite`, and chartwise properties
  finds no upstream algebraic-space permanence statement.
- `rg` over `lean/Sheaf` found `AlgebraicSpace`, `QuasiFiniteMorphism`,
  `EtaleSpaceLocallyQuasiFinite`, `SeparatedLocallyQuasiFiniteSpaceRepresentable`
  and `SpaceQCSeparatedEtaleLocal`. Their statements and relevant definitions were
  read. The first two supply the notions used here; the latter three state
  different results, not this permanence theorem. No second definition of any
  notion is introduced: chartwise quantifiers and the scheme-test diagonal
  condition are written using the existing predicates, as in those space modules.
- The proposed declaration name was searched in Mathlib, upstream
  `WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no collision.

## Second reading by Q01

This section records the author's separate clause audit; no independent reader
is claimed. The brief requires self-delivery, and the maintainer supplies the
independent review after delivery.

I reopened the node and compared each binder and conclusion against the module.
`S`, the objects over `S`, `b`, `X`, and `f` have the original types. Both original
hypotheses remain unchanged, with quantification over all representable etale
charts and all scheme tests of the relative diagonal. The conclusions retain
algebraic-space closure, both properties for `X_B → B`, both properties for every
open subspace, and both scheme properties conditional on an arbitrary representing
isomorphism. In particular the last clause does not substitute Mathlib's weaker
local-quasi-finiteness predicate. The common base `S` is not identified with `T`
or `B`; no atlas or open subspace is assumed affine or quasi-compact.

The first compile exposed an unqualified `pullback` resolving to the algebraic-space
module-pullback functor and line breaks making `.left` parse as an argument.
The correction qualifies the object construction as `Limits.pullback` and attaches
`.left` to the Yoneda preimage. These are elaboration repairs; the statement's
mathematical content was unchanged. The final node record is extracted verbatim
from the final theorem signature. No node fault or statement correction was found.
