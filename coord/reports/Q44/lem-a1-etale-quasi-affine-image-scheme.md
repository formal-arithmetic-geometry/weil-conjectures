## Worker report

This repairs immutable delivery `1fba9ce85b90` for
`lem-a1-etale-quasi-affine-image-scheme`. The saved packet first passed the required
`deliver2.py --no-push` (commit `c581189121`); that mechanical success did not resolve
the mathematical defects in the return. I retained its module and node and repaired
them, rather than treating successful compilation as statement review.

The module `Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme` states
`AlgebraicGeometry.AlgebraicSpace.etale_quasiAffine_image_scheme`, with one postponed
theorem and two explicit, proposition-valued helpers. Its source is Stacks 03XW,
`literature/stacks-project/spaces-morphisms.tex`, lemma-neighbourhood-scheme,
lines 10469–10586; the point-class convention is Properties of Spaces 03BU,
`spaces-properties.tex`, definition-points and the equivalence relation immediately
before it. I read both source passages. The mathematical node already states these
sources correctly: only its `lean` record changes, not its statement, proof, or DAG
edges. Comparison with the current shared node found no non-`lean` differences.

Each hypothesis and conclusion is rendered as follows:

* `S : Scheme.{u}` is the base scheme. `T T' : Over S` with
  `[IsAffine T.left] [IsAffine T'.left]` are precisely the affine schemes over it.
* `a : T' ⟶ T` with `[Etale a.left]` is the affine étale base map.
* `X : AlgebraicSpace S` and `f : X.obj.obj ⟶ yoneda.obj T` give the algebraic
  space and its morphism to `T`; morphisms are natural transformations as in the
  recorded algebraic-space definition.
* `hlocal` tests every `U : Over S` and every `g : yoneda.obj U ⟶ X.obj.obj`
  with `AlgebraicSpace.IsEtale g`. For each composite scheme morphism `q : U ⟶ T`,
  its equality `yoneda.map q = g ≫ f` implies
  `Scheme.Hom.IsLocallyQuasiFinite q.left`. Full faithfulness of Yoneda supplies
  this `q`, so the extra quantified presentation of the composite loses no case.
* `hdiag` is `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)`
  applied to `Limits.pullback.diagonal f`: exactly the closed-immersion property
  after every scheme base change. The duplicate `spaceDiagonal` is removed;
  Mathlib's chosen diagonal is used directly.
* `V' : Over S`, `v : yoneda.obj V' ⟶ X.obj.obj`, and `b : V' ⟶ T'` give the
  represented open's two projections. `hcomm : v ≫ f = yoneda.map b ≫ yoneda.map a`
  is precisely their compatibility over `T`.
* Crucially, `hvopen` asserts the representable open-immersion property of the
  canonical map `Limits.pullback.lift v (yoneda.map b) hcomm` into the actual
  presheaf fibre product `X ×_T T'`. This is the previously missing hypothesis
  that `V'` is an open subspace of that fibre product. It is independent of the
  following quasi-affine factorization.
* `hvquasi` supplies `Y : Over S`, `j : V' ⟶ Y`, `c : Y ⟶ T'`, with `j ≫ c = b`,
  `IsOpenImmersion j.left`, `QuasiCompact j.left`, and `IsAffineHom c.left`.
  Thus the given map `V' → T'` factors as exactly the quasi-compact open immersion
  into a scheme affine over `T'` specified by the node.
* The conclusion gives `W : Over S` and its inclusion `w : yoneda.obj W ⟶ X.obj.obj`:
  this is representability by a scheme. `CompactSpace W.left` is quasi-compactness
  of that scheme's underlying space, equivalently that every open cover has a
  finite subcover. `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) w`
  says that it is an open subspace of `X`. There is no `IsAffine W.left` clause.
* For every field-spectrum `U` and map `g : h_U → X`, the final equivalence
  `FieldPointImage U g V' v ↔ FieldPointImage U g W w` identifies the image of
  `|V'|` with the underlying point set of `W`. `IsFieldSpectrum U` means that
  `U.left` is isomorphic to `Spec K` for some field in universe `u`.
  `FieldPointImage` gives a field-spectrum refinement `E → U` and a lift `E → V`
  with equality of the composites to `X`. For field-spectrum `U`, its refinement
  is a field extension contravariantly. This is exactly membership in the image
  of point classes after a common field extension; no algebraic closure or
  restriction to rational points is imposed. Both helper docstrings now contain
  source and blueprint references. Their data are explicit existential formulas.

The signature uses the recorded dependency declarations:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `AlgebraicSpace.IsEtale`.
* `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` (including finite type,
  unlike the weaker Mathlib locally-quasi-finite predicate).
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  its projections and `Limits.pullback.lift`; and
  `Mathlib.CategoryTheory.Limits.Shapes.Diagonal`: `Limits.pullback.diagonal`.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.

I read their full definitions/docstrings. These have the exact scheme-test meanings
used above. The module also imports the recorded, stated proof dependencies using
ordinary, non-public imports; their names and uses appear in the theorem docstring.
`lem-a1-space-etale-open-image` has no recorded Lean module on the current base,
so its future proof import is the sole omission. No new declaration for that
proof-only prerequisite is needed to type this statement. The docstring now gives
all eleven actual node proof steps, with their named inputs: construction of the
open image; bounded-degree strong induction including zero; the affine diagonal
complement; subtraction of one from fibre degree; degree one; the two-projection
induction diagram; saturation and gluing; quasi-affineness; the correct open base
`B` (which need not be affine); sheaf descent datum; and effective fpqc descent.
It no longer substitutes a short summary or a pointer to JSON for those steps.

Edge cases and the two returned counterexamples were checked:

* Without `hvopen`, take `a = id`, `T = T' = X = Spec k[t]`, `f = id`, and let
  `V' = Spec k` be the closed origin. Its map to `T'` is affine, so it admits the
  old quasi-affine factorization, but its image is not open. The repaired
  hypothesis rejects this example because its canonical map to the base change
  is a closed point, not an open immersion.
* For the erroneous affine conclusion, take `a = id` on `T = Spec k[x,y]`,
  `X = V' = T \ {(x,y)}` with its open inclusion into `T`. This is a separated,
  locally quasi-finite, quasi-compact quasi-affine scheme over `T`, satisfying
  all the node's hypotheses. Its image is itself, the non-affine punctured plane.
  The repaired conclusion requires quasi-compact schemehood and openness only.
* `V' = ∅` and `T' = ∅` allow the empty image scheme; neither a nonempty source
  nor a positive fibre-degree bound is required. Identity base change and a
  non-surjective affine étale base map are allowed. The image base `B` in the
  proof is never assumed affine. Arbitrary fields and their extensions in the
  scheme universe are included. No Noetherian, characteristic, or finite-
  presentation assumption on `X` is added.

Search record (the saved packet's searches were retained; the diagonal search and
helper-name checks were repeated during repair):

* Saved `msearch.py ... leanfinder "scheme image of a quasi-affine open under an
  affine etale map from a separated locally quasi-finite algebraic space"`:
  eight generic scheme/quasi-affine hits, no exact statement.
* Saved `msearch.py ... loogle "AlgebraicSpace, IsOpenImmersion, IsAffineHom,
  IsLocallyQuasiFinite"`: no hits; unknown identifier `AlgebraicSpace`.
* Saved `msearch.py ... grep "AlgebraicSpace.*quasi-affine|quasi-affine.*image"
  Mathlib/AlgebraicGeometry`: no hits.
* Repair `msearch.py ... loogle "CategoryTheory.Limits.pullback.diagonal"`:
  twelve hits, including the exact existing diagonal in
  `Mathlib.CategoryTheory.Limits.Shapes.Diagonal`; reused it.
* Repair `msearch.py ... grep "spaceDiagonal|FieldPointImage|IsFieldSpectrum"
  AlgebraicGeometry`: zero hits. `rg` for `FieldPointImage|IsFieldSpectrum` in
  project `lean/Sheaf` and upstream `WeilConjectures/`: zero hits. `rg` for the
  theorem name/module and the node id likewise found no existing theorem.
* The saved upstream/project text searches found no exact lemma, only generic
  quasi-affine material. A fresh LeanFinder query for the full image statement
  returned eight generic locally-quasi-finite/quasi-affine scheme hits during
  repair; none states this algebraic-space image lemma.

No node statement was corrected and no definition/dependency node was added.
No unresolved `STATEMENT-DISPUTED` remains; the defects were in the old Lean
rendering and have been repaired to match the unchanged, source-correct node.

## Second reading by Q44

I reopened the unchanged node, the Stacks 03XW source, and the final module for a
separate self-check pass. The dispatcher explicitly forbids starting another
agent, so this section records my self-check, not a claimed independent agent
review. The maintainer's independent review remains separate.

The affine base objects and étaleness match the first source assumption; `hlocal`
and the existing diagonal give the second; `hvopen` now gives the third on the
canonical map into the fibre product; and `hvquasi` gives the fourth for the same
map `b`. Previously the quasi-affine open immersion into `Y` had been conflated
with the missing inclusion into `X ×_T T'`; these are now distinct hypotheses.
The conclusion has exactly schemehood (`W : Over S`), quasi-compactness
(`CompactSpace`), openness (scheme-base-change open immersions), and the specified
field-point image equality. The extra affine conclusion was removed, with the
punctured-plane example checked above. The duplicate diagonal helper was deleted
from both the module and `lean.declarations`; the theorem now uses Mathlib's
canonical diagonal. I checked helper source/blueprint docstrings, all eleven
proof steps, proof-only imports, the signature copied into `lean.statement`,
explicit universe/variable binders, and the 100-column limit.
