## Worker report

The module states `AlgebraicGeometry.isAffine_of_isThickening`: for schemes `X X'`, a morphism `i : X ⟶ X'`, a thickening hypothesis `IsThickening i`, and an affine instance on `X`, the target `X'` is affine. The binder `[IsAffine X]` renders the node's hypothesis that `X` is affine; `hi : IsThickening i` renders that `i` is a thickening; the conclusion is `IsAffine X'`. The proof is `sorry` as required.

Dependencies used: `Sheaf.AlgebraicGeometry.Thickening`, declaration `AlgebraicGeometry.IsThickening`; Mathlib `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.IsAffine` from `Mathlib.AlgebraicGeometry.AffineScheme`; closed immersion and surjectivity are included by the dependency definition.

Edge cases checked: no finite-order assumption is imposed; arbitrary universe `u` is used for both schemes; affine source and target may be empty or zero schemes; the morphism is arbitrary subject only to the thickening predicate.

Searches made: existing project and source grep for `IsThickening`/the theorem name (only the dependency definition and no affine-target theorem); Mathlib grep/LeanFinder/Loogle searches recorded in the node found no theorem that a surjective closed immersion from an affine scheme has affine target. Thus no existing declaration matches.

## Earlier second reading (a previous round; superseded)

The node says `i:X→X'` is a thickening and `X` affine, concluding `X'` affine. The Lean theorem has exactly these objects, hypotheses, and conclusion: `i`, `hi : IsThickening i`, `[IsAffine X]`, and `IsAffine X'`. It does not add a finite-order or separation hypothesis and preserves the arbitrary scheme universe.

## Second reading by V1

Independent reading of the node copy and `ThickeningAffineScheme.lean`, checked against
Stacks More on Morphisms, Definition 04EX (`definition-thickening`) and Lemma 06AD
(`lemma-thickening-affine-scheme`). The repository's literature checkout is absent;
I read the local Stacks TeX copies `/home/ubuntu/c1-stacks-review/more-morphisms.tex`
(lines 30–75 and 157–175) and `/home/ubuntu/c1-stacks-review/limits.tex`
(lines 2875–2893). The section introduces arbitrary schemes, with no ambient base,
Noetherian assumption or finite-order assumption. The finite-order proof is explicitly
an alternative, restricted proof; the first proof invokes Limits 05YU.

Objects, hypotheses and conclusion, matched individually:

- Schemes X and X': `{X X' : Scheme.{u}}`. Exact; the recorded dependency
  `def-pc-scheme` supplies Mathlib `Scheme`. I opened `Scheme.lean`: its locally
  ringed space with affine neighbourhoods is the source's scheme notion.
- Morphism i from X to X': `(i : X ⟶ X')`. Exact; this is the recorded
  `Scheme.Hom`, with the orientation of the source closed subscheme inclusion.
- i is a thickening: `(hi : IsThickening i)`. Exact. I read dependency node
  `def-sbc-first-order-thickening` and its module `Sheaf.AlgebraicGeometry.Thickening`.
  Despite that node's name and main recorded declaration `IsFirstOrderThickening`,
  its recorded declarations also include `IsThickening`, which is precisely
  `IsClosedImmersion i ∧ Surjective i`, not a square-zero or finite-order predicate.
- Closed immersion clause: the first conjunct of `hi`. Exact. I read node
  `def-weil-closed-immersion` and Mathlib `Morphisms/ClosedImmersion.lean:45`:
  `IsClosedImmersion` is a closed embedding with surjective stalk maps, the usual
  closed subscheme condition. No extra closed-immersion hypothesis is needed.
- Surjectivity on underlying spaces: the second conjunct of `hi`. Exact.
  Mathlib `Morphisms/UnderlyingMap.lean:59` defines `Surjective` by
  `Function.Surjective f`; combined with a closed embedding, this is equality of
  underlying spaces in Definition 04EX. It is not surjectivity on global sections.
- X is affine: `[IsAffine X]`. Exact. Mathlib `AffineScheme.lean:59` makes the
  canonical map X to Spec of its global sections an isomorphism; `Scheme.isoSpec`
  gives the corresponding spectrum isomorphism. This is the affine clause of
  `def-pc-scheme`, not an extra hypothesis on the ambient scheme.
- X' is affine: `IsAffine X'`. Exact, the entire conclusion of 06AD. The order
  is arbitrary X, X', and i, with thickening and source affineness hypotheses,
  followed by target affineness. No conclusion or hypothesis is added or dropped.

Edge cases: empty schemes are allowed; surjectivity forces an empty target when
X is empty. The zero ring spectrum is included by `IsAffine`, with no Nontrivial
instance. There is no index set, integer n, characteristic or coefficient ring
binder to restrict. In particular n = 0, first-order, finite-order and arbitrary
non-finite-order thickenings are all covered when they satisfy `IsThickening`.
Universe u is explicitly bound and arbitrary; using the common scheme category
universe is the dependency's convention, with no independent test-object universe
that could make a hypothesis vacuous. All variables in the signature are bound.

Independent searches (via `/home/ubuntu/weil-launcher/msearch.py`):

- LeanSearch: "If a closed subscheme is affine and has all the points of the
  ambient scheme, the ambient scheme is affine" returned UNAVAILABLE (Internal
  Server Error). This is an unavailable search, not a no-match verdict.
- Loogle: `AlgebraicGeometry.IsAffine, AlgebraicGeometry.IsClosedImmersion`
  returned five hits. I inspected `isAffine_surjective_of_isAffine` in the pinned
  Mathlib: it assumes affine target and concludes affine source and surjectivity
  on global sections, the opposite direction. The other hits concern construction
  of closed immersions, isomorphisms, and a diagonal restriction; none is this node.
- LeanFinder: "affineness is invariant under a nil immersion or a reduction of
  schemes" returned eight hits concerning affine morphisms and formal
  unramifiedness; none states target affineness under a thickening.
- Grep: independently searched Mathlib AlgebraicGeometry, the project's
  `lean/Sheaf`, and all `WeilConjectures` using `affine.*thicken`, `thicken.*affine`,
  `isAffine_of.*(surject|reduc|nil)` and the declaration name. I opened upstream
  `LocallyRingedSpace.isIso_toΓSpec_dualNumbers`, which covers the particular
  dual-number construction only. I also opened the project's
  `isAffine_of_isFinite_surjective`, which assumes a finite morphism and is a
  different statement. Neither is the exact arbitrary-thickening statement.
  The declaration name and `IsThickening` have no match in `dag/lean_names_upstream.json`.

No semantic mismatch found. No new definition node, dependency module or statement
correction is needed. No Lean or node change made: the signature in `lean.statement`
is verbatim the file's signature. The only theorem has proof `by sorry`; there are
no new definitions, local instances, private copies or file-local notation.
The module and declaration docstrings name 06AD and the blueprint id. The proof
paragraph carries both node steps: obtain surjectivity and universal closedness
from the thickening closed immersion, then apply 05YU to obtain target affineness.
Both imports serve the stated signature. Compilation and delivery preflight are
run on this unchanged module as part of this second reading.
