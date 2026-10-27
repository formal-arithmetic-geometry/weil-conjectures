## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedImmersionProper` states
`AlgebraicGeometry.AlgebraicSpace.mapIsProper_of_isClosedImmersion`, with its proof
left as `sorry`. It is the assertion of Stacks 04XZ, read in
`literature/stacks-project/spaces-morphisms.tex`, lines 7940–7951. No definition,
additional theorem, or mathematical statement correction is needed.

### Hypotheses and conclusion, clause by clause

- The scheme S is `{S : Scheme.{u}}`. The explicit `universe u` follows the size
  convention; algebraic spaces, test schemes, and values have the existing
  framework's universes. No independent smaller test universe is introduced.
- The algebraic spaces over S are `{Z X : AlgebraicSpace S}`. This is the recorded
  full subcategory of fppf sheaves, with representable diagonal and a surjective
  representable etale atlas. The morphism is `(i : Z ⟶ X)`; its underlying natural
  transformation is `i.hom.hom`.
- Closed immersion is the hypothesis
  `hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`.
  The recorded definition quantifies over EVERY `T : Over S` and EVERY
  `a : yoneda.obj T ⟶ X.obj.obj`. It supplies `U : Over S`, a scheme projection
  `p : U ⟶ T`, and a genuine representing presheaf pullback square, together with
  `IsClosedImmersion p.left`. This includes representability, rather than assuming
  that the algebraic space Z itself is a scheme.
- The conclusion is the existing `MapIsProper i`, which unfolds to
  `MapIsSeparated i ∧ MapIsFiniteType i ∧ MapIsUniversallyClosed i`.
- Separatedness is `IsRepresentableWith` for scheme closed immersions on
  `pullback.diagonal i.hom.hom`, exactly the diagonal condition in the node.
- Finite type is `MapIsQuasiCompact i.hom.hom ∧
  MapIsLocally (@LocallyOfFiniteType) i`. Quasi-compactness tests compactness of
  the actual point space of each affine-scheme pullback; local finite type is
  checked on every compatible pair of representable etale scheme charts, using
  Mathlib's scheme `LocallyOfFiniteType`.
- Universal closedness quantifies over EVERY `Y' : AlgebraicSpace S` and
  `g : Y' ⟶ X` and requires
  `IsClosedMap (mapPoint (Limits.pullback.snd i.hom g.hom).hom)`.
  The topology is the recorded atlas topology `pointTopologicalSpace` and the
  fibre product is the sheaf fibre product. Thus the conclusion is intrinsic
  properness, not merely proper scheme tests or a property of one atlas.
- There are no finite-presentation, Noetherian, reducedness, flatness, or absolute
  quasi-compactness assumptions on S, Z, or X.

### Dependency declarations used

Read the statements and lean/mathlib records of every original statement
 dependency, and the signatures/docstrings of their recorded declarations:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsRepresentableWith`,
  `AlgebraicSpace.IsRepresentable` and `AlgebraicSpace.IsEtale`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-size-convention`: a metatheoretic convention with no declaration;
  rendered by explicitly bound `universe u` and the existing framework.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace` and `pointImage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, and `etale_fibreProduct_isScheme`. The first identifies
  the sheaf pullbacks used by the intrinsic properness predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsProper`, `IsSeparated`, and `UniversallyClosed`, for the
  underlying scheme convention and proof input.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, applied to the scheme projection.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsProper`, `MapIsSeparated`,
  `MapIsFiniteType`, `MapIsLocally`, and `MapIsUniversallyClosed`.
  This already-landed definition node, `def-sfb-space-morphism-properties`, is
  added to stmt_deps under the standing permission to cite landed notions.
  It supplies exactly the intrinsic properness explicitly described in the item;
  no duplicate definition or replacement of the scheme definitions is made.
- Its existing quasi-compactness and point-map ingredients are
  `AlgebraicGeometry.AlgebraicSpace.MapIsQuasiCompact` and `mapPoint` in
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`; their definitions were also read.

Proof dependencies: `lem-weil-pbc-closed-immersion-proper` is a Mathlib-status
node whose match includes `AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`
in `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`; this module is a plain proof
import. `lem-sfb-space-representable-proper-tests` has no Lean record or Mathlib
match at this delivery's base, so there is no module to import for it yet. It is
used only in the natural-language proof plan, not as an object needed to type
this statement. Its two-direction statement was read; no dependency module or
new theorem is needed for this stage-2 signature.

### Edge cases checked before writing

- Empty Z: the empty scheme pullbacks are closed immersions, the point images
  after all base changes are empty and closed; no nonemptiness binder excludes it.
- Empty X and the empty base S are allowed by the signature.
- Identity of a non-quasi-compact scheme: the identity is relatively proper;
  `MapIsQuasiCompact` is relative, so no absolute compactness is imposed.
- A closed subscheme cut out by an infinitely generated ideal remains included:
  the quotient is a finite-type algebra, without requiring finite presentation.
- Nonreduced source/target and nonflat closed immersions are included. For
  example `Spec(k) -> Spec(k[epsilon]/(epsilon^2))` is not excluded.
- Scheme-representable spaces recover the usual properness assertion; general
  algebraic spaces retain their original sheaves, point sets and atlases.

### Searches actually run

All remote searches used `msearch.py Q35 lem-sfb-space-closed-subspace-proper`.

- leanfinder: `Every closed immersion of algebraic spaces is proper`.
  Eight hits, all scheme declarations, including
  `instUniversallyClosedOfIsClosedImmersion` and `IsFinite.instOfIsClosedImmersion`;
  no existing algebraic-space theorem.
- loogle: `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsProper`.
  Two scheme hits in `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`:
  `IsClosedImmersion.iff_isProper_and_mono` and
  `IsClosedImmersion.eq_proper_inf_monomorphisms`; neither is this space theorem.
- grep: `algebraic.?space|IsClosedImmersion.*IsProper`, directory
  `AlgebraicGeometry`: five scheme-result lines in ZariskisMainTheorem.
- leansearch: `A closed immersion of algebraic spaces is a proper morphism`.
  Eight scheme-result hits, no matching algebraic-space statement.
- Local rg on `lean/WeilConjectures` for closed/proper combinations and on
  `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*.lean` for the same concepts found
  scheme results, references in later proof docstrings, and existing notions;
  no theorem with this hypothesis and intrinsic conclusion. In particular the
  existing ClosedCoherentModules/ClosedStructureFinitePresentation modules use
  precisely the same scheme-test closed-immersion hypothesis.
- `grep -rn lem-sfb-space-closed-subspace-proper lean/WeilConjectures` had no hits.
- rg for `mapIsProper_of_isClosedImmersion|ClosedImmersionProper` over both Lean
  roots and `dag/lean_names_upstream.json` had no hits before writing.
- The recorded module `AlgebraicSpaceMorphismProperties` was opened and reused;
  a second properness definition is not introduced.

### Validation

The delivered file compiled with scompile.py against the published server build,
separately in sandbox and library module modes (1.4 seconds each), with no errors
or unexpected warnings. The only postponed proof is the item's named theorem.
The node copy changes only lean and adds the already-landed properness definition
to stmt_deps. No source statement or proof plan is changed.

## Second reading by Q35

Author self-check under the dispatcher's direct-delivery rule; independent review
is left to the maintainer, and no other agent was started. Reopened the item,
the module, and the four intrinsic property definitions. Matched S, Z, X and i
with the explicit binders, and the representable scheme-test closed immersion
with hi. Unfolding MapIsProper supplies separatedness, relative quasi-compactness,
local finite type on compatible etale charts, and universal closedness for every
space base change. No scheme-test criterion has been substituted for the intrinsic
conclusion. The universe follows the existing framework without adding an equality
or excluding empty objects. Checked that all theorem proof text is postponed,
that the docstring contains both DAG proof steps, and that the newly cited notion
is already landed. No mismatch or statement correction was found.
