## Worker report

The module defines the statement `AlgebraicGeometry.isAffine_of_isFinite_surjective` in
`lean/Sheaf/AlgebraicGeometry/FiniteSurjectiveAffineTarget.lean`. It uses Mathlib's
`Scheme` objects (`{X Y : Scheme.{u}}`) and a morphism `f : X ⟶ Y`. The hypothesis
that `f` is finite is the typeclass `[IsFinite f]`, exactly Mathlib's finite morphism
notion; the hypothesis that the underlying map is surjective is `[Surjective f]`;
and the source-affineness hypothesis is `[IsAffine X]`. The conclusion is
`IsAffine Y`. The proof is `sorry`, as required for stage 2.

The dependency declarations used are the Mathlib declarations `AlgebraicGeometry.IsFinite`
(`Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`, class declaration),
`AlgebraicGeometry.Surjective` (`Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean`,
class declaration), and `AlgebraicGeometry.IsAffine`
(`Mathlib/AlgebraicGeometry/AffineScheme.lean`, class declaration). The dependency node
`def-pc-scheme` is represented by Mathlib's `AlgebraicGeometry.Scheme`; the other two
DAG dependencies record the corresponding Mathlib notions above.

The statement renders every clause of the node: `f : X ⟶ Y` renders the morphism of
schemes; `[IsFinite f]` renders finiteness; `[Surjective f]` renders surjectivity on
underlying topological spaces; `[IsAffine X]` renders that `X` is affine; and
`IsAffine Y` renders that `Y` is affine. No extra hypotheses are introduced.

Edge cases checked include arbitrary universe `u`, the empty scheme and zero/empty
rings through Mathlib's unrestricted `Scheme` and `IsAffine` definitions, and arbitrary
(nonempty or empty) underlying spaces. No characteristic, finite-type, or Noetherian
assumption is present in the node and none was added.

Searches made:

* `msearch.py ... leanfinder "if a finite surjective morphism of schemes has affine source then target is affine"` returned Mathlib's `IsFinite.toIsAffineHom`, `isFinite_iff`, and related affine/surjective declarations, but no theorem with this statement (verdict: no exact match).
* `msearch.py ... loogle "IsFinite Surjective IsAffine"` returned 0 hits and reported unknown identifier `IsFinite` (verdict: unavailable/no exact match).
* `msearch.py ... grep "isAffine_of_isFinite_surjective|finite.*surjective.*affine" Mathlib/AlgebraicGeometry` returned no hits.
* Direct `rg` searches of `lean/Sheaf` and the source repository for finite/surjective/affine target statements found no existing project declaration.

The module compiled cleanly with `scompile.py`; only the expected `sorry` proof is present.

## Earlier second reading (a previous round; superseded)

I reread the target node and the three dependency records. The target's sole
hypothesis that `f` is finite is rendered by `[IsFinite f]`, its surjectivity clause
by `[Surjective f]`, and its source-affine clause by `[IsAffine X]`; the conclusion
is exactly `[IsAffine Y]` as a proposition. The binder `f : X ⟶ Y` supplies precisely
the morphism in the node, with no omitted base or separation hypotheses. The
Mathlib dependency records were opened at their class declarations and match these
notions directly. The module docstring and theorem docstring identify Limits Lemma
01ZT and the blueprint node. The server compile was clean after this signature and
docstring check; the dry run is being rerun now.

## Second reading by H1

Read the sandbox node and Lean file independently, then all three statement-dependency
nodes and their Mathlib declarations. Read the source on the server:
`literature/stacks-project/limits.tex`, lines 2815–2900, including the section preamble,
Lemma `lemma-affine` (01ZT), and its proof. The preamble imposes no standing base,
Noetherian, or separation hypotheses. Also checked the published tag at
https://stacks.math.columbia.edu/tag/01ZT.

Object/hypothesis/conclusion checklist (node order):

- Schemes X and S [def-pc-scheme]: `{X Y : Scheme.{u}}`, with Y naming S. PASS.
  Mathlib `Scheme` is a locally ringed space locally isomorphic to ring spectra
  (`Scheme.lean:42`); `Scheme.Hom` (`:74`) is a locally ringed-space morphism.
- Morphism f : X → S: `(f : X ⟶ Y)` in the category of those schemes. PASS.
- f finite [def-weil-finite-integral-morphism]: `[IsFinite f]`. PASS.
  Opened `Morphisms/Finite.lean:39`: extends `IsAffineHom f` and requires
  `(f.app U).hom.Finite` on every affine open of Y. This is exactly the dependency's
  finite clause, not its integral-only clause or a finite-fibre condition.
- f surjective on underlying points [def-weil-surjective-morphism]:
  `[Surjective f]`. PASS. Opened `Morphisms/UnderlyingMap.lean:59`:
  field `surj : Function.Surjective f`; no flatness or stalk surjectivity is required.
- X affine [def-pc-scheme]: `[IsAffine X]`. PASS. Opened `AffineScheme.lean:59`:
  the canonical map to Spec of global sections is an isomorphism, equivalently
  isomorphism to the spectrum of a commutative ring as in the node.
- Conclusion S affine: `IsAffine Y`. PASS. No extra conclusion or existential choice.
- Quantifiers: arbitrary schemes first, then their morphism, then exactly the three
  hypotheses. The binder/instance form introduces no additional assumptions. PASS.

Edge cases: no `Nonempty` or domain hypotheses; the empty scheme (Spec of the zero
ring) is included. If X is empty, surjectivity forces Y empty, consistent with the
conclusion. Nonreduced rings and every characteristic are included. No field,
Noetherian, separatedness, finite presentation, or finite-type hypothesis is added.
The shared arbitrary universe u is Mathlib's scheme category universe; any pair of
schemes can be placed in a common larger universe. No test-object universe makes a
hypothesis vacuous. There is no index set or n in the statement, so empty index sets
and n = 0 impose no omitted cases.

Independent searches (recorded in searches.jsonl):

- LeanFinder: "Affineness descends along finite surjective scheme morphisms
  (Chevalley)". Eight hits, including `IsFinite.toIsAffineHom`, `isFinite_iff`, and
  `Scheme.exists_hom_isAffine_of_isLocalAtSource`; none proves this statement.
  The first two express finiteness/affineness of a morphism; the last constructs a
  surjective affine source and does not conclude affineness of its target.
- LeanSearch: "The target of a finite surjective morphism from an affine scheme is
  affine". Service unavailable (Internal Server Error); no verdict inferred.
- msearch grep on AlgebraicGeometry for `01ZT|01YQ|IsAffine.of_surjective|`
  `isAffine.*(finite|surjective)|affine.*finite.*surjective`: 24 hits, no exact match.
  In particular closed-immersion `isAffine_surjective_of_isAffine` concludes source
  affineness and ring-map surjectivity under an affine-target context.
- Direct rg over the source `WeilConjectures/` and repository `lean/Sheaf`, using
  finite/surjective/affine phrases and the tags and alternative names: no exact match.
  Opened `IsAffineOfFiniteClosedCover.lean`: requires finitely many closed immersions
  covering a scheme, a different statement, so it is not a replacement for this node.
  Other target-affine hits concern quasi-affine blowup targets or assume an affine
  target. The proposed full theorem name has no existing declaration in those trees.

Mismatch found: H8, the original theorem docstring had only "Noetherian approximation
and the Noetherian case", omitting the nine proof steps and their dependencies.
Replaced that summary-only proof description by all nine node steps, including qcqs,
finite-presentation reduction, directed Noetherian approximation, spreading out,
descent of finiteness and surjectivity, eventual source affineness, the Noetherian
case, and the affine limit projection. The signature was retained. Updated the
node's lean.statement to the literal multiline signature, without changing its type.
No new definition nodes, dependency modules, private notions, hollow definitions,
or proved lemmas were introduced. The only theorem proof is `by sorry`. All imports
supply the notions used; universe u and every variable are explicitly bound; all
Lean lines are at most 100 characters. Both source and blueprint docstring markers
are present. No statement correction or citer revalidation is needed.

Validation: scompile.py compiled the repaired 75-line module on the server in
1.6 seconds, exit 0, with no warnings. deliver2.py --no-push printed OK: the
module compiled and the stage-2 preflight passed.
