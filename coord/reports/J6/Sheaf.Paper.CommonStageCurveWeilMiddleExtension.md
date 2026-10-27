## What changed

Completed the proof body of `WeilConjectures.qbarAffineWeilShift_forget` in
`Sheaf.Paper.CommonStageCurveWeilMiddleExtension`, keeping its statement and all
existing definitions unchanged. The proof identifies the unshifted arithmetic
trivial-character line with the coefficient unit, commutes geometric pullback
with shift using `fieldCommonPullShift`, transports the unit using the common-stage
unit clause of `derivedPullbackTensorIso`, and applies the shifted-unit tensor
comparison. The componentwise tensor comparison has a proved naturality square;
whiskering it by the Weil forgetful functor gives exactly the original conclusion.

Added private proof imports of `Sheaf.Paper.FourierTrivialCharacterUnit`,
`Sheaf.Paper.CommonStageShiftedUnitTensor`, and
`Sheaf.Paper.FieldWeilShriekShiftData`. Added the first two modules as separate
supporting items, with source references and complete proof descriptions.
Updated the existing node's proof, dependencies and proof origin accordingly.
No existing signature, definition, public import, or unit route changes.

## Proved and sorry left

The item originally had one hole. Its proof body is now complete:
`WeilConjectures.qbarAffineWeilShift_forget` (node `def-wf-middle-extension`).
There are zero holes left in the item module. This is a decomposition, not a
closed proof of the dependency closure: two strictly smaller supporting holes
are added, so this delivery has one hole closed and two holes added (net -1).

The complete list of added holes is:

- `WeilConjectures.fourierTrivialCharacter_unit`, in
  `Sheaf.Paper.FourierTrivialCharacterUnit`, node
  `lem-wf-fourier-trivial-character-unit`: an unshifted object isomorphism, before
  geometric pullback, tensor action, or Weil descent.
- `WeilConjectures.commonStageShiftedUnit_tensor`, in
  `Sheaf.Paper.CommonStageShiftedUnitTensor`, node
  `lem-wf-common-stage-shifted-unit-tensor`: the geometric shifted-unit tensor
  comparison, independent of Artin--Schreier sheaves and Weil structures.

Both proofs are exactly `by sorry`; neither is the original theorem with renamed
or repackaged hypotheses. All glue between them and the original conclusion is
proved Lean. No data definition is added or changed.

## No longer needed

None. No original import, declaration, module, node, or unit proof step is
withdrawn. The existing ordinary Weil-heart adjunction and arithmetic-geometry
proofs are retained. The new proof uses each of its three additional imports.

The search found the existing trivial-character etale isomorphism and the
prime-character decomposition in `FourierArtinSchreierProperties`. The latter
uses a finite-field Over structure rather than the canonical characteristic-p
structure used by `fourierAdicArtinSchreier`; its chosen prime-character object
is not the same expression. The new object-comparison item isolates the required
completed common-stage identification rather than importing that entire
character-decomposition theorem into this proof. No dependency of that existing
module is pruned by this observation.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The previous node correctly left the affine
comparison open; its proof text now records the actual assembly instead.
The existing tensor/pullback package supplies the unshifted unit comparison,
but does not itself state the signed shifted-unit natural isomorphism for the
actual common-stage tensor. The unshifted character-unit comparison likewise
requires matching completed realization with the reconstructed coefficient unit.
Those are the two remaining, separately documented mathematical steps.

The new statements were checked on the empty scheme, characteristic two with
coefficient prime different from two, zero objects, shift zero, negative shifts,
and ramified finite coefficient extensions. The signed tensor map uses
`(-1)^(a*r)` on a tensor in degree `a`, so both positive and negative shifts obey
the cohomological convention. Neither statement asserts preservation of arbitrary
Weil structures; that extra structure is unnecessary for a forgetful comparison.

## New nodes

`lem-wf-fourier-trivial-character-unit` records the trivial summand clause of
current `lem-fd-as-characters`, realized in the fixed integral completion and
then rationalized into the actual common-stage category. Its proof description
uses injectivity of the coefficient embedding, the existing etale constant
character isomorphism, completed scalar extension of the regular module,
reconstruction from coherent reductions, and the unit scalar-stage comparison.
Bhatt--Scholze Lemma 6.8.2(1) and Proposition 6.8.4(1) explain the completed unit
and its coherent reductions; the construction is applicable to the actual
Noetherian arithmetic affine line.

`lem-wf-common-stage-shifted-unit-tensor` records the signed total tensor/shift
comparison with the coefficient unit, for every integer shift. Stacks Project
`more-algebra.tex`, `section-sign-rules` and `item-shift-tensor`, give the signed
comparison. Derived coefficient reduction and inverse limit (Tags 06YY and
0941), rationalization, and the specified scalar conjugations give its
common-stage form and naturality for every represented common-stage arrow.
There are no definition changes or change records.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
