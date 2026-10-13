## What changed

Replaced the proof of AlgebraicGeometry.affine_truncation_kernel_flat without changing
its signature or visibility. Added the proved private helper
AlgebraicGeometry.image_flat_finitePresentation in the item's module.
Added Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact, which states the missing
principal-open tensor-exactness step, and its DAG node
lem-sc-affine-open-localized-tensor-exact. Updated the parent's proof, proof_deps and
proof_origin to match the actual Lean argument.

The proof applies the existing Module.Flat.opcycles_of_exactAt at r - 1 instead of
at r. Tensor exactness at r - 2 gives flatness of these opcycles. Tensor with the
unit gives ordinary exactness at r - 1; the quotient description of opcycles and
the first isomorphism theorem identify them with the differential image. The image
has a finite free presentation because its relations are the range of the preceding
finite module. Exact localization preserves images; categorical image/range isos
and Shrink.linearEquiv give the precise LocalizedModule.Away conclusion.

Added proof imports of AffineOpenLocalizedTensorExact, ModuleCat.Images,
Limits.Preserves.Shapes.Images and LocalProperties.Projective. Existing public
imports and the FlatOpcyclesTorCriterion proof import remain. There are no interface
changes, forced adaptations, new definitions, arbitrary witness choices or changes
to Challenge.lean.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.affine_truncation_kernel_flat
(lem-sc-affine-truncation-kernel-flat). No sorry remains in the item's module.
The private algebraic helper is fully proved.

Added one hole: AlgebraicGeometry.affine_open_localized_tensor_exact in
Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact
(lem-sc-affine-open-localized-tensor-exact), with whole proof `:= by sorry`.
This is precisely the geometric localization/tensor-exactness step; it says nothing
about flatness or finite presentation of an image. Both output properties and their
transport are proved in Lean in the original module. Thus this delivery is a
one-for-one decomposition, with net zero holes removed, not an unconditional
axiom-free proof of the original theorem. The existing opcycles criterion is used
as an authorized dependency; its downstream proof obligations remain.

Both sandbox modules compiled together in import order without errors or warnings.
The original theorem's signature and visibility were checked mechanically against
the repository copy. Second-reader scratch copies were used for explicit #print axioms checks and removed.

## No longer needed

No imports, DAG nodes or library modules are pruned. The affine Tor-amplitude
criterion remains a planned dependency of the new geometric step and remains a
public import of the original module. The flat-opcycles criterion is used directly.

The plan's flat-kernel argument using Tag 00HM is unnecessary: applying the
opcycles criterion one degree earlier proves image flatness directly. There was no
separate node or import for that argument to remove. No unit statement or realized
step is bypassed; the unit's realized arrays are empty in the repository record.

## Where the brief, the DAG or earlier work was wrong

The DAG's source field names Tag 08ED, but the truncation-image paragraph is in
Tag 08EG, as the Lean docstring already says. The online primary sources were
checked: https://stacks.math.columbia.edu/tag/08EG,
https://stacks.math.columbia.edu/tag/08E9,
https://stacks.math.columbia.edu/tag/09U8 and
https://stacks.math.columbia.edu/tag/0653. The parent source field is left unchanged
because this delivery owns only its proof fields. The new node records the correct
source URLs. The source text is absent from this clone's literature directory.

The DAG did not provide a Lean statement for restriction to a principal open
followed by ordinary tensor computation. The existing affine criterion applies to
Spec(A_f), not directly to the derived restriction to U, so it does not by itself
close that step. AffineUniversalTensorExact has a different hypothesis, universal
scheme pullback exactness; it is not the needed statement. The new lemma isolates
this comparison instead of duplicating the original theorem.

The new statement was checked on the zero ring, f = 0, empty U, N = 0 and P = 0:
the relevant localized/tensor complexes are zero when appropriate. No a <= b
hypothesis was added; widening to max(a,b) preserves the lower-bound assertion.
LeanSearch was unavailable (Internal Server Error); LeanFinder returned only
ordinary derived t-structure vanishing lemmas, Loogle had no range/finiteness match,
and Mathlib/source-library grep found exact localization but no sheaf Tor-amplitude
comparison of this form. These searches are recorded in the new node.

## New nodes

lem-sc-affine-open-localized-tensor-exact, in
 dag/nodes/sec-picard-framework/lem-sc-affine-open-localized-tensor-exact.json,
states universal tensor exactness of the canonical localized complex in all degrees
below a. It is strictly the first geometric step of the parent's argument. Its
proof in words combines open-immersion Tor-amplitude preservation, the existing
affine derived pullback/tensor comparison, the affine Tor-amplitude criterion,
and bounded-above flat K-flatness. The second reading replaces the extension-by-zero
wording with ordinary direct image and the cited tensor/restriction comparison. It has one public theorem in its own new module,
the complete source/proof docstring, three kinds of recorded Mathlib search and
all required creation, blueprint and Lean fields. There are no change records
because no existing statement, definition or public import changes.

## Second reading by V1

1. Interfaces: diffed the complete existing module against the repository copy and
   mechanically compared the text from `theorem affine_truncation_kernel_flat` to
   `:= by`; it is byte-identical, including universes, all hypotheses, conclusion
   and visibility. Only its proof, proof docstring, proof imports and a private
   proved helper changed. The parent JSON changes exactly proof, proof_deps and
   proof_origin. There are no changed definitions or undeclared interface changes.
   Verdict: pass.

2. Proof: compiled both delivered modules in import order with lcompile.py;
   no errors or warnings. Explicit #print axioms in removed scratch copies reports
   only propext, Classical.choice and Quot.sound for image_flat_finitePresentation;
   the original theorem and the new open theorem additionally use sorryAx.
   The only delivered sorry is the entire named affine_open_localized_tensor_exact
   theorem. No forbidden declarations, hidden holes, definitions or arbitrary
   data choices occur. Checked r-2 < a and r-1 < a, the exact range/kernel identity,
   the direction of the quotient/image equivalences, the finite-generated-kernel
   presentation, and exact localization's image comparison. Verdict: pass as a
   one-for-one decomposition, not an unconditional closed target.

3. Split statement: read Stacks Tags 08EG (lower image paragraph), 09U8
   (pullback preserves amplitude), 08E9 (affine comparison), and 0653 (flat
   cokernel argument). The new theorem uses exactly the parent's geometric data,
   omits r and flatness/finite-presentation conclusions, and provides the tensor
   exactness needed by the separately proved algebraic argument. It is strictly
   a geometric part, not the target under another name. For each sheaf H on D(f),
   j_*H restricts to H by its sections formula; restrict the hypothesis for j_*H
   and use the existing derivedTensor_openRestriction_iso. No exactness of j_*
   is assumed. Localization/tilde comparison and bounded-flat K-flatness then
   give the concrete tensor complex. Checked zero A, f=0, U empty, P=0, N=0,
   f a unit, and a>b (widen to max(a,b)); no missing nonemptiness or ordered-interval
   assumption. New Lean theorem matches its node and has a complete source/proof
   docstring. Repeated searches with the distinct LeanFinder query
   "Exactness of module tensor complex from sheaf Tor amplitude on a principal
   open subscheme", Loogle `ModuleCat, HomologicalComplex.ExactAt`, launcher grep
   `TorAmplitude|torAmplitude|localizedModuleFunctor`, and rg in both Lean roots
   and the upstream source checkout. Results concern ordinary tensor/localization
   exactness, not this geometric comparison. Read AffineUniversalTensorExact:
   its universal pullback hypothesis differs and cannot directly replace this
   theorem. Verdict: pass; the substantial geometric formalization remains open.

4. Route/pruning: the proof follows the parent's principal-open reduction and
   uses Module.Flat.opcycles_of_exactAt at r-1, saving the proposed extra flat-kernel
   step. Its finite presentation proof needs no coherence or Noetherian hypothesis.
   The old affine amplitude dependency moves to the new geometric step and is
   still transitively used; the old opcycles dependency remains used directly.
   No old proof dependency is discarded from the argument and no module is pruned.
   Read sk-thm-picard-duality's realized record: statement [] and steps [[]];
   no realized node or prescribed unit step is bypassed. Existing public imports
   remain unchanged. Narrowed the new module's public imports to the vanishing
   predicate and Mathlib tilde module needed by its signature; its three planned
   proof dependencies are plain imports. Verdict: pass.

5. DAG: parent steps match the actual Lean algebraic proof and canonical
   localization equivalence. New node's proof_deps is precisely the union of its
   cited steps; its creation, source, statement/Lean record, chapter, unit and
   blueprint ancestry were read and checked. Repaired its first step, previously
   incorrectly elementary with no citation, to cite
   lem-pc-affine-derived-pullback-tensor-tilde and explicitly explain the sheaf
   testing argument. Set LeanSearch's failed service verdict to unavailable.
   No existing node fields outside the stage-3 owned proof fields changed.
   Verdict: pass.

Second reading changed: new-module import visibility and minimal signature
imports; geometric docstring and DAG step-one justification/citation; unavailable
search verdict; this report. No Lean proof or theorem signature needed repair.
Holes closed: AlgebraicGeometry.affine_truncation_kernel_flat (1 of 1 original).
Holes added: AlgebraicGeometry.affine_open_localized_tensor_exact (1 split off).
Net holes removed: zero; this is a decomposition with the algebraic argument proved.
