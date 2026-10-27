## What changed

Proved the unchanged `orderedAffineTranspose_projection` from a genuine dimension induction,
the directly computed zero case, a single-successor coefficient lemma, line normalization,
and comparison naturality. Derived transpose naturality from comparison naturality and the
existing exceptional-counit naturality theorem. The block equation follows by mapping that
equality through the outer compact-support functor and composing its counit. Both identity
block cases are covered by the same calculation.

Moved the original concrete definition bodies to `Sheaf.Paper.OrderedAffineTransposeData`,
publicly reexported by the original module. This prevents cycles for the three independent
proof obligations. Existing signatures, visibility and map bodies are preserved.
The large map definitions gain `@[irreducible]` after a profiled data compile showed repeated expensive type
checking and linting; explicit unfolding handles the proof calculations. The five
existing trace-data declaration attachments move to that module; a new definition node owns
the other constructions. No data are chosen from an existence-only theorem.

The only downstream consumer is `Sheaf.Paper.AffineSpaceTraceFactorization`, held by D3.
It needs no edit: all original declarations are public through the original import.
The source-library tree and all target statements are unchanged.

Change record: `coord/changes/S3-ordered-affine-transpose-data.md`.

## Proved and sorry left

Closed the one original textual hole:
`AlgebraicGeometry.ProEtale.OrderedAffineTranspose.orderedAffineTranspose_projection`
(node `lem-pur-ordered-affine-transpose-projection`). Its proof is complete Lean assembly,
with zero holes in the item module. The zero calculations explicitly normalize
identity-stage casts using `with_unfolding_all`; the recursive calculation keeps its
comparison and origins irreducible locally. Private helpers prove zero transpose, zero integration,
counit naturality, transpose naturality and the arbitrary-block law.

Added three named public theorem holes, each with a source, proof in words and its own module:

- `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.orderedAffineComparison_natural`
  (`lem-pur-ordered-affine-comparison-natural`): naturality of the recursive comparison,
  for all retained ordinary origins.
- `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.orderedAffineTranspose_successor`
  (`lem-pur-ordered-affine-transpose-successor`): one successor dimension, assuming the
  coefficient formula in the preceding dimension over all finite-type bases.
- `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.orderedAffineTranspose_line`
  (`lem-pur-ordered-affine-line-transpose-normalization`): only coefficient-unit normalization
  at dimension one.

This is a decomposition: one upper hole closed and three lower holes added, net -2.
It is not a sorry-free proof of the mathematical result. Each lower statement is strictly
a step: no child asserts the full conjunction or the all-dimensional coefficient theorem.
The data module contains zero `sorry`; no definition or private theorem contains a hole.
The item proof compiled in 37.4 seconds; its sole style warning was then corrected.
The final clean `lcompile.py --all` passed all five delivered modules and the unchanged
downstream `Sheaf.Paper.AffineSpaceTraceFactorization`; the verification-only copy of
that consumer was then removed from the packet. No consumer adaptation is delivered.

## No longer needed

Removed the following private imports from the item module, and from the extracted data
module, because the written assembly uses the three child declarations and the existing
counit naturality directly. Their mathematical obligations remain in the successor and
normalization children's DAG plans; none is claimed globally unnecessary or withdrawn:

- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.Paper.FiniteCoefficientTensorCtf`
- `Sheaf.Paper.SfPreservationClass`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.Paper.FiniteCompactSupportConstructibility`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.Paper.ProjectionFormulaCoefficientCoherence`
- `Sheaf.SixFunctors.CompositionProjectionMate`
- `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly`
- `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.CategoryTheory.Adjunction.Basic`

All original public imports stay. No existing mathematical node or module is withdrawn;
no source-library declaration is removed. The original generic-tool approvals are retained,
since the children's proof plans still need those tools.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The existing dependency declarations are meaningful, but none
states naturality for the recursively defined affine comparison or the fully transported
single-successor formula in these literal coordinates. These are explicit child obligations,
rather than unstated glue. The original unit route is preserved: ordered iteration,
projection coherence and extraction at the unit, with no coordinate-permutation argument.

Edge cases checked in the statements and proof plans: dimension zero is computed directly;
the successor includes d=0; line normalization is only d=1; comparison naturality allows
v=id and arbitrary retained origins; empty schemes and zero complexes add no hypotheses;
both zero block lengths use normalized identity functors and counits.

## New nodes

`def-pur-ordered-affine-transpose-data` registers the relocated concrete construction API.
It asserts no projection or transpose theorem and owns only the declarations not already
owned by `def-pur-ordered-affine-trace-data`.

`lem-pur-ordered-affine-comparison-natural` records the naturality part of original Step 2.
Its proof plan follows the naturality of the line augmentation and the defining Hom chain,
then induction through source reassociation and the pasted-counit compositor.

`lem-pur-ordered-affine-transpose-successor` records original Steps 1 and 3--6 for exactly
one successor. Its induction hypothesis is universally quantified over the base to permit
the last-coordinate tower calculation. Coefficient associativity, projection naturality,
composition coherence and evaluation at the unit identify the resulting trace.

`lem-pur-ordered-affine-line-transpose-normalization` records the line part of Step 4.
It transposes the actual comparison back to its augmentation and applies the projection
unit law with the exact source and compactification transports.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
