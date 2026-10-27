## What changed

The item theorem `AlgebraicGeometry.Scheme.sfbImmersion_residueComparison_fixed`
retains its statement. Its proof first applies the existing `finiteComparison`
at exponent one. It then transports finite reduction at the source, uses exactness
of the constant-coefficient pullback through `derivedPull_computes`, localizes the
ordinary constant-scalar square, and applies the exact derived factorization for
`sfbFixedResiduePull`.

Two new modules make the two different comparisons explicit:
`Sheaf.Paper.AdicResidueNormalization` states the finite-reduction comparison on a
single scheme; `Sheaf.Paper.ImmersionConstantResidueSquare` proves the ordinary
inverse-image square for an arbitrary coefficient ring. The latter constructs the
canonical constant-ring direct-image map and its module adjunction. On fixed-scalar
sections, direct image commutes with realization because the canonical map sends
each constant scalar to itself. Conjugating the resulting right-adjoint square
proves the square for inverse image. Only private proved helpers are used in that
construction. The item imports both modules privately and privately imports the
existing `derivedPull_computes` theorem with `import all`.

No existing module other than the item, no shared definition, and no existing
public declaration signature is changed. The original node's proof dependencies
now describe this argument.

Validation: `lcompile.py --all` compiled all three final modules without warnings:
normalization 8.3 s, ordinary square 6.8 s, item 11.9 s. The parsed item signature
matches the repository verbatim, all node signatures match their Lean declarations,
and all new dependency references exist. Import-direction checks confirm that the
three new external proof imports do not reach the item.

## Proved and sorry left

The original single hole is closed in
`AlgebraicGeometry.Scheme.sfbImmersion_residueComparison_fixed`
(node `lem-sfb-adic-immersion-residue-comparison-fixed`). The new ordinary theorem
`AlgebraicGeometry.Scheme.sfbImmersion_constantResidueSquare` is proved.

One new hole remains:
`AlgebraicGeometry.Scheme.sfbResidue_normalization`
(node `lem-sfb-adic-residue-normalization`). It compares the two source finite
reductions only. It has one scheme and no immersion, target scheme, pullback,
completion-after-pullback or Noetherian hypothesis. Thus it is strictly a source
coefficient-normalization step, rather than the original comparison under a new
name. Its docstring and node explain the coefficient projection square, flat-term
K-flat transport, balanced tensor maps, and localization counits needed to prove it.

This is a decomposition: one original hole closed, one new hole added, zero net
holes removed among the declarations delivered. Existing imported theorems may
still depend on their own recorded holes; they are not claimed as new proofs here.
No sorry occurs in a definition or private helper.

## No longer needed

No module or node is withdrawn. The existing public imports of the item are
retained. In the new ordinary-square file, the redundant template imports of
`AdicImmersionCompletedModel` and `AdicImmersionResidueTransport` were removed;
`AdicImmersionResidueComparisonCore` supplies its statement dependencies. The new
normalization file imports `SfbCompletionNormalization`, `AdicStratumCompletionUnit`
and `ConstantScalarRestrictionTensor` directly rather than the immersion/residue
transport template imports. These cleanups do not withdraw any existing module. The original direct use of the constant-ring module equivalence is
replaced by the explicit ordinary square, which still uses that equivalence
through `ConstantScalarRestriction.restriction` and the realization comparison;
it is not claimed as globally pruned. The completion-normalization node remains
needed through the new source normalization step. The unit's immersion and
finite-projection route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original node compresses two distinct conjugations into one sentence:
normalizing the completed coefficient before finite scalar extension, and
identifying ordinary constant-ring pullback with fixed-scalar inverse image.
`finiteComparison` supplies the completed-pullback/finite-projection square but
does not itself supply either conjugation. The delivery proves the ordinary one
and isolates the source normalization. The residue target and its coefficient
action are unchanged.

For edge cases, the ordinary square permits the zero ring and empty sites: its
section identities and adjunction argument require neither nonzero constants
nor points. The new normalization step permits I=0 and I=A; in the latter case
the finite coefficient module category is the zero category. Tensor transport
uses the ringed-site monoidal equivalences, not an assertion that an arbitrary
exact equivalence preserves flatness.

## New nodes

`lem-sfb-immersion-constant-residue-square` records the proved ordinary square.
Its source is the constant-ring and inverse-image/direct-image adjunction material
of Stacks, Tags 00YV, 03A0, 03CY and 03D2. The proof uses the existing scalar
normalization equation and the supplied algebraic-presentation module adjunction,
then computes the right-adjoint square on sections and invokes adjoint uniqueness.

`lem-sfb-adic-residue-normalization` records the remaining single-scheme finite
coefficient normalization. Its source is the original node's projection-and-K-flat
argument, Stacks Tags 03A0, 03CY and 06YY, and the coefficient projection identity
in `SfbCompletionNormalization`. Both nodes remain under `sk-lem-integral-models`
and cite its imported Stacks detail as their blueprint ancestor. No change record
is needed because no existing statement or definition is changed.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
