## What changed

Proved `AlgebraicGeometry.Scheme.finiteExtension_properBaseChange` in
`Sheaf.Paper.FiniteExtensionProperBaseChange`, preserving its entire signature and
`finiteExtensionRationalExchangeComponent` unchanged. The integral corollary on
identity squares supplies each preservation witness. Cartesian pasting transfers
the fiber bound to f-prime; field spectra give the identity fiber bound zero.
The first quotient is annihilated by l by the spectral norm and DVR description.
The specified integral exchange is an isomorphism, its lift to the full subcategory
is an isomorphism, and rationalization preserves it. Added proof-only imports of
CompletedOpenExchangeTransport, CompletedExchangeCoherence and PbcActualRingedExchange
for the normalized identity comparisons. Updated the existing node's proof and
proof dependencies to this route. No definitions or public interfaces changed.
On resumption, replaced broad simplification in the spectral-norm calculation by
an explicit change of goal and the natural-number-cast equation. The complete
module compiles through lcompile.py against the current published library in 6.2 seconds.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.finiteExtension_properBaseChange`
(node `thm-weil-pbc-finite-extension`). Added 0 holes; split off 0 statements.
There are 0 textual sorries remaining in the delivered module. This is a proof
from the library's declared dependencies, some of which still use sorry; it is
not a claim that the complete transitive proof is axiom-free yet.

## No longer needed

Removed the following direct proof imports:

- `Sheaf.Paper.CompletedPullback`
- `Sheaf.Paper.CompletedRlimFunctor`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.CategoryTheory.ScalarLocalization`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `Mathlib.LinearAlgebra.TensorProduct.Basic`
- `Mathlib.RingTheory.Localization.Away.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.IntrinsicCompletionCompleted`
- `Sheaf.Paper.PbcQbarCompletedPullback`

The original plan's independent scalar-linearity and rational-extension arguments
are unnecessary for this Lean statement: its exchange component is already defined
as the image under the rationalization functor. Thus the proof no longer directly
uses `lem-weil-linear-abelian-derived-category`,
`lem-pur-left-derived-from-kflat-class`, `lem-weil-pbc-kinjective-total-derived`,
or `prop-weil-pbc-rlim-functoriality`. It does not invoke
`prop-weil-pbc-rational-transport`, though its existing public import and statement
dependency remain unchanged. Removed the obsolete top-level `tool_uses` approval for
`lem-pur-left-derived-from-kflat-class`. Also removed direct proof dependencies
`def-weil-pbc-intrinsic-completion` and
`lem-weil-pbc-constant-completion-equivalence`: their work is encapsulated by
the existing normalized identity comparisons used here.
The constant-completion and intrinsic-completion
modules are not direct proof imports; the normalized existing identity interfaces
encapsulate those arguments. Redundant imports of the coefficient, tensor, scalar
localization and localization-away APIs are already publicly provided by retained
imports. No claim is made that these modules leave the whole targets' closure:
other modules may still need them. The unit's realized statement and steps are
unchanged; this node is below them and realizes none of them itself.

## Where the brief, the DAG or earlier work was wrong

The long previous proof plan proves scalar-linearity and exact rational extension
facts beyond the current theorem's conclusion. The existing component definition
makes ordinary functorial preservation of isomorphisms sufficient for the last
step. The node attachments for completed pullback, ambient exchange, and uniform
triangulation now point at newer interfaces; the proof uses the preserved actual
completed-coefficient declarations, rather than redefining them. No statement
repair or consumer adaptation was required. The existing docstring's longer plan
remains historical; the node and this report record the actual proof route.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
