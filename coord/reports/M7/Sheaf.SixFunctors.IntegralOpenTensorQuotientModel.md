## What changed

Constructed the ordinary consecutive-coefficient open restriction comparison in
`Sheaf.SixFunctors.IntegralOpenScalarRestrictionComparison`, and imported it
privately into the item module. Naturality of the supplied
system ring map gives the finite transport square. Module pushforward composition
and congruence preserve the underlying sections. Composing this transport with
the inverse of `RingedOpenScalar.comparison` gives the comparison and proves its
specified generator normalization.

The target theorem is reduced, with its signature unchanged, to the ordinary
module quotient square and the scalar K-flat quotient-model formula. The private
categorical lemmas localize the ordinary square through exact functor factors
and conjugate it by the canonical reduction models. New imports used only by
proofs are private. No other existing module or public interface is changed.

Validation: `lcompile.py --all` accepted all four delivery modules in import
order with the required per-file limit. The original theorem statement was
compared byte-for-byte with the repository version and is unchanged.

## Proved and sorry left

Original holes: 1, `WeilConjectures.integralOpenTensorQuotientModel`.
Its proof is complete from the two intermediate statements below. This is a
decomposition (one upper hole closed, two lower holes added), not a net reduction
of the hole count.

New holes, each the whole proof of one public theorem:

- `WeilConjectures.integralOpenTensorModuleQuotientSquare`, node
  `lem-sf-integral-open-tensor-module-quotient-square`: ordinary modules only,
  assuming one already constructed generator-normalized comparison; no derived
  category, K-flatness or construction of the comparison.
- `WeilConjectures.integralReductionQuotientModel`, node
  `lem-coef-integral-reduction-quotient-model`: scalar reduction at one site,
  with no open immersion or tensor comparison.

The ordinary comparison and its generator formula are proved in
`WeilConjectures.integralOpenScalarRestrictionComparison` (no holes). The
exact-localization square identity and conjugation argument are proved in the
item module. No definitions
contain holes.

## No longer needed

No original public import is removed. No existing module or node is withdrawn.
The proof does not use the full `CoefficientDerivedSystemCalculus` structure or
any completed-system reconstruction comparison. The original proof dependency
`lem-coef-derived-system-evaluation-calculus` is now used only within the two
smaller quotient-normalization steps, rather than as a claim that directly
supplies the open tensor square. The original dependencies on
`lem-sf-integral-open-reduction-comparison` and
`lem-cbc-ringed-open-scalar-adjunction` remain through the proved ordinary
comparison. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing DAG step describing localization did
not provide an API directly equating the specified adjoint quotient mate with
its canonical K-flat representative. The new single-site statement isolates
exactly that missing normalization. The ordinary tensor quotient step is also
separate from construction of the open scalar restriction comparison; treating
those as one existence claim would hide the work proved here.

The module's statement and all existing definitions are preserved. The zero
complex, the empty open and n=0 obey the same generator/unit computations; no
boundedness or flatness of a quotient ring is introduced.

## New nodes

`lem-sf-integral-open-scalar-restriction-comparison`, in
`dag/nodes/sec-smooth-purity/`, records the proved construction of the ordinary
comparison and its generator normalization (parent Steps 1 and 2). It is kept
in a separate module so that checking the coefficient transport and checking
its derived localization each stay within the per-file time limit.

`lem-sf-integral-open-tensor-module-quotient-square`, in
`dag/nodes/sec-smooth-purity/`, records parent Step 3 before localization, with
the same generator normalization and arbitrary modules.

`lem-coef-integral-reduction-quotient-model`, in
`dag/nodes/sec-smooth-purity/`, records the single-site K-flat normalization in
parent Step 4. Its proof uses the normalized derived scalar unit and the ordinary
quotient mate, independently of open functors. Both nodes include source,
proof steps, Mathlib searches and exact Lean attachments. The parent proof and
proof dependencies now follow this decomposition. The record
`coord/changes/M7-integral-open-tensor-quotient-private-helpers.md` documents
the scope of the new private helper sections and their variable commands.
No existing statement, definition or other module is changed.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
