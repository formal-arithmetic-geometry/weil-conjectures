## What changed

Replaced `diagonal_source_quotient_normalization` by a cokernel comparison. The
coefficient calculation proves that the lifted p-adic residue projection is a
cokernel of the positive prime power, using `PadicInt.ker_toZModPow` and its
surjectivity. Constant sheafification and finite direct image preserve this
cokernel. The quotient comparison with `D.quotient` preserves its projection,
and `pro_supported_generator_scalar` proves the required normalization.

Added `Sheaf.Paper.SupportedPadicScalarExtension`, proving the ordinary supported
p-adic scalar-extension identification independently of every residue level and
reduction presentation. The proof uses lifted integer scalar forgetting,
`finite_ordinary_scalar_unit`, and the canonical comparison adjunctions. Every
new helper is proved. Existing signatures, public imports, and definitions are
unchanged. The blueprint unit's supported-source scalar-extension route is kept.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.diagonal_source_quotient_normalization`
(`lem-sfb-diagonal-source-quotient-normalization`).

Also proved
`AlgebraicGeometry.ProEtale.supported_padic_scalar_extension`
(`lem-sfb-supported-padic-scalar-extension`).

No holes added; no `sorry` left in the delivery. This is a proof, not a
replacement of the original hole by another obligation. Both delivery modules
compiled through `lcompile.py`; the final item check passed without warnings
(reported 10.9 seconds). The service accepted the auxiliary module as compiled.
The required delivery command performs the independent compile and axiom probes.

## No longer needed

No original imports were removed: the item originally imported only its public
statement interface. Its previous planned proof dependencies
`lem-pur-constant-two-term-resolution` (module
`Sheaf.Paper.ConstantTwoTermResolution`) and
`lem-weil-pbc-site-module-sheaf-constant-ring-equivalence` (module
`Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`) are unnecessary
for this proof: it works directly with external constant module sheaves and
ordinary cokernels, without a ringed-site equivalence or a K-flat resolution.

The planned explicit uses of `lem-sp-supported-integral-residue-sequence` and
`lem-sp-cartier-reduction-site-comparison` are replaced by the ordinary finite
scalar-unit theorem and canonical supported comparison isomorphisms; the full
Cartier/Kummer reduction theorem is not invoked. These modules may remain
reachable through the unchanged public statement interface or other proofs;
this delivery claims no global module withdrawal.

## Where the brief, the DAG or earlier work was wrong

The ordinary-module declaration listed by
`lem-fd-proetale-finite-pushforward-exact` exists as
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isFinite` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite`,
although that node still carries `lean_not_found`. This proof uses its ordinary
module-sheaf part only; the node's condensed and derived assertions are not used.

No statement defect was found. The earlier proof plan mixed a needed ordinary
quotient calculation with stronger derived and ringed-site machinery. In
particular the Cartier reduction theorem assumes an invertible prime on the
base, whereas this source quotient assertion does not. The new proof uses its
ordinary supported comparison ingredients without introducing that hypothesis.

## New nodes

`lem-sfb-supported-padic-scalar-extension`, in
`Sheaf.Paper.SupportedPadicScalarExtension`, records the proved
insertion-of-one-normalized scalar extension of a closed supported integral
constant to p-adic coefficients. It is the source paragraph of blueprint
step (3), before any finite quotient. Its proof transfers the ordinary Hom
universal property through finite direct image and comparison adjunctions.
Searches found the existing finite ordinary scalar-unit theorem and no direct
Mathlib supported-constant identification. No change record is needed because
no existing interface is changed.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
