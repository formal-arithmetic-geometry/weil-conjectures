## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.embeddedIntegralCompletenessTransport`
by a derived transport proof from an underived constant scalar square and its residue
kernel identity. The theorem's signature and existing public imports are unchanged.
Proof imports add `EmbeddedIntegralScalarKernelSquare`,
`FlatRingedIdealCompleteEquivalence`, and `ContinuousCoefficientModuleEncoding`.

The proof descends the ordinary scalar-restriction square using the exact derived
functor composition and natural-isomorphism APIs. It proves the small section-module
restriction comparison, applies the existing local completeness restriction iff, and
uses internal-Hom functoriality to pass between exact derived functors and the chosen
representatives in `smallDerivedObject`. The small section-module functors are shown
to be equivalences using the existing section-module equivalence and the equivalent
small site, so their exact derived functors are available. No arbitrary witness is
used to define data: the new existence statement is eliminated only inside a theorem
proof.

## Proved and sorry left

Original hole closed by a complete assembly proof:
`AlgebraicGeometry.ProEtale.embeddedIntegralCompletenessTransport`
(`lem-sfb-embedded-integral-completeness-transport`).

One hole added and left:
`AlgebraicGeometry.ProEtale.embeddedIntegralScalarKernelSquare`
(`lem-sfb-embedded-integral-scalar-kernel-square`). This is a decomposition, with net
zero holes closed, not a claim of a full proof independent of sorry. There is no sorry
in the item module. The new theorem is strictly an underived step: it mentions neither
a complex, completeness, a module-category equivalence nor derived internal Hom.
The existing restriction theorem supplies the whole derived completeness argument.

## No longer needed

No module is withdrawn and no existing import is removed. The original node's direct
DVR proof dependency moves to the underived scalar-kernel-square node. The original
plan's reconstruction of slice localizations and comparison of derived internal Homs
is unnecessary here: `siteDerivedRestrictScalars_locallyDerivedComplete_iff` already
proves this for arbitrary ring maps and extended ideal sheaves. The assigned module
now uses that existing theorem rather than introducing a new derived transport axiom.
The unit's constant-coefficient completeness route is retained. The coefficient
comparison theorem is not used as a proof dependency; its statement dependency in
the existing node is retained unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan did not identify the already-proved generic ringed-site restriction
completeness theorem. Most of its derived part can be implemented from this API.
The genuine missing ingredient is the underived constant scalar square for the given
arbitrary continuous-ring isomorphism, together with identification of the first
residue kernel. An iff split into two implications would repeat the same obstacle;
that draft was discarded and is not delivered.

The kernel-square statement is true for arbitrary e: naturality against points makes
its action on continuous functions pointwise the induced integer-ring isomorphism.
It preserves constants and the local ring's nonunits, hence its maximal ideal. The
uniformizer assumption identifies the first embedded kernel; the spectral first ideal
is also its maximal ideal. The scalar direction is from spectral constants to embedded
constants, matching e inverse and contravariant scalar restriction. The empty scheme
and zero or unbounded complexes introduce no additional hypothesis.

## New nodes

`lem-sfb-embedded-integral-scalar-kernel-square`, module
`Sheaf.Paper.EmbeddedIntegralScalarKernelSquare`, is the underived scalar square and
extended residue-kernel identity. Its docstring gives the pointwise, local-ring,
sheafification, and inverse-image argument. The assigned node is updated to the actual
Lean assembly from this statement and the existing generic local completeness iff.
Blueprint searches for “scalar square” and “kernel completeness” found no duplicate
node. The existing flat ringed-ideal complete equivalence node is used as a generic
tool in the same constant-coefficient completeness argument, without replacing a
step of the unit route. No definition, existing statement, public import, or consumer
changes; no change record is needed.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
