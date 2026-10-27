## What changed

Proved `AlgebraicGeometry.Etale.FiniteSmoothPurity.quotientRootLineComparison` in
`Sheaf.Paper.QuotientRootLineComparison`, with its statement unchanged. Added proof-only
imports of `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback` and
`Sheaf.SecSmoothPurity.ReductionExceptionalObjects` (the latter uses `import all` for its
proved private ordinary scalar isomorphism lemma).

Apply the existing exponent-change comparison at the target coefficient ring, then compose
it with the existing fixed-exponent scalar comparison. Scalar-adjunction naturality proves
the composite generator formula, and derived-single functoriality proves the derived
normalization. Only the assigned Lean module and its node are changed.

Validation: the required `lcompile.py` single-file compile passed cleanly in 33.8 seconds,
with no warnings. Both added proof imports are used. The theorem signature and public
imports are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.FiniteSmoothPurity.quotientRootLineComparison`
(`lem-pur-quotient-root-line-comparison`). Zero holes remain in the item. Zero new holes or
split-off statements. The proof uses the existing declared dependencies; their own proof
obligations are not claimed closed by this delivery.

## No longer needed

None: no import removed, and both original declared dependencies remain used. The local
primitive-root construction and fresh K-flatness argument in the plan need not be repeated:
existing exponent-change and fixed-exponent scalar APIs already supply them. No existing
module or node is withdrawn or claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan describes reconstructing the quotient sheaf and derived comparisons.
The exponent-change clause of `finiteEtaleTwistPullbackData`, already in the declared
`lem-asd-etale-finite-twist-pullback` dependency, supplies the required root map and its
normalized comparison over the target ring. The existing `reductionEtaleTateIso` and proved
ordinary scalar isomorphism supply the other half. The updated node records this composition
and the existing nodes owning those scalar APIs. No statement or definition repair is needed.

The argument includes equal levels, the empty scheme, and zero coefficient rings: it uses
the existing universally quantified comparison theorems without assuming a primitive root
or nontrivial global sections.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
