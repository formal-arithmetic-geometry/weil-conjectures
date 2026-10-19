## What changed

Proved six declarations in `Sheaf.Paper.IntegralScalarExtensionWellDefined` without
changing any existing signature, definition, or import. The finite coefficient
proofs use spectral norm uniqueness, DVR witnesses, ideal powers, and quotient
induction. The constant section proof uses the existing constant-to-completion
limit lift and sectionwise limit extensionality. A proved private helper establishes
restriction compatibility of the chosen constant section. Multiplication by that
section then defines the natural chain endomorphism; sectionwise extensionality
proves uniqueness.

The retained module was compared with the current shared source; only the six
proof bodies and one proved private naturality helper differ. A fresh server
compile with `lcompile.py` passed in 8.3 seconds with no diagnostics. The required
resumption dry run passed: candidate `f132250820` compiles and passes preflight
(review class AUTO). No new nodes or statement repairs.

## Proved and sorry left

Closed six of the original eight holes:
`WeilConjectures.integralScalar_absoluteValue`,
`WeilConjectures.integralScalar_integer_mem`,
`WeilConjectures.integralScalar_quotient_kernel`,
`WeilConjectures.integralScalarQuotientMap_transition`,
`WeilConjectures.integralScalarConstant_existsUnique`, and
`WeilConjectures.integralScalarChainAction_existsUnique`.

Two existing holes remain, unchanged:
`WeilConjectures.integralScalarTransition_existsUnique` and
`WeilConjectures.integralScalarExtensionWellDefined`. Both realize
`lem-weil-integral-scalar-extension-well-defined` and retain their source and
complete proof plans. The first still needs the sheafified balanced tensor
transition and its uniqueness; the second still needs quasi-isomorphism invariance,
Roos localization/descent with shifts, and scalar compatibility.

Added zero holes. This is a partial proof delivery, with no decomposition. The
proved declarations use existing library dependencies, including declarations
whose own proofs remain open.

## No longer needed

None. No import or dependency is pruned: the remaining main theorem still follows
the recorded proof route and needs its existing proof-dependency interfaces.

## Where the brief, the DAG or earlier work was wrong

None found. The earlier attempt's work was retained and checked against the current
source. The existing tensor-transition constructions found in
`CompleteCoefficientDatum` use constant source coefficient sheaves; the source here
is the completed coefficient sheaf, so those statements do not directly close the
remaining transition obligation.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
