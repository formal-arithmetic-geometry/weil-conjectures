## What changed

Implemented the ordinary scalar-restriction comparison by transporting the proved
fixed-ring comparison through the canonical constant-module encoding equivalence.
The construction uses the actual sheafification unit. Its effect on local sections
is the specified normalization, and adjunction extensionality proves uniqueness.

The derived proof transports the restriction square through exact localization,
uses the invertible mate of the encoding equivalence, and applies mate normalization
to the proved fixed-ring site scalar mate. Every existing public definition and
statement is retained verbatim. All additional helpers are private and proved.
The DAG records this route and its actual dependencies.

## Proved and sorry left

Closed both original holes (2 of 2):
- WeilConjectures.finiteHomNuRestriction_existsUnique.
- WeilConjectures.finiteHomSiteBeta_isIso.

Holes added: none. Holes left: none. Split-off modules: none. This is a proof,
not a decomposition. The final complete module compiled with lcompile.py in
57.7 s, with no warnings or errors. Public definitions and theorem signatures
were checked against the original and are unchanged. The delivery check validates
the final packet. The first delivery attempt exhausted its slot wait and returned
DELIVERY BUSY without running compilation or pushing; the packet was retained.

## No longer needed

No original imports or declared dependencies are removed. The original node had
no proof dependencies. No separate K-flat resolution or new tensor-comparison
lemma is required: the proved pbcComparisonReductionMap_isIso is reused.
The direct proof import of ProEtaleConstantModuleEncoding was removed because
IntrinsicRealizationOriginComparison already exports it.
No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node contained no numbered proof plan. Its source paragraph is realized by
canonical encoding and the already proved fixed-ring mate, without constructing
a second flat-resolution model. The ordinary normalization requires the actual
sheafification unit, so an arbitrary choice of a realization isomorphism was not
used. No statement dispute or definition repair is needed.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
