## What changed

Restored Sheaf.Paper.VerdierExchange from its current quarantine/rework source.
Reconciled the restoration with the newly reviewed definition ownership in
Sheaf.SixFunctors.VerdierExchangeData: publicly import that module instead of
redeclaring its 34 definitions. This is explicitly required by the current
reviewed_lean note of def-sf-verdier-exchange-data. Package, Assertion and
verdier_exchange retain their archived statements, fields and docstrings.
All original imports remain; the coefficient applications specify their already
inferred universe u. Optional unused generated record helpers are disabled.
The imported data module then failed in the compile tool's private dependency overlay
at 60 seconds. It is unclaimed. Its live source later disappeared while the DAG retained the same
reviewed module attachment; the tested copy is preserved in this packet. This packet
repairs its existing signedShift choice by
abstracting the same expression over its site before specialization, suppresses unused
generated helpers and uses direct case elimination for ringInclusionShift. All public
signatures, fields, docstrings and normalization equations are preserved.

Change record: coord/changes/B2-verdier-exchange-elaboration.md.

## Proved and sorry left

Assigned quarantine/build repair; zero theorem holes closed and zero added.
The single retained hole is WeilConjectures.VerdierExchange.verdier_exchange,
attached to sk-thm-sf-verdier-exchange and thm-sf-verdier-exchange. The existing
complete proof plan and source docstring are preserved. No theorem is renamed,
weakened, replaced or split off, and no definition contains sorry.

The final two-file packet compiled successfully through lcompile.py --all: both
Sheaf.SixFunctors.VerdierExchangeData and Sheaf.Paper.VerdierExchange returned
compiled with exit code 0. The original data dependency failed at 60 seconds before
its repair. The archived consumers AdmissibleVerdierExchange, GlobalVerdierDuality,
TensorAdjunctionExchange and VerdierCoefficientRealization, plus the data owner's
direct consumer TensorHomTranspositionData, all compiled unchanged together with
both packet files (exit code 0). The required delivery tool performs independent preflight.

## No longer needed

No mathematical dependency, node, module or original import is pruned. A copy of
def-sf-verdier-exchange-data carries its existing lean.file attachment and a lean.note
explaining restoration so the
restored dependency module is recognized by the delivery gate. The 34 copied
definitions composition through integralAlphaRealization (including smallSite) are
supplied by their reviewed owner Sheaf.SixFunctors.VerdierExchangeData. This is shared
ownership reconciliation, not withdrawal of those declarations. The unit route,
normalization equations and all-stage package remain intact.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined, not withdrawn. The B2 return file contains only the old
upstream-sync notice. During this session def-sf-verdier-exchange-data was updated to
the independently reviewed Q38 data module. Its note explicitly requires restored
parents to import the data module and drop their copies. Keeping the archive intact
would now redeclare the shared interface; the restoration follows that instruction.
The file separation is the pre-existing reviewed dependency repair, not a new split
made to evade a compile bound.

The archived module contains one theorem hole. The DAG nodes
lem-sf-finite-exceptional-compositor-coefficients and
lem-sf-adic-exceptional-compositor-coefficients have no lean attachment despite the
brief's readiness promise. This delivery repairs restoration/build compatibility and
does not manufacture substitute proof dependencies.

## New nodes

None. The packet includes the existing def-sf-verdier-exchange-data node with only
a restoration explanation appended to lean.note:
its reviewed lean.file already names Sheaf/SixFunctors/VerdierExchangeData.lean.
The file disappeared during delivery waits; preflight therefore classified its
restoration as a new module and required the owning node in this packet. No statement,
proof route, ownership or review field is changed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
