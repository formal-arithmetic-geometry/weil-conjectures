## What changed

Proved
`SheafOfModules.ringedSlicePullbackMateNormalization` without changing its
statement, public imports, or ordinary comparison construction.

Restriction preserves independent K-flatness and termwise flatness by the existing
slice restriction theorems. The private `epsilon_isIso` transfers model invertibility
from the normalized derived-image existence theorem by uniqueness of left derived
functors. The ordinary comparison's transpose is the degreewise unit identity.
Private categorical helpers derive the normalized global unit and compare the two
local transposes using the square's unit, naturality, and the given normalization.
The counit field proves the two exchange-mate assertions. The private categorical
calculation adapts the existing argument in `RingedSliceDerivedMate` to the given
adjunction square.

The node records these proof dependencies. The local elaboration environment is
documented in `coord/changes/M4-ringed-slice-pullback-mate-proof-environment.md`.
The downstream check reports zero current Lean importers; no parent is withdrawn. Local irreducibility keeps the derived
restriction constructions behind their functor and comparison-isomorphism interfaces.

## Proved and sorry left

Original hole: `SheafOfModules.ringedSlicePullbackMateNormalization`.
Holes closed: 1, by `SheafOfModules.ringedSlicePullbackMateNormalization`.
Holes added: 0. Sorry left: none. Split-off holes: 0.
All five new private helpers have complete proofs; no public declaration or module
was added. The complete file compiled through lcompile.py in 44.8 seconds with no
warnings. The final packet retains the theorem statement text verbatim and only
subsequently simplifies unused local bindings and updates its proof docstring.
The delivery tool's initial compile also passed. Server preflight requested the
change record for local attributes; that record is now included for resubmission.

## No longer needed

Removed unused private proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.RingedSliceDerivedComparisons`.

The proof does not directly use `lem-pc-kflat-resolution`,
`lem-weil-pbc-ringed-topoi-derived-pullback`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-ringed-slice-derived-comparisons`, or
`lem-weil-pbc-ringed-derived-slice-localization`.
The given normalized presentations and hnormal supply the comparison data;
model invertibility and restriction preservation use existing slice-specific results.
The obsolete tool approval for `lem-pc-kflat-resolution` is removed from the node.

No declaration or module is withdrawn. An import-graph comparison found zero modules
removed from the item or targets closure: the removed direct imports remain transitively
reachable through retained imports. Dependencies used inside retained results remain
needed. Module pruning: none.

## Where the brief, the DAG or earlier work was wrong

The planned resolution-descent step is unnecessary for the formal statement.
The model equation follows on every complex from normalization; the exchange identity
follows on every derived object from the square's counit field. The flat-term K-flat
hypotheses provide restriction preservation and model invertibility. No K-injectivity
of the ordinary pulled-back complex is used. The statement and fixed unit route stay
unchanged.

The retained attempt was unverified. After the compile service resumed, it exposed an
unsupported pretty-printer option and expensive unfolding during categorical rewrites.
This revision removes that option, proves the direct-image identity explicitly, and
uses private categorical helpers to control unfolding. Locally prioritizing
`hasSheafCompose_of_preservesLimitsOfSize` avoids a costly general multicospan-limit
instance search; the existing derived-category elaboration settings and local
irreducibility do not change any public construction or statement. No target or source-library
signature, data construction, or axiom has been changed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
