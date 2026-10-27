## What changed

Replaced the proof hole in `continuousFiniteEtaleLattice_sheet_charts` by a
complete matrix-to-fixed-lattice argument. The remaining local-frame computation
is `continuousFiniteEtaleLattice_sheet_matrices` in its own module. It supplies
continuous invertible matrices and their inverses in a common rational frame;
it asserts no fixed lattice, lattice basis, constant coset or discrete
lattice-class presentation.

The proof defines a matrix's integral lattice by inverse-coordinate integrality.
An explicit integral linear equivalence supplies a basis whose columns are the
same as those of a rational basis. Integral change matrices and their inverses
preserve integral coordinates, so equal integral right cosets give equal
lattices. The integral coefficient ring is open since it contains the open unit
ball. `continuousMatrixCoset_neighborhood` gives a common open refinement on
which all finitely many cosets are constant. A proved subspace-topology argument
identifies pointwise membership with the range of continuous lattice-valued
functions. Binding these open covers with the supplied pro-etale cover gives
the claimed simultaneous sheet charts. Generic proved helpers keep the frame
and section-range family abstract while assembling covers.

The real definition `continuousFunctionPresentationRange` packages the ordinary
sectionwise range of an encoded internal map in supplied coordinates. Its
defining equation is proved by reflexivity. The proof uses it internally, then
applies that equation to recover the original explicit sheet-range formula.
The item's public signature and all its former public imports stay verbatim.
No other existing module, source-library declaration, target statement or
existing definition changes. All new imports used only by the proof are private.

Validation: the item compiles in 32.0 seconds, the new matrix statement in
29.3 seconds, and the range API in 1.8 seconds. The unchanged direct importer
`Sheaf.Paper.ContinuousFiniteEtaleTraceImageCharts` compiles against the complete
overlay in 52.1 seconds, using the original trace-range theorem. Its temporary
unchanged sandbox copy was removed after this check. All files are within the
60-second limit; no profiler or tracing option remains.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleLattice_sheet_charts`
(node `lem-sfb-continuous-finite-etale-lattice-sheet-charts`). All private lattice,
basis, coset-invariance, openness, continuous-range and cover helpers are proved.

Added one hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleLattice_sheet_matrices`
(node `lem-sfb-continuous-finite-etale-sheet-matrices`). Its docstring and DAG
node give the complete local-basis and coefficient-encoding argument.

There are zero holes in the item, zero in the range-definition module, one in the matrix-coordinate module, and no changes to other existing modules. This
is a decomposition: one hole closed, one strictly smaller hole added, net zero
within changed modules. A proof independent of that remaining local-frame step
is not claimed. The pinned ledger determines the targets-closure count.

## No longer needed

No existing public import is removed and no module is withdrawn. The new matrix
module does not need `Sheaf.Paper.ContinuousLatticeSum`. The proof does not use
`lem-weil-pbc-lattice-sheaf-locally-constant` from
`Sheaf.Paper.LatticeSheafLocallyConstant`, its constant-sheaf section lifting,
spectral WithAbs coefficient replacement or universe-lift transport. It proves
matrix-coset local constancy directly over the supplied E. The lattice-class
node remains a realized step of `sk-lem-stratified-lattice` in the parent DAG;
that unit step and its parent dependencies stay. Only the extra use inside
this sheet-chart subargument is avoided. The basic coset definitions and
`integralMatrixSubgroup_mem_iff` from `Sheaf.Paper.LatticeSheafBasic` remain
needed, recorded by `lem-weil-pbc-matrix-lattice-coset-invariance`.

The converse integral-module reconstruction statement
`lem-weil-pbc-continuous-module-encoding-lattices` is not used: the matrix step
uses the scalar-extension comparison directly. The original finite-etale
splitting, local-freeness and encoding dependencies are retained in the new
matrix-coordinate node rather than directly in the matrix-to-lattice proof.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan combines coefficient-encoding
normalization and the discrete-lattice step, suggesting a universe lift to
invoke the lattice-class theorem. That detour is unnecessary:
`continuousMatrixCoset_neighborhood` works directly with Type-zero E and schemes
in any universe. The DAG now separates the remaining local-frame computation
from the proved algebraic and topological argument.

The expanded encoded sheet-range expression caused deterministic kernel timeouts
when repeatedly normalizing categorical maps. The concrete range API on an
abstract internal morphism, the generic frame/range cover helpers, and direct
assembly under the item's original instances avoid those conversions. Its
proved defining equation recovers the former formula at the last step. This
requires no interface change to the item or to its consumers.

Edge cases checked for the new statement are rank zero (empty matrices and
coordinate tests), empty X (empty cover), empty open restrictions (unique
continuous sections), and a single sheet. The rational frame is common; the
integral sheet lattices may differ. No simultaneous diagonalization or equality
of distinct integral lattices is asserted.

## New nodes

`lem-sfb-continuous-finite-etale-sheet-matrices`, in
`dag/nodes/sec-six-functors-basics/`, records the continuous local-frame
computation before making matrix cosets constant. Its module is
`Sheaf.Paper.ContinuousFiniteEtaleSheetMatrices`. LeanSearch, LeanFinder, Loogle
and source grep found ordinary continuous-matrix and basis lemmas but no result
normalizing the actual internal sheet embeddings.

`def-sfb-continuous-function-presentation-range`, in the same directory, records
the ordinary range of a supplied internal morphism in supplied coordinates.
Its module `Sheaf.Paper.ContinuousFunctionPresentationRange` contains the real
definition and its proved defining equation, with no holes. LeanSearch,
LeanFinder, Loogle and repository grep found the ordinary Set.range operations
used in this construction and no existing named wrapper for the encoded range.
Neither the new definition nor any public data are chosen from an unproved
existence theorem.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
