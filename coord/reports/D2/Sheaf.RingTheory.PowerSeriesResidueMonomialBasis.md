## What changed

Proved `RingTheory.powerSeriesResidueMonomialBasis` with its signature and public imports
unchanged. Added the proof-only import `Mathlib.LinearAlgebra.Basis.Basic` and private,
fully proved helpers for exponent splitting, monomial coefficient calculations, series
column decomposition, spanning, and coefficient recovery. No other module changes.

The series columns are explicitly defined coefficient functions, not witnesses chosen
from an unproved existence theorem. Spanning treats each original polynomial monomial
separately, so finite polynomial support is preserved without a global regrouping
construction. Coefficient recovery proves independence, and `Module.Basis.mk` assembles
the required basis with its exact displayed values.

Updated the existing node's proof and proof_origin to describe this implementation.
The proof follows the same residue decomposition route below the unit level; no unit
statement or realized step is bypassed.

## Proved and sorry left

Closed the sole original hole: `RingTheory.powerSeriesResidueMonomialBasis`
(node `lem-weil-pbc-power-series-residue-monomial-basis`).

Every private helper is proved. There are no remaining sorries, no new holes, and no
split-off statements. The complete module compiles through `lcompile.py` in 42 seconds
on the initial complete-file check. The delivery dry run additionally checks axioms.

The arithmetic uses only positivity of p; no characteristic assumption enters.
The proof covers p=1 and n=0 or m=0 through the same finite products and exponent split.

## No longer needed

None. No original import or dependency node was removed. The original three definition
nodes remain the proof dependencies. The planned construction of polynomial columns
by regrouping all polynomial exponents is unnecessary: the finite support expansion
and the series decomposition prove spanning directly. Temporary split modules used
while developing the argument were removed and are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original node's numbered argument is
valid; its spanning construction can be shortened as described above. Its proof_deps
are definitions matched to Mathlib, rather than pre-existing coefficient lemmas, so
the residue bookkeeping had to be proved here.

The source checkout does not contain literature/stacks-project/more-algebra.tex on
this machine. Read the official [Stacks Tag 07P5](https://stacks.math.columbia.edu/tag/07P5)
instead: its first proof paragraph establishes finiteness from the finite coefficient
extension and the corresponding power-series extension. The explicit residue-basis
construction is the elaboration already documented in this item's node and docstring.


## Second reading by D2

1. Compared the complete delivered module with the repository version. The sole
   existing declaration's signature is byte-for-byte identical, verified separately
   by extracting the text before its proof. Its docstring and visibility are unchanged;
   all four public imports are unchanged. The additional Basis.Basic import is
   proof-only. No definitions or target statements are changed. Verdict: pass.
2. Read every private helper and the final proof. The columns in series_decomposition
   are explicit coefficient functions; no arbitrary existence witness supplies data.
   Spanning uses the finite polynomial support, and independence recovers every scalar
   coefficient using b.repr and the support condition. No sorry or forbidden declaration
   occurs in the delivered Lean source. Compilation and axiom checks are recorded below.
3. There are no split-off statements or added holes. Checked the residue arithmetic
   at p=1 and the empty-variable cases n=0 and m=0: quotient/remainder and empty products
   give exactly the same decomposition and recovery. For p=0 the private recovery lemma
   either has no residue index or has empty variable sets, so it remains valid; the
   public spanning theorem correctly requires p>0. Verdict: pass.
4. Searched the library for residue bases and series decomposition, and independently
   searched Mathlib via msearch grep for MvPowerSeries basis declarations. The matches
   concern topological neighborhood bases, not this module basis. Read the expansion
   API: exponent expansion alone does not supply this coefficient-field residue basis.
   The proof already uses Mathlib monomial coefficient formulas and Basis.mk. All
   original imports serve the unchanged statement, and Basis.Basic supplies the proof
   construction. No old proof dependency becomes unused. Checked sk-thm-p1.realized:
   this auxiliary node is below its realized steps and the unit route is preserved.
   Verdict: pass; no pruning needed.
5. Compared the old and delivered node JSON. Only proof and proof_origin changed;
   proof_deps remains exactly the three Mathlib definition nodes used for bases,
   multivariate series, and polynomials. Read those nodes and checked the three revised
   proof steps against the actual decomposition, support spanning, and recovery code.
   There are no new nodes or change records to validate. Verdict: pass.

Changes by the second reader: appended this independent review and validation evidence
only. No repair to the Lean proof or DAG was necessary. Holes closed: one,
RingTheory.powerSeriesResidueMonomialBasis; holes added: zero.


Validation: a scratch copy of the entire delivered module, with
`#print axioms RingTheory.powerSeriesResidueMonomialBasis` appended, compiled without
errors or warnings through lcompile.py (50.3 seconds). The printed axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`; in particular no `sorryAx` occurs.
