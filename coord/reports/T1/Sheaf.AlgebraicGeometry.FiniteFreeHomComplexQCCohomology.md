## What changed

Proved `AlgebraicGeometry.finiteFree_homComplex_qc_cohomology` without changing its
signature or any existing public imports. The proof performs a genuine induction
on the finite source support width, constructs the stupid tail using the existing
Lean definition, transports its support and finite-free properties, and combines
the existing `exists_homComplex_stupid_tail_shortExact` theorem with the one-column
calculation and extension closure below. The empty interval is covered by choosing
`(b-a).toNat` and widening to `[a,a+(b-a).toNat]`.

Three new modules contain proved tools (no postponed proofs):

- `Sheaf.AlgebraicGeometry.SingleSupportedFiniteFreeHomologyIso` computes the
  cohomology of internal Hom from a source supported in one degree. Its proof
  constructs the inverse to the surviving product projection, checks the actual
  differential formula, compares the three-term complexes, uses exactness of
  finite-free internal Hom, and applies the finite-free coordinate isomorphism.
- `Sheaf.AlgebraicGeometry.SingleSupportedFiniteFreeHomQC` transports finite
  coproduct closure through the localized-site/open-subscheme equivalence and
  applies that cohomology calculation.
- `Sheaf.AlgebraicGeometry.LocalizedComplexQCHomologyExtension` transports the
  long exact cohomology sequence to the open subscheme and uses the proved
  five-term weak Serre-class lemma with kernel, cokernel and extension closure.

All added imports in the original module are proof-only imports. The second reader also
made the new extension module’s HomologySequence import proof-only. Private helpers
are fully proved; no definition selects arbitrary data from an unproved existence
statement. All four modules compiled without warnings within the single-file
limit. The delivery dry run performs the required axiom and direct-sorry probes.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.finiteFree_homComplex_qc_cohomology`.

Also proved all three newly recorded tools:
`AlgebraicGeometry.single_supported_finiteFree_homology_iso`,
`AlgebraicGeometry.single_supported_finiteFree_hom_qc`, and
`AlgebraicGeometry.localized_complex_qc_homology_extension`.

Sorries left in the item: none. Sorries added: none. This is a proof from existing
library dependencies, not a decomposition into new holes. The delivery does not
claim to close any pre-existing holes in those dependencies.

The proofs are uniform in the universe, integer degree and target complex. The
one-column calculation includes rank zero and the empty open; no target
boundedness assumption is introduced. The induction handles both ordered and
reversed original support bounds.

## No longer needed

No import was removed from the original module: its existing public imports
provide its statement and remain intact. Removed the unused Hom-complex and free
module public imports from the newly written extension-closure module after its
proof compiled.

The planned binary-sum theorem
`lem-weil-pbc-quasi-coherent-module-direct-sum` and its module
`Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum` are not used. The
already proved `Scheme.Modules.isQuasicoherent_sigma` in
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` gives all the finite
sums needed here directly; its node is
`lem-weil-pbc-quasi-coherent-module-coproduct-closure`. No new binary-sum import is added. The other old direct proof dependencies are now used through the new helpers:
`def-pc-derived-category`, `lem-sc-finite-free-internal-hom-exact`,
`lem-weil-pbc-complex-ses-homology-long-exact`,
`lem-weil-pbc-quasi-coherent-module-kernel`,
`lem-weil-pbc-quasi-coherent-module-cokernel-closure`, and
`lem-pc-quasi-coherent-extension`. They remain in the proof closure.
`def-pur-hom-complex` remains a direct dependency. This is the only
planned mathematical dependency pruned; internal-Hom exactness, the long exact
sequence, kernel, cokernel and extension closure remain needed through the three
new proved tools. DerivedCategory remains an existing statement import.

## Where the brief, the DAG or earlier work was wrong

The DAG supplied the mathematical argument but no interface for its one-column
cohomology calculation or its localized-site cohomology extension step. Both are
now implemented rather than postponed. The existing stupid-tail short-exact Hom
theorem, found by local library search, supplies the filtration step without
constructing another finite-filtration interface. The unit statement and its
steps are preserved; this only implements the subordinate finite-column lemma.

The cited Stacks TeX files are absent from this read-only clone. Read the official
Stacks pages for Tags 0A6H, 08I5 and 01IE; the new proofs are marked as agent-written
implementations of their calculations. Tag 08I5 itself states a bounded-below
case, while the one-column calculation used here is valid for arbitrary targets
because just one source factor survives. No bounded-below assertion is inferred
from that tag for arbitrary targets. LeanSearch returned Internal Server Error;
this is recorded without an absence verdict and supplemented by LeanFinder,
Loogle and local source searches.

## New nodes

`lem-sc-single-supported-finite-free-homology-iso` records the proved one-column
cohomology isomorphism in `SingleSupportedFiniteFreeHomologyIso.lean`.

`lem-sc-single-supported-finite-free-hom-qc` records its proved quasi-coherence
consequence in `SingleSupportedFiniteFreeHomQC.lean`.

`lem-sc-localized-complex-qc-homology-extension` records proved extension closure
of quasi-coherent cohomology in `LocalizedComplexQCHomologyExtension.lean`.

The existing `lem-sc-finite-free-hom-complex-qc-cohomology` node now records the
finite-width induction and these dependencies. No existing statement, definition,
visibility or public import changed; no change record or forced adaptation is
needed.

## Second reading by T1

1. Compared every delivered module with the repository. Only the item exists
   there; its entire existing declaration signature is byte-for-byte unchanged,
   as are its existing public imports. The other three modules are new. The
   existing node changes only proof, proof_deps and proof_origin. No statement or
   definition change, change record or forced adaptation is needed. Verdict: pass.
2. Compiled all four modules in import order without errors or warnings
   (22.7, 23.2, 15.5 and 17.6 seconds). Independently printed axioms of the item
   and all three public helper theorems: each uses exactly propext,
   Classical.choice and Quot.sound, with no sorryAx. Scanned all delivered Lean
   for forbidden declarations and sorry: none. soleFactorIso constructs its
   inverse by an actual limit lift; the other choices unpack specified
   isomorphisms or universal properties. No arbitrary unproved existence witness
   is used to define data. Verdict: pass.
3. There are no split-off holes. Read all three new proved helper statements and
   their complete proofs. Checked rank zero, empty opens, arbitrary target
   bounds, and the degree k+n indexing: the source differential vanishes, so
   there is no shift-sign error. The five-term sequence has the cokernel as
   subobject and the kernel as quotient. Fresh LeanFinder search for internal Hom
   concentrated in degree k returned external Hom-complex APIs, not a replacement;
   Loogle’s IsLimit query was not indexed (no absence inference). Fresh grep
   found the exact-functor and quasi-coherent transport ingredients already used.
   Local searches also found SingleDegreeExactTermHomQuasiIso and
   StrictlyPerfectDerivedInternalHom; neither states the required cohomology
   isomorphism or quasi-coherence result. Verdict: pass.
4. Read the proof from the item downward: width-zero calculation, actual stupid
   truncation, existing stupid-tail short exact theorem, and long exact sequence.
   Checked width reduction and reversed bounds b<a; widening by (b-a).toNat is
   valid even then. No shorter applicable library theorem was found. Existing
   imports needed for the public statement stay. Corrected HomologySequence
   visibility in the new extension module and independently recompiled it.
   No longer needed now explicitly accounts for every old proof dependency:
   binary-sum closure is replaced by existing coproduct closure; all other
   mathematical ingredients remain through the helper proofs. Read the unit’s
   realized field (currently empty) and statement: this subordinate finite-column
   implementation neither changes it nor bypasses its route. Verdict: pass.
5. Matched node proof steps and dependency unions to the Lean proof and verified
   new node provenance, sources, searches, blueprint, chapter, unit and Lean
   records. Independently checked the official Stacks pages for [0A6H](https://stacks.math.columbia.edu/tag/0A6H),
   [08I5](https://stacks.math.columbia.edu/tag/08I5), [0A8X](https://stacks.math.columbia.edu/tag/0A8X),
   [0117](https://stacks.math.columbia.edu/tag/0117) and [01IE](https://stacks.math.columbia.edu/tag/01IE);
   their formulas and closure results support the cited agent-written argument.
   Replaced the three new lean.statement records with verbatim
   multiline signatures from their modules. Verdict: pass.

Second-reading changes: one proof-only import visibility correction; verbatim
new-node signature records; complete old-dependency accounting in this report.
The proofs themselves needed no repair. Closed original holes: one; added
holes: zero; no decomposition.
