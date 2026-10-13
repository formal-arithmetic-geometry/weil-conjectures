## What changed

Replaced the single hole in `picardExternalCupCochain_isIso` by two natural-number
inductions on explicit, nonnegative cohomological bounds. The existing
`exists_quasicoherent_cohomology_bound` supplies bounds for X and Y. The inner
induction proves the comparison for arbitrary bounded G with F acyclic. The outer
induction then handles arbitrary bounded F with G fixed. Every induction hypothesis
quantifies over all quasi-coherent coefficients with the smaller bound, every
normalized cochain realization, and every natural degree; no cochain map is chosen
in the main proof.

Split the geometric base case and the two individual successor steps into separate
modules, each with one public named theorem, a source/proof docstring, and a new DAG
node. The base has two acyclic coefficients. A successor step requires a bound-d
induction hypothesis and treats only a coefficient with bound d+1. Neither
successor lemma is the original unbounded comparison under a different name.
The main proof actually combines these restricted statements by two inductions
and the existing finite-bound theorem. All existing signatures and public imports
are preserved. Updated the item's DAG proof to match those inductions.

## Proved and sorry left

Hole replaced: `AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso`
(`lem-sc-picard-external-cup-quasi-iso`), by a complete induction proof text.
This is a decomposition, not a completed geometric proof: one upper hole is
replaced by three strictly restricted base/successor statements. All four modules
compile using `lcompile.py`; the main theorem contains no `sorry`. The new geometric
steps remain explicit proof obligations. Net holes closed minus added: 1 - 3 = -2.

Added holes, each exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_of_acyclic`
  (`lem-sc-picard-external-cup-acyclic`), in `PicardExternalCupAcyclic`.
- `AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_shiftLeft`
  (`lem-sc-picard-external-cup-shift-left`), in `PicardExternalCupShiftLeft`.
- `AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_shiftRight`
  (`lem-sc-picard-external-cup-shift-right`), in `PicardExternalCupShiftRight`.

No other new holes or definitions. No change of an existing theorem statement.

## No longer needed

Removed proof imports from the item's module:
`AffineModuleCechComparisonNatural`, `AffineOpenModuleCohomologyVanishing`,
`LerayDegenerateSections`, `ModuleCechComparisonIsoAffine`,
`ModulePullbackAffineSections`, `QcqsCohomologyDirectSum`,
`QuasiCoherentTensorProductAffineSections`, `QuasicoherentAcyclicEmbedding`,
`CechComparisonMapNaturality`, `CechCupPullbackCompat`,
`HigherDirectImagePresheaf`, and `TensorKunnethNat` (with their original topic
prefixes). The new base/successor nodes retain these results as proof dependencies;
they are relocated in the DAG, not pruned from the mathematical argument.
The new statement modules have minimal signature imports; the maintainer restores
planned proof imports for their open obligations. No closure-pruning count is claimed.
`QuasicoherentFiniteCohomologicalDimension` remains a direct proof import.
No whole mathematical dependency node or module is claimed pruned.


Old direct `proof_deps` removed from the main node (retained in the step
arguments or their statement interfaces):

- `def-pc-fibre-product`
- `def-pc-module-pullback`
- `def-pc-scheme`
- `def-sc-field-linear-module-cohomology-operations`
- `lem-pc-leray-degenerate-sections`
- `lem-sc-cech-comparison-map-iso-affine`
- `lem-sc-cech-comparison-map-naturality`
- `lem-sc-cech-comparison-natural`
- `lem-sc-picard-affine-diagonal-intersections`
- `lem-sc-picard-cech-cup-pullback-compat`
- `lem-sc-picard-external-cup-cochain`
- `lem-sc-picard-kunneth-resolution-model`
- `lem-sc-picard-qcoh-universal-delta-embedding`
- `lem-sc-qcoh-cech-total-tensor-nat-iso`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-higher-direct-image-presheaf`
- `lem-weil-pbc-module-pullback-affine-sections`
- `lem-weil-pbc-qcqs-cohomology-direct-sum`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `pqf-def-coherent`
- `pqf-lem-affine-vanishing`

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped because the shared compiled cochain import was
missing. That import is now available. Compiling the saved reduction exposed an
instance-inference failure at `exists_quasicoherent_cohomology_bound`: the local
`X.Over` and `Y.Over` structures alone did not supply the affine-diagonal instances
in the form needed by the bound theorem. The repaired proof explicitly transports
each given instance by `change` immediately after installing its local `Over`
structure. This changes only the proof. The main proof and all three intermediate
statements now compile without warnings. The first completed dry run caught an
earlier node-generator bug: an unanchored search matched “theorem and” in the
proof docstring and recorded the declaration as `and`. All three new Lean records
now use the actual theorem declaration and its verbatim signature.

The Stacks source is not installed in this clone's literature directory. Read the
[canonical Stacks Tag 0BED page](https://stacks.math.columbia.edu/tag/0BED), including its short-exact-sequence argument,
dimension-shifting paragraph and acyclic Leray base case. The proof is the node's
existing route. The explicit degree-zero normalization and resolution transport
are documented rather than silently treated as the omitted source verification.

The least nonnegative bound is unnecessary: arbitrary nonnegative bounds suffice
for the two inductions. For the successor step, if d<p then p>0 and d+1<p+1,
so H^p of the cokernel vanishes. In particular d=0 does not force its H^0 to vanish.
The base and successor statements include zero coefficients, empty schemes, and
acyclic coefficients whose H^0 also vanishes. No finite-dimensionality assumption
is introduced. The unit's realized statement/step lists are empty; none of its
fixed route is bypassed.

## New nodes

`lem-sc-picard-external-cup-acyclic`: external cup on the constructed models when
both coefficients have no positive cohomology; source Tag 0BED's acyclic Leray
base case. Its proof records affine section identifications, the higher-direct-image
calculation, direct sums, Leray, and the degree-zero cup formula and cycle spanning.

`lem-sc-picard-external-cup-shift-left`: one successor step for the left
coefficient, using a supplied comparison for every coefficient with the smaller
bound. Source Tag 0BED's exact-sequence and dimension-shifting paragraphs.

`lem-sc-picard-external-cup-shift-right`: the corresponding successor step for
the right coefficient, with the left coefficient fixed. Same source.

Searches: LeanSearch failed with Internal Server Error (recorded unavailable);
LeanFinder returned group-cohomology and Ext exact-sequence statements, not a
matching external cup comparison. Logged Mathlib grep and local library/DAG
searches found existing bounds and embeddings but no matching base/successor
lemmas. A whole-blueprint search for Kunneth found etale/six-functor results with
other coefficients; no duplicate of these quasi-coherent comparison steps.
A fresh LeanFinder query for the geometric quasi-isomorphism returned mapping-cone,
shift, and sheaf-cohomology declarations, without a matching geometric comparison.
Loogle rejected the unqualified `IsIso` identifier; this is a query failure,
not evidence of absence. The corrected query with `CategoryTheory.IsIso` returned
six generic homology and exact-sequence lemmas, without the geometric comparison.
Local library searches found no existing base or successor
comparison theorem.
No change records or forced adaptations.

## Second reading by F1

1. **Signatures and visibility.** Compared the delivered main module with the
repository version. The existing target signature is byte-for-byte unchanged;
the proof-only imports are private imports, and the three added modules expose
only their new named theorems. Verdict: passed.

2. **Compilation and trust.** Compiled all four delivered modules with
`lcompile.py --all`; they compile without warnings. The only remaining
`sorry`s are the three explicitly named split-off theorems, and no definition
contains `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
Scratch `#print axioms` checks on all four theorems show only `propext`,
`Classical.choice`, `Quot.sound`, and the expected `sorryAx` from open
obligations. Verdict: passed.

3. **Split-off statements.** Checked the acyclic base and the left/right
successor statements against their declarations and node records. Each is a
strictly restricted step of the dimension-shifting proof, has the Stacks Tag
0BED source and a complete proof outline, and is not duplicated in the local
Lean library. A fresh LeanFinder search for the quasi-coherent sheaf Kunneth
formula returned generic sheaf cohomology and monoidal sheaf lemmas, not this
comparison. Independently read [Stacks Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
and checked the exact coefficient ladders and acyclic Leray argument. For the
successor bound, `d < p` implies `p > 0` and `d + 1 < p + 1`, so the cokernel
has bound d even when d = 0; its H^0 need not vanish. Zero coefficients,
empty schemes, and acyclic coefficients with zero H^0 cause no exception.
Verdict: passed; this delivery is a decomposition with one hole
closed and three holes added.

4. **Route and pruning.** The main proof uses the finite cohomological bound,
then the acyclic base and the two successor inductions. Removed imports are
listed above and the corresponding dependencies remain on the new step nodes.
The unit `sk-prop-av-cube` route is not bypassed by the reduction. Verdict:
passed.

5. **DAG agreement.** Checked each new node's theorem name and verbatim
signature, proof dependencies, source, and `status: split`; the main node's
proof dependencies now match the four imported declarations used by its Lean
proof. Verdict: passed.

Second reading changed only this report: added the complete old dependency-node
list and corrected the distinction between DAG dependency relocation and
actual import-closure pruning. No Lean or node repairs were necessary.
