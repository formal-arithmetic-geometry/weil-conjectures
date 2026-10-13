## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.Modules.picard_kunneth_iso_exists with
an explicit composition of factor homology comparisons, the algebraic tensor Kunneth
map, and the geometric tensor-total comparison. The original signature and all four
public imports are unchanged. The proof lifts both scalar classes to cycles and
uses the two cycle formulas to prove the exact externalCup equation.

Added Sheaf.Algebra.Homology.TensorKunnethNat: its natural-degree tensor Kunneth
formula is fully proved from the existing integer-index tensor_kunneth. The proof
constructs the direct-sum inclusion and its left inverse, proves surjectivity by
annihilating negative-degree summands, and preserves the generator formula.

Added Sheaf.AlgebraicGeometry.PicardKunnethCechModels for the geometric part still
to be proved. This states factor cohomology comparisons and the geometric comparison
with total-complex cohomology; it does not assert the direct-sum decomposition.
The parent performs that decomposition using the separate algebraic Kunneth result.
Updated all three DAG proof records to follow these steps.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.Modules.picard_kunneth_iso_exists
(lem-sc-picard-kunneth-qcoh-iso-exists). No sorry remains in the assigned module.

Added, proved from existing named dependencies: HomologicalComplex.tensor_kunneth_nat
(lem-sc-qcoh-cech-total-tensor-nat-iso). No sorry in this new module.

Added, still sorry: AlgebraicGeometry.Scheme.Modules.picard_kunneth_cech_models
(lem-sc-picard-kunneth-cech-models). Its proof is exactly `by sorry`, and its docstring
and node give the source and the geometric proof, including the acyclic base case
and the scalar cup normalization.

This is a decomposition: one upper hole closed, one strictly geometric hole added.
The local net is zero. The existing HomologicalComplex.tensor_kunneth remains a
named dependency with its existing sorry; this delivery does not close it.

Edge cases: n=0 retains only (0,0); negative integer pairs outside the natural index
set have zero tensor factors, established in the reindexing proof. Zero complexes
are handled by the same direct-sum induction. The geometric statement retains
empty schemes and zero modules, and uses no finite-dimensionality assumption.

All three delivered modules compile together without warnings using lcompile.py.

## No longer needed

No node or module is pruned from the combined proof-dependency closure. The old
geometric dependencies remain needed by the new Cech comparison item. The old
algebraic tensor dependency remains needed by tensor_kunneth_nat. Removed the following
direct proof imports from the assigned module and relocated their uses:

- Sheaf.Algebra.Homology.TensorKunneth
- Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural
- Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
- Sheaf.AlgebraicGeometry.LerayDegenerateSections
- Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
- Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
- Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
- Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
- Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding
- Sheaf.AlgebraicGeometry.QuasicoherentFiniteCohomologicalDimension
- Sheaf.AlgebraicGeometry.TensorPullback
- Sheaf.Paper.CechComparisonMapNaturality
- Sheaf.Paper.CechCupPullbackCompat
- Sheaf.Paper.HigherDirectImagePresheaf

The assigned module now imports only TensorKunnethNat and PicardKunnethCechModels
for its proof, in addition to its unchanged public imports. The Cech-model module
has no import of TensorKunneth: its comparison precedes the algebraic decomposition.

For completeness, the old node dependencies removed from the parent’s direct
`proof_deps` are listed below. They remain in the combined dependency closure through
the geometric comparison or the natural-degree algebraic comparison; none is globally
pruned.

- def-pc-fibre-product
- def-pc-module-pullback
- def-pc-scheme
- def-sc-field-linear-module-cohomology-operations
- lem-pc-leray-degenerate-sections
- lem-sc-cech-comparison-map-iso-affine
- lem-sc-cech-comparison-map-naturality
- lem-sc-cech-comparison-natural
- lem-sc-picard-affine-diagonal-intersections
- lem-sc-picard-cech-cup-pullback-compat
- lem-sc-picard-qcoh-finite-cd
- lem-sc-picard-qcoh-universal-delta-embedding
- lem-sc-qcoh-cech-total-tensor-iso
- lem-weil-pbc-fibre-product-affine-spectra
- lem-weil-pbc-higher-direct-image-presheaf
- lem-weil-pbc-module-pullback-affine-sections
- lem-weil-pbc-qcqs-cohomology-direct-sum
- lem-weil-pbc-quasi-coherent-tensor-product-affine-sections
- pqf-def-coherent
- pqf-lem-affine-vanishing

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. The DAG's seven-step source proof separates the
geometric quasi-isomorphism from the algebraic decomposition, but the old module
had no typed bridge between those steps. The two new interfaces supply that bridge.
The tensor-total map is a quasi-isomorphism, not a degreewise isomorphism; the new
geometric statement asserts equivalences only on cohomology, as the source requires.

The repository copy of literature/stacks-project/varieties.tex is absent on this
machine. Read the source from https://stacks.math.columbia.edu/tag/0BED instead;
its affine-cover, short-exact-sequence, induction and Leray argument agrees with
the recorded plan. LeanSearch returned Internal Server Error, recorded as an
unavailable search rather than an absence claim. LeanFinder, Loogle, and local
source searches were available. No unit statement or realized step was bypassed.

## New nodes

lem-sc-qcoh-cech-total-tensor-nat-iso: natural-degree indexing and cycle formula for
nonnegative integer cochain complexes. Proved by explicit direct-sum reindexing
from lem-sc-qcoh-cech-total-tensor-iso, without adding a hole. Its source is the
zero-extension/reindexing step in the parent's Tag 0BED proof. Searches found the
integer-index theorem and Mathlib's component lemmas, used in the Lean proof.

lem-sc-picard-kunneth-cech-models: the geometric comparison in Steps 1 and 3--7 of
the parent's Tag 0BED plan, before algebraic tensor Kunneth. It supplies two complexes,
their scalar factor comparisons, and the comparison from total tensor cohomology to
product-module cohomology, normalized on tensor cycles. It has one named sorry.
The docstring explains both dimension-shifting inductions and the acyclic base case.
Searches found no existing declaration of this particular comparison. No change
record is needed because no existing statement, definition, or public import changed.

## Second reading by J3

1. Interface check: diffed the assigned module against the repository and compared
   the complete theorem signature as bytes: identical. The four existing public
   imports are identical. The other two modules are new; no definitions or existing
   signatures are changed. The parent node changes only proof, proof_deps and
   proof_origin. Verdict: no accidental interface change and no change record needed.

2. Proof check: compiled all three modules in import order with lcompile.py, without
   errors or warnings. Read the direct-sum inclusion/projection and surjectivity proof,
   then the parent’s factor transport and cycle-representative calculation. There is
   exactly one new sorry, in picard_kunneth_cech_models, and no forbidden declaration
   or hollow definition. Scratch copies with #print axioms for all three declarations
   report only propext, Classical.choice, Quot.sound and sorryAx. The latter is expected
   from tensor_kunneth and the still-open geometric comparison. Existential models are
   eliminated inside a proposition proof; no definition chooses arbitrary data from
   them. Verdict: kernel-checked decomposition, not an axiom-complete target proof.

3. Split check: read Stacks Tag 0BED, equation the project server and its dimension-shifting
   argument. The geometric statement has exactly the original field, quasi-compact,
   affine-diagonal and quasi-coherent hypotheses. It compares total-tensor cohomology
   and normalizes tensor cycles; it leaves the algebraic decomposition outside its
   conclusion. Alpha and beta identify the factors, while gamma is an equivalence on
   homology, not on complex terms. The new natural-degree statement is a specialization
   of tensor_kunneth proved by removing zero negative-degree summands. Checked n=0,
   zero complexes/modules, empty schemes and arbitrary-dimensional vector spaces.
   For the acyclic base case, complements split the complexes into degree-zero
   homology and contractible pieces. Scalar Ext comparison and the section pairing
   give the externalCup normalization. Read ModuleCechComparisonIsoAffine,
   AffineModuleCechComparisonNatural, CechCupPullbackCompat and
   PicardExternalCupScalarComparison; the last concerns only unit coefficients in
   degree one and cannot replace this all-degree comparison. Fresh LeanFinder searches
   for nonnegative grading and for product-cover quasi-isomorphisms, Loogle search
   `HomologicalComplex.homology, TensorProduct`, and rg searches in Mathlib, lean/Sheaf,
   lean/WeilConjectures and slopmaster2 found no replacement. Verdict: one true geometric
   part remains open; no split-off hole is quickly closable from an existing theorem.

4. Route/pruning check: the parent actually composes the two factor tensor equivalences,
   tensor_kunneth_nat and gamma, and proves the generator formula using surjectivity of
   homologyπ. The natural-index theorem really invokes the old tensor_kunneth. The
   geometric node retains affine comparison, exactness, both inductions and Leray.
   Proof-only imports are private; public imports of the new modules provide types
   and instances appearing in their signatures. Listed every old parent proof_deps
   entry removed directly, in addition to the fourteen relocated imports. No module
   is globally pruned. Read sk-prop-av-cube.json: realized.statement and its single
   realized step are already empty on this base, and this supporting item changes
   neither the unit nor its cube-theorem route. Verdict: route preserved below units.

5. Node check: all proof_deps equal the unions of the proof steps’ uses. The two new
   Lean statement records are verbatim matches for their declarations; chapter, unit,
   source, created, blueprint ancestry and search records are present. The parent’s
   proof steps match the implemented composition and cycle calculation. Fixed stale
   step numbers copied from the seven-step parent into the six-step geometric plan
   and spelled out the final Leray calculation rather than referring to absent steps.
   Verdict: Lean and DAG agree after that repair.

Second-reading changes: expanded the new geometric theorem’s docstring to explain
why the tensor-total source is acyclic in positive degrees in the base case; corrected
three stale references and expanded the final Leray calculation in its DAG proof; completed the explicit old-dependency list
and recorded this review. No Lean proof body, signature, definition or import changed.
The delivery closes the one assigned hole and adds one geometric hole (net zero),
with tensor_kunneth_nat additionally proved relative to its existing dependency.
