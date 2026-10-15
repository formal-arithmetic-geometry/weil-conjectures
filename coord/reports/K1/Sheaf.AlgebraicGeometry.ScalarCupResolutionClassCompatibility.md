## What changed

Corrected the missing Koszul factor in scalarCup_resolution_class_compatibility,
scalarCup_moduleCup_compatibility and scalarExternalCup_moduleComparison, and
propagated it through the two Picard scalar Cech comparison theorems, the right Cech
cycle/generator comparisons, and the cochain/homology normalization predicates.
The scalar/module formulas have (-1)^(p*q) on the right; the Cech normalization
formulas have it on the left. The constructed cochain includes the same sign on
each homology summand, and uniqueness cancels the square of that sign.

This is the coordinated correction requested by reviewer X-8bf90 at 8bf90db57.
The seven requested DAG statements, verbatim Lean signatures and statement_change
records are present. The second reader also corrected the cochain-existence and
right-Cech-homology node descriptions and the homology-uniqueness proof plan.
All edited Lean docstrings now describe the signed normalization.
The packet retains six further caller repairs from the second reader after compilation
found signed-coordinate failures, including the left generator conclusion.

The second reader removed the proposed ScalarizedModuleCupRealization module and
its new node. Its hevaluation hypothesis already identifies the evaluated value
with the paired target class; its unresolved scalar comparison repackaged the
original hole. The signed original theorem remains openly unproved. The packet
contains fifteen existing Lean modules, sixteen changed existing node records, and no new module.

PicardLeftCechCupHomology remains unchanged and omitted.
Reviewer X-67490, A3: omitted PicardExternalRightCechComparison from the delivery.
All fifteen delivered modules compiled through lcompile.py with exit 0.
Its original `hab hd n` call also compiled against that rebuilt signed dependency
overlay with exit 0 (3.9 s);
the pointwise conversion is unnecessary. This omits a sandbox copy, without
withdrawing the library module. No deleted.txt entry is needed. Change record:
coord/changes/scalar-cup-resolution-class-compatibility-route.md.

## Proved and sorry left

Holes closed: none. Holes added: none.
Removed the pre-existing private axiom
AlgebraicGeometry.Scheme.picardExternalCupCochain_h1_isIso in
PicardH1ProductSpanningBypass, replacing it with a theorem proved by
AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso at degree one.
This removes a nonstandard axiom without introducing a sorry.
This is a statement/normalization repair,
not a proof completion or decomposition. Existing downstream proofs are adapted
to the corrected formulas.

The sole remaining direct sorry in the delivered Lean files is the original named
theorem AlgebraicGeometry.Scheme.Modules.scalarCup_resolution_class_compatibility,
node new-sc-scalar-cup-resolution-class-compatibility. Its docstring supplies the
signed injective-resolution/Yoneda comparison argument. The former proposed hole
AlgebraicGeometry.Scheme.Modules.scalarized_moduleCup_realization is not delivered.
No definition contains sorry or chooses arbitrary data from an unproved existence.

## No longer needed

Removed from the original item's imports: ScalarExtCupDegreeZero,
ModuleCupShiftedUnitChainTensor, Mathlib.Algebra.Homology.BifunctorShift, and
WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex. They supported
the removed private sign diagnostics. None is a proof_deps entry of the base node;
its two original definition dependencies are retained. The proposed evaluation,
realization and scalarized bridge imports are also absent from the final item.
No proof_deps node of the original item is dropped. No whole library module is withdrawn.

The private scalarCup_yoneda_order, oddShiftTensor_component,
oddTensorSummand_ne_neg and oddShiftTensor_not_unsigned diagnostics are removed;
the sign justification is preserved in the change record and corrected proof outline.
The omitted unchanged left Cech module remains in the library.
The two ladder proofs no longer import TensorKunnethNat or directly use
lem-sc-qcoh-cech-total-tensor-nat-iso or lem-sc-picard-kunneth-resolution-model;
they call lem-sc-picard-external-cup-homology-unique instead. The right ladder
also drops the direct lem-sc-picard-external-cup-cochain dependency from its proof
plan (the statement still uses the normalization predicate).
The H1 spanning node no longer uses lem-sc-picard-kunneth-qcoh directly: the
existing bypass constructs degree-one Kunneth using the general cup invertibility
theorem, scalar models and tensor_kunneth_nat. The unit route is retained.
ProperBasic and TensorKunnethNat imports in the H1 bypass are proof-only and are
now plain imports, as required by the module convention.

## Where the brief, the DAG or earlier work was wrong

The unsigned scalar comparison omits (-1)^(p*q): scalarExtCup composes the left
class first, and extracting the left shift before the right contributes this
factor. The base's private degree-one tests verify its nontriviality over Q.
The earlier delivery corrected Lean without updating seven DAG statements; those
records now match. The second reader found two further unsigned prose descriptions
and a uniqueness proof plan that also needed the sign recorded.

The proposed scalarized bridge is not a smaller outstanding step: its supplied
evaluation formula makes its conclusion the original unresolved comparison. It is
removed rather than counted as a decomposition. Searches using Yoneda-product,
tensor-cohomology and Ext-composition terminology found general Ext APIs but no
ready-made scalar-to-module resolution comparison.

Reviewer X-67490 found that PicardExternalRightCechComparison also compiles
unchanged against the final signed dependencies. The earlier report's claim that
the pointwise conversion was forced was wrong; that module is omitted.

Reviewer X-67490, H7: the six breaking citer entries in the statement_change
records for new-sc-scalar-cup-resolution-class-compatibility,
lem-sc-scalar-cup-module-cup-compatibility,
lem-sc-scalar-external-cup-module-comparison,
lem-sc-picard-scalar-cech-external-cup-core,
lem-sc-picard-scalar-cech-external-cup, and
lem-sc-picard-right-cech-cup-cycle-comparison now say `holds: false`.
Their notes describing the coordinated signed corrections are retained verbatim.
These flags describe whether the old citer statements survive the change, not
whether the corrected statements in this delivery are valid.
All changed caller modules are unclaimed on the base; the change record lists
their coordinated interface changes.

## Forced adaptations

None. PicardExternalRightCechComparison compiles unchanged against the signed
dependency overlay and is omitted, as requested by A3. No module held by another
group is adapted. Existing theorem signatures are unchanged except the explicitly
recorded signed conclusions; the two normalization predicates have the recorded
signed correction. The H1 bypass replaces its private axiom by a theorem of the
same type and wraps its public signature without changing the type.
No target signature or definition used by Challenge.lean is changed.

## Earlier second reading (a previous round; superseded)

This is the previous reader's record, retained as history. Its claim below that
PicardExternalRightCechComparison requires adaptation is superseded by reviewer
X-67490 and the A3 repair above. A fresh second reading is still required.

1. Compared every delivered Lean module with the repository using textual diffs
and declaration signatures. The seven signed theorem conclusions and two signed
predicate bodies are declared in the change record. The additional left generator conclusion has its own statement_change record.
PicardExternalRightCechComparison is the one forced adaptation; its original compiler
error and changed lines are recorded in the change record.
Other existing public types remain identical. The H1 bypass signature is only
line-wrapped as recorded above; no hypothesis is added or conclusion weakened.
2. Compiled every delivered module through lcompile.py and inspected declaration
axioms using the delivery probe and a scratch #print axioms check. Both the original
comparison and the repaired H1 spanning result list only propext, Classical.choice,
Quot.sound and sorryAx from the listed local/imported open statements.
The only local
hole is the explicitly listed original theorem; no forbidden axiom, unsafe code,
opaque replacement or hollow definition is introduced.
3. Removed scalarized_moduleCup_realization and its new node because the supplied
evaluation characterization simply turns its remaining conclusion back into the
original comparison. No new statement is split off. Checked the sign on degree
zero, even products, characteristic two and zero classes; odd-by-odd over Q has
sign -1 as the base's proved tensor-shift diagnostics show.
4. Retained the scalar Yoneda, module cup, Cech comparison and Kunneth route.
The unit sk-prop-av-cube has empty realized lists; no realized unit statement or
step is bypassed. Removed the diagnostic-only imports and all proposed bridge
imports. No old proof_deps node is omitted from the report.
5. Checked every changed node's recorded signature against Lean, signed prose
against its coordinates, statement_change old text and all base citers, and
proof_deps against the recorded proof steps. Corrected two additional unsigned
node descriptions and the uniqueness proof plan. The original node now records
the signed comparison as still open, with no purported scalarized reduction.

Second-reading changes: remove the restating split, leave the original signed
hole honestly open, remove its proof-only bridge imports, correct signed
explanations in Lean and the additional node proof plans, repair seven additional callers, replace the pre-existing private H1 axiom with a
library theorem, and rewrite the report to claim zero holes closed and zero holes added.

## Second reading by K1

1. Compared all fifteen delivered Lean modules with the repository, including
   declaration signatures, predicate bodies, imports, visibility and options.
   Verdict: the eight signed theorem conclusions and two signed normalization
   predicate bodies are explicitly covered by the change record. The private H1
   axiom becomes a proved theorem of the same type. Other public signatures keep
   their types; the H1 signature wrapping is documented. No target changes.
   All additional caller modules are unclaimed. The six breaking citer flags
   requested by X-67490 are false, and the unchanged right Cech caller is omitted.
2. Compiled the fifteen-file delivery through lcompile.py in import order, with
   exit zero and no warnings. Independently ran #print axioms on its public
   declarations in a scratch module. Verdict: only propext, Classical.choice,
   Quot.sound and the acknowledged sorryAx occur. The cochain construction,
   signed homology uniqueness and acyclic base case have no sorryAx. There is
   exactly one direct sorry, the original named signed resolution comparison;
   no new hole, arbitrary axiom, hollow definition or forbidden implementation
   device is delivered. The delivery tool also probes every local declaration.
3. No new theorem is split off and no new node or module is delivered. Repeated
   LeanFinder and Loogle searches using Ext/cocycle/shifted-tensor terminology,
   and searched the repository with resolution and tensor-product terminology.
   Verdict: the results provide general Ext composition and injective-resolution
   APIs, not the missing scalar-to-module comparison. Checked degree zero,
   total degree one, even p*q, zero classes and characteristic two; the sign
   reduces to one where required. For odd-by-odd degrees the repository's
   checked tensor-shift diagnostics supply the negative sign. Read Stacks
   [07MB](https://stacks.math.columbia.edu/tag/07MB),
   [0FKV](https://stacks.math.columbia.edu/tag/0FKV) and
   [0BED](https://stacks.math.columbia.edu/tag/0BED) against the signed comparison
   and retained Cech/Kunneth argument. The original comparison stays openly
   unformalized; zero holes are counted as closed and zero as added.
4. Read the representative-lifting reductions, signed cochain construction,
   homology uniqueness, Cech transports, ladders and H1 spanning argument.
   Verdict: the ladder proofs already use the shorter existing uniqueness
   theorem. The report lists every removed old proof_deps edge, including the
   H1 direct geometric Kunneth dependency. No whole library module is pruned.
   The unit sk-prop-av-cube has empty realized statement and step lists; its
   unit statement and route are retained. Proof-only H1 imports are plain.
5. Checked all sixteen node records: recorded Lean signatures match after
   whitespace normalization; proof_deps is exactly the union of proof-step
   uses; changed statements retain their exact old statements and all base
   citers. The H1 node correctly remains attached to the unchanged public
   wrapper, whose proof invokes the repaired bypass. Verdict: the nodes and
   proof origins describe the delivered proofs and the sole remaining hole.

Stable-overlay consumer verification: all ten unchanged direct consumers of
the normalization predicates and H1 bypass compiled individually in import order,
including PicardExternalRightCechComparison, PicardLeftCechCupHomology,
PicardExternalCupQuasiIso and PicardH1ProductSpanning. An initial consumer check
overlapped the delivery tool rebuilding the shared sandbox artifacts and produced
a transient mismatch; both a direct predicate conversion and the complete
sequential rerun passed. No extra caller adaptation is needed.

Changes in this reading: refreshed stale maintainer-owned lean_audit fields in
all sixteen sandbox node copies from the current repository, preserving every
refreshed upstream audit. Added this independent review. No Lean proof or
statement needed a further correction. Validation artifacts and search logs
remain in the sandbox scratch directory.
