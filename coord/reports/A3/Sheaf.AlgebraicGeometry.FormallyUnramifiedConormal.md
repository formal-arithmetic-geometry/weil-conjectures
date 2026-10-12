## What changed

Replaced the original sorry of `AlgebraicGeometry.formallyUnramifiedConormal_independent`
by a reduction to the existing universal-thickening comparison, existence of a kernel
pullback comparison, and a proved uniqueness argument. The conormal definition and both
existing declaration signatures are unchanged. The new proof-only import is
`Sheaf.AlgebraicGeometry.KernelTensorPullbackIsoExists`. Its single theorem asserts
existence only; no data definition chooses an arbitrary witness of an open theorem.
All three private helpers are now used to prove uniqueness.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.formallyUnramifiedConormal_independent`.
Hole added and left: `AlgebraicGeometry.exists_kernelTensorPullbackIso`, node
`lem-weil-pbc-kernel-tensor-pullback-iso-exists`, in its own new module.
This is a decomposition (one hole closed, one added, net zero), not an axiom-free proof
of the whole result. The target module has no sorry. Its uniqueness argument and the
three private helpers are proved; the existing universal-thickening existence theorem
and the new existence theorem still contribute `sorryAx` transitively.

## No longer needed

Removed redundant proof-only imports `Sheaf.AlgebraicGeometry.TensorPullback` and
`Sheaf.AlgebraicGeometry.Thickening`; both are already available through retained public
imports. No node in the original proof_deps is discarded. In particular the first-order
thickening definition is used to extract the closed-immersion hypotheses. No formerly
reachable module is claimed pruned. No private helper is unused in the repaired proof.

## Where the brief, the DAG or earlier work was wrong

The first report incorrectly described the original TensorPullback import as public.
It was private. Its proposed import change record was unnecessary for a proof-only
import and was removed. The new theorem's signature originally asserted uniqueness
while its docstring explicitly denied that assertion; second reading removed uniqueness
from the new theorem and proved it in the original module. The earlier node's
proof_deps included the new comparison without any proof step citing it. Its proof now
records the actual reduction and the independent uniqueness argument.

## New nodes

`lem-weil-pbc-kernel-tensor-pullback-iso-exists` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-kernel-tensor-pullback-iso-exists.json`
states existence of the comparison for arbitrary closed immersions related by an
ambient isomorphism, with the normalized pullback-unit section equation. It neither
asserts existence of universal thickenings nor uniqueness of their comparisons nor
uniqueness of the module map. This is strictly a part of the original argument. The
source is the ambient-isomorphism specialization of Stacks 01R4, together with 01R3
and 0096. No interface change record is needed.

## Second reading by A3

1. Compared both delivered modules with the repository: the only existing module is
FormallyUnramifiedConormal. Its definition body and the full signatures of
`formallyUnramifiedConormal` and `formallyUnramifiedConormal_independent` are byte for
byte unchanged, including every section, restriction, and normalized unit in the
uniqueness predicate. Public imports and exposure are unchanged. The other module and
its theorem are new. Verdict: no accidental interface or target change.

2. Compiled both files in import order through lcompile.py. Inspected every declaration:
no axiom, unsafe, opaque, implemented_by, extern, sorry in data, or anonymous hole.
The only explicit sorry is the named new existence theorem. Printed axioms of both
existing declarations, the private helpers, and the new theorem in scratch copies.
Only propext, Classical.choice, Quot.sound, and the explicitly allowed transitive
sorryAx occur. Verdict: kernel-checked reduction; remaining existence hole is reported,
so no claim of a complete proof.

3. Read Stacks [01R3](https://stacks.math.columbia.edu/tag/01R3),
[01R4](https://stacks.math.columbia.edu/tag/01R4), and
[0096](https://stacks.math.columbia.edu/tag/0096). Matched common source Z, both
closed-immersion assumptions, ambient IsIso, compatibility, orientation M₂→M₁,
and the normalized unit formula. The existence proof now explicitly constructs the
kernel section maps, takes the adjoint after pushforward comparison, constructs the
inverse from inv φ, and proves inverse laws by the injective Hom bijection. Restriction
naturality supplies the formula on arbitrary W, not just affine opens. Tested the
identity comparison (identity map), identical zero ideals (zero modules), the empty
closed subscheme (zero module), and affine quotients including non-square-zero ideals:
a ring isomorphism preserving the quotient induces I₂/I₂²→I₁/I₁² with its inverse.
No nilpotence, finite type, or nonemptiness is needed. New searches used kernel transport
rather than the first worker's conormal terminology: leanfinder returned ideal-data
map/comap, loogle returned categorical kernel isomorphisms, and grep found no exact
normalized module comparison. The original LeanSearch call failed, and its node record
now says unavailable rather than inventing a successful search. Also read the existing
ClosedImmersionConormalFunctorial theorem: it supplies a morphism from pullback along
an arbitrary subscheme map and an adjoint equation, not this isomorphism and its formula;
using it requires the remaining inversion and normalized comparison argument. Verdict:
the new existence statement is true, smaller, and not a duplicate declaration.

4. Read TensorPullback, TensorPullbackAdjunction, UniversalFirstOrderThickeningExists,
and the ideal-module range/injectivity declarations. The upper proof uses the existing
comparison immediately. Its uniqueness is now a short adjunction argument, using the
first worker's previously unused helpers. Removed redundant private imports; retained
all original public dependencies. Checked dag/units/sk-thm-p1.json realized statement
and four step lists: this node is a subordinate tool, none of the realized nodes is
bypassed or changed. Verdict: the unit route is kept; no module pruning is claimed.

5. Checked both node records against the repaired Lean. The item's proof now explicitly
cites the lower existence lemma and records the kernel lift plus adjunction uniqueness.
proof_deps is exactly the union of the steps' uses, retaining every old dependency and
adding the comparison and adjunction. The new node has self-contained hypotheses,
conclusion and section formula, actual searches, source, proof steps, provenance,
blueprint parent, chapter/unit, created fields, and the verbatim new Lean signature.
Verdict: node records agree with Lean and report the remaining hole.

Changed in this reading: narrowed the new split to existence, proved uniqueness in the
original module, made all helpers useful, removed two redundant private imports and
the unnecessary change record, expanded the remaining hole's natural-language proof,
scoped the first worker’s elaboration options to individual proofs,
and repaired the node proofs, search records, signatures, and this report.
