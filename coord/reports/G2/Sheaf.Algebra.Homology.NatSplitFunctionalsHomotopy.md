## What changed

Proved `ChainComplex.exists_nat_homotopy_equiv_of_split_functionals` directly in
`Sheaf.Algebra.Homology.NatSplitFunctionalsHomotopy`, with its signature and docstring unchanged.
The proof follows the existing node's route. It constructs the degreewise kernel projection,
proves it lands in the kernel terms, fixes those terms, and commutes with every differential.
These identities give invariant submodules, the restricted complex, its inclusion, and its
retraction. The inclusion-retraction composite is exactly identity on the restricted complex.
An explicitly constructed homotopy with sole nonzero component `-β.smulRight z` proves the
other composite homotopic to identity. The inclusion components are subtype inclusions and
therefore injective. No data is chosen from an existence theorem.

Both original public Mathlib imports remain necessary for the statement. No import was added.
A theorem-scoped `linter.unusedVariables` setting accommodates the existing unused existential
binder `g` without changing the statement. No mathematical or elaboration option changed.

The Lean compile is clean. The delivery dry run also checks the declarations' axioms.
The source was read at https://stacks.math.columbia.edu/tag/00MT because the local literature
checkout is absent. The construction implements the complement and identity summand described
there. Searches through the required `msearch.py` wrapper (LeanFinder, Loogle, grep), and local
searches in both library roots, found integer-degree constructions but no direct natural-degree
replacement. These integer-degree modules are not imported or bypassed dependencies: this
node's planned proof has no proof dependencies.

## Proved and sorry left

Closed the single original hole:
`ChainComplex.exists_nat_homotopy_equiv_of_split_functionals`
(node `lem-weil-pbc-nat-split-functionals-homotopy`).

No `sorry` remains in the module. No holes or intermediate statements were added.
This is a complete proof, not a decomposition.

The boundary case `j = 0` uses the chain shape to make off-shape differentials zero; the
outgoing shape branch at degree zero is impossible. The homotopy calculation uses
`dNext_nat`, which already handles this boundary. The proof needs no nontrivial-ring,
boundedness, finite-generation, or freeness assumption, so the zero ring and zero complementary
terms are included.

## No longer needed

None. No imports were removed. The existing node has empty `proof_deps`, and the proof follows
its kernel-complement and explicit-homotopy construction without adding dependencies. No node
or module on that route is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The local file
`literature/stacks-project/algebra.tex` is absent on this machine; the cited Stacks tag was
read online instead. The integer-indexed `restrictToSubmodules` construction cannot directly
serve this natural-indexed theorem, so its elementary restriction construction is implemented
locally for the supplied kernel terms.

## Second reading by G2

1. **Interface and accidental changes.** I compared the delivered module with the repository
version. The theorem signature, `let S` conclusion, hypotheses, and declaration name are byte
for byte unchanged. The only declaration change is the replacement of the original proof
`sorry`; the theorem-scoped linter setting suppresses the pre-existing unused existential
binder warning and does not alter the interface.

2. **Proof and trust.** The module compiles with `lcompile.py` without errors or warnings. It
contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow
definition. The construction is explicit: kernel submodules, restricted differentials, the
projection retraction, inclusion, and a single homotopy component. The only possible boundary
case is `j = 0`; the proof uses the natural chain shape to discharge the outgoing differential
there. The resulting declarations use only the permitted standard axioms (the delivery
preflight axiom scan checks this).

3. **Statements and dependencies.** The node statement and its Lean theorem agree hypothesis
by hypothesis: `hz`, `hw`, `hd`, `hdz`, `hin`, and `hout` are all used, and the conclusion gives
the stated natural-degree complex, linear equivalences, homotopy equivalence, and injective
forward components. No intermediate theorem or split-off statement was added. The node's
proof route is the explicit kernel-complement deformation retract described in its proof field;
its `proof_deps` remains empty, and both public Mathlib imports are needed by the statement.

4. **Mathematical edge cases and shortest route.** I checked the zero ring and zero modules:
the assumptions `α z = 1` and `β w = 1` force the relevant split data, while all kernel and
subtype constructions still elaborate. I also checked `j = 0`; no predecessor term is used
in the homotopy calculation, and shape makes the outgoing map zero. Searches recorded in the
worker report found no Mathlib or upstream declaration that constructs this natural-indexed
retract. The integer-indexed restriction API therefore cannot replace this direct proof.

5. **DAG/unit route and changes.** The existing node, chapter, unit, source, and blueprint
records were not changed. The proof keeps the unit's complement-and-contractible-summand route:
restriction to kernels, retraction, and explicit homotopy. No old proof dependency became
unused, no node or module can be pruned, and no change record is required.

I changed only this report by adding the required second-reader record. No Lean source,
statement, node, or import required repair.
