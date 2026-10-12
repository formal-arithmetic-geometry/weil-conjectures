## What changed

Repaired the maintainer's import-cycle return. Before editing, listed all direct
importers with grep: `Sheaf.ConstructibleSheaf.ConstantFiniteDual` and
`Sheaf.ConstructibleSheaf.DualStalk`. Neither is imported by the repaired item or
its new dependency. ConstantFiniteDual already proves its comparison by applying
nonempty_constantModuleDualIso, so importing it here cannot prove the item.

The sandbox inherited a finite-presentation reduction replacing that circular
application. This pass isolates the fully proved internal-Hom transport as the local isomorphism
eD: it maps the opposite cokernel comparison, maps kernelOpOp, and applies
PreservesKernel.iso. The final proof composes eD with the finite-matrix comparison
eF and the inverse module-dual comparison. The DAG now records this composition.
The existing theorem's signature, visibility, docstring and public imports stay
identical. No other existing module is changed.

The shared lower argument is isolated in the new module
`Sheaf.ConstructibleSheaf.ConstantFiniteMatrixDualKernel`; it imports only the
upstream definitions and categorical APIs. Both downstream dual modules can use
it without a cycle. Its single statement concerns finite free matrices, not an
arbitrary finite module. No lemma of ConstantFiniteDual is used or duplicated.

Both delivered modules compile in import order with lcompile.py --all. The whole
library's source graph, overlaid with both delivered files, has no return path for
any delivered import edge. A regression check reinstating the rejected import
finds the exact ConstantModuleDual -> ConstantFiniteDual -> ConstantModuleDual cycle.
Unchanged copies of the two direct importers are also compiled against the sandbox
compiled modules. No global build is run by this worker.

## Proved and sorry left

Closed the item's one direct hole:
`AlgebraicGeometry.Scheme.nonempty_constantModuleDualIso`
(node `lem-weil-pbc-constant-module-dual`). Its proof constructs a finite presentation
using proved Mathlib theorems, identifies its categorical cokernel, transports this
through constant sheafification and contravariant internal Hom, and identifies the
module kernel with Hom(M, Lambda) using dual-map annihilator identities.

Split off one lower named hole:
`AlgebraicGeometry.Scheme.nonempty_constantFiniteMatrixDualKernelIso`
(node `lem-weil-pbc-constant-finite-matrix-dual-kernel`). Its entire proof is `by sorry`.
This delivery is a decomposition: one upper hole closed, one lower hole added, net
zero holes. The original theorem depends on the lower theorem and is not claimed
axiom-free. No additional holes, definitions or arbitrary witness constructions
are added in this repair.

The lower lemma only compares kernels of dual maps between finite free constant
sheaves. It assumes an arbitrary commutative ring, without noetherianity or an
arbitrary finitely generated module. For m=0 or g=0 the kernel is the entire rank-n
dual; for n=0 it is zero; the zero ring and empty scheme give zero objects. The
finite-presentation and Hom(M, Lambda) identifications are fully proved above this
hole. Thus it is strictly part of the argument, not the original statement renamed.

## No longer needed

The rejected import `Sheaf.ConstructibleSheaf.ConstantFiniteDual` and its node
`lem-weil-pbc-constant-finite-dual` are not needed to prove this item. Nor is
`Sheaf.ConstructibleSheaf.DualStalk` / `lem-weil-pbc-flc-dual-stalk`. They remain
downstream users; no claim that they leave the targets' closure is made.

The inherited repair also removed the redundant proof import
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`; its instances are
available through the existing public imports. The inherited second reader removed
`Mathlib.CategoryTheory.Abelian.Opposite` and `Mathlib.Algebra.Module.FinitePresentation`
from the item, and `Mathlib.Algebra.Category.ModuleCat.Kernels` and
`Mathlib.LinearAlgebra.Dual.Defs` from the lower module. They remain absent and their
APIs are available transitively. This pass removes no further imports.

No baseline public imports are removed. The repository node has empty proof_deps;
its repaired proof_deps contains exactly the lower finite-matrix node. No realized
unit statement or step is bypassed. No module is claimed pruned from the global
closure.

## Where the brief, the DAG or earlier work was wrong

The returned proof imported its own downstream user ConstantFiniteDual, creating
an import cycle despite compilation against existing oleans. The repair uses the
finite-presentation argument and a lower finite-matrix statement with no downstream
imports. Source-graph checking, including a regression of the rejected edge, verifies
this independently of compiled oleans.

The sandbox already held an attempted repair and a second-reading section. That
section has been removed because it is not an independent review of this pass's
changed transport and composition. A new second reader must inspect the current files. No interface
changes or forced adaptations are required.

Local searches in both library roots found only downstream uses of the constant
finite-dual comparison. The nodes and searches.jsonl retain the earlier Mathlib
search results: no existing finite-matrix constant-sheaf dual comparison was found.
The unit sk-thm-p1's realized nodes do not include either delivered node, and its
statement and steps are retained unchanged.

## New nodes

`lem-weil-pbc-constant-finite-matrix-dual-kernel`, module
`Sheaf.ConstructibleSheaf.ConstantFiniteMatrixDualKernel`, isolates the finite free
transpose and constant-kernel argument from the upstream
IsFiniteLocallyConstantSheaf.ihom_unit docstring. Its proof in words identifies finite
free modules with finite biproducts, uses the unit and dual basis, checks the transpose
square on basis vectors, transports kernels, and uses left exact constant
sheafification and the categorical module kernel comparison. The node records its
matching signature, source, searches, creation fields, chapter and unit. No change
record is needed because no existing interface changes.

## Second reading by G1

1. **Visible declarations and interfaces.** Compared the delivered
`ConstantModuleDual.lean` with the repository version. The existing theorem
signature, visibility, docstring, and statement are byte-for-byte unchanged;
only proof imports and the proof body differ. The new finite-matrix module adds
only the node's declared theorem.

2. **Proof and axioms.** Compiled both delivered modules with
`lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the
named split theorem `nonempty_constantFiniteMatrixDualKernelIso`. An axioms
probe reports only the permitted axioms plus `sorryAx` propagated from that
open theorem; the upper theorem has no independent hole.

3. **Split statement.** Checked the new theorem against its node and its
finite-free edge cases (zero ranks, zero ring, and empty scheme). It is a
strictly smaller kernel comparison, has a complete proof-source docstring, and
does not restate the item theorem or duplicate an existing library declaration.

4. **Proof route and pruning.** The repaired proof uses the finite-presentation
route and the new finite-matrix comparison, with no downstream import cycle.
The unit route and realized fields are retained. The report's listed removed
imports and dependencies agree with the files and DAG node.

5. **DAG agreement.** The item node records exactly the lower theorem as its
proof dependency and the lower node records no proof dependencies; statements,
declarations, modules, and proof origins match the delivered Lean files.

Changed after this reading: appended this independent review section only;
no Lean declarations or DAG statements were changed.
