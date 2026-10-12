## What changed

Replaced the sorry in `ChainComplex.exists_splitting_of_isUnit_entry` with a complete Lean
reduction, retaining its exact signature. Define the split vectors and coordinate functionals
explicitly from the unit entry, prove normalization and both neighboring-differential
compatibilities, and transfer bases and rank equations to the resulting complementary complex.
Added `Sheaf.LinearAlgebra.KernelBasisOfUnitValue`, whose kernel-basis theorem is fully proved
by a bijective off-pivot coordinate map, and
`Sheaf.Algebra.Homology.SplitIdentityFromFunctionals`, which states only the complex assembly
part of Stacks 00MT. Updated the parent DAG proof and added a node for each new theorem.
All proof imports are non-public. No existing signature, visibility, or definition changed.
The second reader narrowed the new kernel module's public Mathlib import from
`FreeModule.Basic` to `Basis.Defs`; its proof-only `Pi` import remains non-public.

## Proved and sorry left

Closed the original hole in `ChainComplex.exists_splitting_of_isUnit_entry`
(`lem-weil-pbc-free-complex-unit-entry-splits`). This is a decomposition into one remaining
assembly hole, rather than an unconditional proof of the whole cancellation theorem.
Fully proved `Module.Basis.exists_basis_ker_of_isUnit_value`
(`lem-weil-pbc-kernel-basis-unit-value`); it has no sorry dependencies.

Added exactly one hole, and the only sorry in the delivery:
`ChainComplex.exists_splitting_of_split_functionals`
(`lem-weil-pbc-split-identity-from-functionals`). Its statement has no finite bases, no unit
matrix coefficients and no rank assertions: it assembles the two complexes after the split
functionals and neighboring-differential conditions have already been supplied. The original
module proves those conditions and separately proves finite freeness and every rank equation.
The remaining proof is exactly `:= by sorry`, with source and complete construction in words.

Hole accounting: one original hole closed, one assembly hole added, net zero.
The original cancellation theorem still depends on the assembly hole; the fully proved
kernel-basis lemma is a separate closed intermediate result.

All three files compile without warnings through `lcompile.py --all`.
Edge cases checked: the kernel coordinate proof works over the zero ring and at rank one;
a rank-zero pivot is excluded by `p : Fin n`. The two integer degrees are distinct by omega.
The assembly construction uses no nontriviality, field, projectivity, or freeness assumption:
its split functionals directly give the displayed inverse decompositions, including over
the zero ring and for arbitrary ambient modules.

## No longer needed

Removed `import Sheaf.LinearAlgebra.TriangularChangeOfBasis`.
`lem-weil-pbc-triangular-change-of-basis` and module
`Sheaf.LinearAlgebra.TriangularChangeOfBasis` are not needed anywhere in this proof's route:
coordinate elimination proves the finite kernel bases directly.
Retained the Mathlib statement imports and the two definition nodes
`def-weil-pbc-free-module` and `def-weil-pbc-direct-sum-modules`.
No other original proof-dependency module or node is pruned here; whether the removed module
remains reachable through other targets is for the maintainer's import-closure calculation.
The unit `sk-thm-p1` realized statements and steps are unchanged; the item realizes none of
those unit-level steps directly.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG's triangular basis lemma is an optional route,
and its purportedly elementary final assembly is substantial Lean work; that assembly is now
one explicit independent item. The earlier DAG steps remain represented by the coordinate
normalization, proved kernel calculation, proved incoming/outgoing compatibilities, and
assembly statement. Stacks 00MT was read in the local cached algebra.tex, lines 24608--24650.
LeanSearch returned Internal Server Error for both new statements; recorded as unavailable,
without a verdict, and supplemented by successful LeanFinder, Loogle and source searches.
No tools were changed and no forced adaptations were needed.

## New nodes

`lem-weil-pbc-kernel-basis-unit-value`: the kernel of a functional taking a unit value on a
finite-basis vector has a basis indexed by one fewer vector. Fully proved, including the
explicit coordinate map, injectivity, surjectivity and Fin reindexing.

`lem-weil-pbc-split-identity-from-functionals`: constructs the complementary and identity
complexes from compatible normalized split functionals and vectors. This is precisely the
restriction and assembly portion of Stacks 00MT; it leaves out pivot normalization and
finite freeness/rank computations. Its proof in words specifies the restricted maps,
zero-square checks, inverse decompositions and degreewise compatibility.

## Second reading by F3

1. **Existing interface unchanged: pass.** Read the full diff of
   `UnitEntrySplits.lean` against the repository. Its sole existing theorem signature,
   from `theorem exists_splitting_of_isUnit_entry` to the proof delimiter, is byte-identical.
   The changes are its proof, proof explanation and two non-public dependency imports.
   The other two modules are new. No existing definition, visibility, target, statement,
   or public import was changed, and no forced adaptation or change record is needed.

2. **Proof and trust boundary: pass as a decomposition.** Independently compiled all three
   modules in import order with `lcompile.py --all`, including after the import repair:
   no errors or warnings. Scanned the sources: exactly one `sorry`, the whole proof of
   `ChainComplex.exists_splitting_of_split_functionals`; no forbidden declarations or
   holed definitions. Appended `#print axioms` to temporary copies of each module.
   `Module.Basis.exists_basis_ker_of_isUnit_value` uses only `propext`, `Classical.choice`,
   `Quot.sound`. Both chain-complex theorems use these plus `sorryAx`, exactly because of
   the assembly theorem. The temporary copies were removed before delivery.
   The unit witness extracted from `hunit` and the bases extracted from the proved
   kernel theorem occur only inside a theorem proof, not in any definition of data.

3. **New statements, source and searches: pass.** Read Stacks 00MT in the local cache
   `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 24608--24650. The parent retains
   the source's finite bases, unit coefficient, identity differential and all rank clauses.
   For the kernel lemma, off-pivot coordinates are injective because the missing
   coordinate times the unit pivot value is zero; its explicit corrected inverse is
   surjective. Reindexing removes exactly one coordinate. For the assembly lemma,
   `hd` restricts the middle differential, `hin` restricts the incoming differential,
   and `hdz`/`hout` make the rank-one summand a subcomplex. The inverse decompositions
   in the docstring really have kernel components since `hz`/`hw` are one; injectivity
   follows by applying the functionals. The restricted complex inherits square-zero
   by injectivity of its inclusions. Thus every clause follows without freeness.
   Tested in words: rank zero has no pivot; rank one leaves the zero kernel;
   the zero ring makes all modules and the rank-one summand trivial; degrees `i` and
   `i-1` cannot coincide; unrelated differentials are unchanged. No field or
   nontriviality assumption was silently used. The assembly hole is strictly a part
   of cancellation: the parent proves all normalization, incoming/outgoing conditions,
   finite bases and rank arithmetic, rather than merely applying a renamed target.
   Fresh logged searches used LeanFinder for "unimodular coordinate functional ...
   free kernel of codimension one" and "cancel a contractible disk summand ...
   retraction to the scalar ring", Loogle `ChainComplex, LinearEquiv`, and grep with
   kernel/basis, disk, contractible and unimodular terminology. Also searched
   `lean/Sheaf`, `lean/WeilConjectures`, upstream algebra and Mathlib basis/homology
   sources. Field-only adapted-basis results, cylinder homotopies and short-complex
   splittings do not supply either statement over an arbitrary commutative ring.
   Both new statements have complete construction proofs in their docstrings and nodes.
   Assembly is not a few-minute closure: the dependent degreewise complex and direct-sum
   constructions remain to be formalized; no additional hole was introduced by this reading.

4. **Top-down proof, imports and pruning: pass after one import repair.** Traced the parent
   from the unit coefficient through the two kernel bases and the complex square-zero
   relation into assembly, then through basis transport and positivity of `p`/`q` into
   every rank equation. The direct coordinate argument supplies the triangular elimination
   without the original general triangular-basis lemma. `## No longer needed` names the
   sole removed original proof dependency and module. Read `dag/units/sk-thm-p1.json`:
   none of its `realized` statement/step nodes is the parent or the removed triangular
   node, and no unit-level route changes. All new proof dependencies are plain imports.
   Narrowed the kernel module's statement import to `Mathlib.LinearAlgebra.Basis.Defs`,
   which supplies its basis signature; `Mathlib.LinearAlgebra.Pi` is used only in its
   coordinate-map proof and stays a plain import. Retained the existing public statement
   imports of the parent and the three statement imports of the assembly module.

5. **DAG/Lean agreement: pass.** Compared the parent node with its repository version:
   only `proof`, `proof_deps`, `proof_origin` changed. Its five steps are the normalization,
   kernel bases, neighboring-map compatibility, assembly, and basis/rank transport in Lean.
   The dependency union is precisely the two original definition nodes plus the two new
   theorem nodes; the triangular node is removed. Read both new node records, checked
   their verbatim Lean signatures, source, proof steps and dependency unions, created/group,
   chapter/unit and blueprint ancestry. The kernel node's elementary steps are fully
   implemented; the assembly node records exactly the remaining named construction.

Changes made by this reader: narrowed the new kernel module's public basis import, removed
one extra blank line, made the report's net-zero decomposition accounting explicit, and
added this independent reading. No mathematical proof or statement needed repair.
