## What changed

Completed `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_charP_two`
without changing its signature, docstring, public imports, or hypotheses. The proof handles
dimension one by Artin–Schreier and dimension at most zero by the existing geometric-point
vanishing theorem, then transports to Ext cohomology.

Added the fully proved module
`Sheaf.AlgebraicGeometry.Curve.ConstantModCharPFiniteSumColimit`. Its theorem constructs the
filtered presentation of the underlying constant Λ/pΛ sheaf by finite biproducts of
`constantZMod p`, from a basis over ULift (ZMod p), Mathlib's finite-subcoproduct diagram,
and the constant-sheaf/forgetting comparison. The main proof explicitly proves finite-stage
cohomology zero and applies large filtered-colimit continuity. Both node records follow
the Lean proof. Added imports in the existing module are proof-only.

Both modules compile without warnings. Edge cases include the zero ring, zero quotient
(in particular p invertible in Λ), and arbitrary infinite bases in the coefficient universe.

## Proved and sorry left

Proved the item's sole formerly sorry declaration
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_charP_two`
(`lem-sc-c3-degree-two`). Also proved
`AlgebraicGeometry.Etale.exists_constantModSheaf_finite_sum_colimit`
(`lem-sc-constant-mod-charp-finite-sum-colimit`). No sorry remains in either delivered
module, and no unresolved theorem is split off. Existing vanishing and filtered-colimit
dependencies keep their own transitive obligations; those are not claimed closed here.

## No longer needed

None of the item's original proof imports or dependency nodes is removed: all four are
used. Finite subsets of a chosen basis realize the planned finite-subspace construction
using Mathlib's existing finite-subcoproduct theorem. No additional unresolved algebra or
sheafification nodes are needed. Tentative redundant imports of
`Mathlib.CategoryTheory.Preadditive.Biproducts`, `Mathlib.CategoryTheory.Filtered.Basic`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`, and `Mathlib.Algebra.Field.ULift`
were removed from the new module after compiling without them. No existing module is
claimed to leave the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The coefficient extension had no single
matching declaration among the four original dependencies; it is now a fully proved,
geometry-independent presentation theorem with no cohomology conclusion. The existing
node's blueprint ancestry is incomplete (`from.node = null`), although its source names
`lem-sc-c3`. The new node records that blueprint ancestor; the original ancestry fields
are unchanged because this stage owns only its proof fields.

The Mathlib leaf for constant-module underlying sheaves had noted that its universe
instances were uncompiled. This delivery constructs the comparison at precisely
ModuleCat.{u + 1} over Scheme.{u}. Explicit limit and filtered-colimit preservation,
followed by `GrothendieckTopology.instPreservesSheafification`, avoid the timeout from
bare instance search. The machine's /tmp ran out of inodes during record preparation;
using this sandbox's scratchpad for TMPDIR resolved the local temporary-file failure.

## New nodes

`lem-sc-constant-mod-charp-finite-sum-colimit` records the proved theorem in
`lean/Sheaf/AlgebraicGeometry/Curve/ConstantModCharPFiniteSumColimit.lean`. Its conclusion
is only the coefficient presentation on an arbitrary scheme; it has a complete Lean
proof from Mathlib and no sorry. The unit's Artin–Schreier route stays unchanged. Searches
are logged in searches.jsonl: LeanSearch returned Internal Server Error; Loogle/LeanFinder
and grep found component constructions. No existing public interface changes, so no
change record is needed.

## Second reading by G1

1. PASS: Compared the existing module with the repository by diff. Its declaration
   signature, variables, hypotheses, conclusion, docstring, and public imports are
   byte-for-byte unchanged. Only proof imports and the proof body changed. The new
   coefficient module introduces a new theorem, with no existing interface modified.
2. PASS: Compiled both modules in import order through lcompile.py without warnings.
   Scanned the delivered Lean files: no sorry, axiom, unsafe, opaque, implemented_by,
   extern, or kernel-check bypass. Scratch-copy #print axioms reports only propext,
   Classical.choice and Quot.sound for the coefficient theorem. The item's theorem
   additionally reports sorryAx from existing imported obligations, notably large
   filtered-colimit continuity; the delivery does not claim those obligations closed.
3. PASS: No unresolved statement is split off. Read the complete coefficient proof:
   p kills the quotient, the lifted prime field admits a basis, finite subcoproducts
   present its direct sum, and preservation plus the constant/forgetting comparison
   transports that presentation. Checked zero ring, p invertible, empty basis, empty
   finite stage, and infinite basis cases. Independent LeanFinder and grep searches
   with different wording found component constructions, not the whole presentation;
   repository searches likewise found no duplicate. The new statement has no geometric
   hypothesis and no cohomology conclusion, so it is a genuine intermediate result.
4. PASS: Read all four original proof dependencies and the unit sk-thm-p1 realized
   record. The dimension-one branch still uses Artin–Schreier; dimension at most zero
   uses the existing geometric-point theorem. Finite-stage vanishing uses additivity,
   and the final passage uses existing large filtered-colimit continuity. No unit step
   is bypassed. Public imports supply the statements; added proof imports are private.
   All original proof dependencies remain used, so No longer needed is complete.
5. PASS: Compared the old node with the repository: only proof, proof_deps and
   proof_origin change. Its three steps track the Lean proof. The new node records
   the proved coefficient theorem, source, blueprint ancestry, statement dependencies,
   proof dependencies, searches, creation information and Lean record. Its dependencies
   correspond to the existing Mathlib leaves used by the proof.

Changed no Lean proof, signature, import, or node: the first worker's implementation
passed the second reading. Added this review and independent search evidence only.
