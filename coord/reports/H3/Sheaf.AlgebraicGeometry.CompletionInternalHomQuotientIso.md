## What changed

Proved `AlgebraicGeometry.completion_internal_hom_quotient_isIso` directly. Its existing signature,
visibility and definitions are unchanged. The proof uses the upstream tensor–Hom adjunction,
Mathlib's Yoneda criterion and preservation of cokernels by tensoring. Multiplication naturality
and `formalModuleQuotient_map_zero` prove the required annihilation inside the proof.

Added only proof imports `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` and
`Mathlib.CategoryTheory.Monoidal.Closed.Braided`. The original two public imports remain because
the statement needs quotient definitions and internal Hom. Updated the existing node's proof,
proof_deps and proof_origin to this route. No interface change or change record is needed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.completion_internal_hom_quotient_isIso`.
Added zero holes. There are no `sorry`s in the delivered module and no split-off statements.
The first worker's `AlgebraicGeometry.completion_internal_hom_quotient_inverse`, its new module,
and its new node were removed from the sandbox delivery: they were equivalent to the original
item. The completed proof constructs each cokernel factorization explicitly, using no arbitrary
witness from an unproved existence theorem. The proved declaration has no transitive sorry dependency; the axiom check is recorded below.

## No longer needed

None of the original proof_deps is pruned: coherent formal quotient definitions, sheaf tensor
product and internal Hom are all used. No original module is pruned. The first worker's proposed
inverse module and node are not delivered. The temporary tensor-annihilation helper was proved
and then kept as a local `have` in the target proof, so it adds neither a module nor a DAG node.
An unnecessary explicit `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` import was
removed; its API is already available through the existing imports.

## Where the brief, the DAG or earlier work was wrong

The first worker's inverse datum merely repackaged `IsIso` as existence of a two-sided inverse.
It had the same hypotheses and full mathematical content as the item, so it was not a valid
reduction. Its node also lacked the required searches and a verbatim Lean signature.
This second reading replaced it with the actual proof and removed the proposed split.

The published [Tag 0882](https://stacks.math.columbia.edu/tag/0882) proves the completed Hom
comparison under coherence and Noetherian hypotheses, leaving this finite-level map implicit.
[Section 0EHN](https://stacks.math.columbia.edu/tag/0EHN) supplies the quotient/annihilation
setup. The elementary finite-level argument works for arbitrary modules; the existing item
correctly does not require coherence or Noetherianness. The DAG now records the tensor–Hom
route and the already-proved ideal-power factorization actually used by Lean.

## Second reading by H3

1. **Unchanged interfaces: pass.** Compared the delivered module with the repository version.
The only existing declaration is `completion_internal_hom_quotient_isIso`; its signature is
byte for byte identical, including X's universe, I, F, G, m, n, the hypothesis n ≤ m and the
precise homObjMap expression. No definition, target, attribute or visibility was changed.
The existing node's statement, stmt_deps, lean record and unit are unchanged.

2. **Kernel proof: pass.** Compiled the complete module locally through lcompile.py with no
warnings. No forbidden declarations or attributes occur and no `sorry` remains. A scratch
copy with `#print axioms AlgebraicGeometry.completion_internal_hom_quotient_isIso` checks the
axiom closure; its exact result is appended below. The factors are real cokernel.desc maps,
not data chosen from an open mere-existence theorem.

3. **Split statements: pass after repair.** Refused the equivalent inverse theorem and deleted
its module and node. No new statements are delivered. Searched with the distinct phrases
“An ideal power annihilates the tensor product source of every linear map into a module
quotient by a smaller ideal power” (LeanFinder), `"whiskerRight", "zero"` (Loogle), and
`idealModuleProduct.*tensor|tensor.*annihilat` (Mathlib grep), plus rg over both library roots.
No ready-made quotient internal-Hom isomorphism was found. The useful existing APIs are
tensorHomEquiv, formalModuleQuotient_map_zero, PreservesCokernel.iso and Yoneda. Checked n=0
(the target quotient is zero), m=n, the zero/unit ideal and zero source/target: the argument
uses only cokernel and ideal-power identities, with no excluded case or extra finiteness.

4. **Route and imports: pass.** The proof genuinely establishes injectivity by epi cancellation
and surjectivity by annihilation followed by the preserved-cokernel construction. The two
new imports are plain proof imports. All three old proof_deps remain used, so “No longer
needed” is complete. Read dag/units/sk-thm-p1.json: this item's node is below the unit's
realized statement/steps; none of those nodes or routes is bypassed or changed. Added the
existing tensor-Hom adjunction node as the tool used by the shorter node-level argument.

5. **DAG agreement: pass after repair.** The existing item's three proof steps now describe
Yoneda injectivity, tensor annihilation, and cokernel factorization/surjectivity. Their uses
union is exactly proof_deps. The tensor-Hom adjunction is implemented by the already-proved
upstream SheafOfModules.tensorHomEquiv API. formalModuleQuotient_map_zero is listed among
the declarations of def-weil-pbc-coherent-formal-module. No new nodes remain to audit.

Changes from the first reading: removed the restatement and its hole, completed the entire
proof, corrected the node's route, minimized the proof imports and fixed the empty-line linter.

Axiom check result: `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
The final single-file scratch compile, including the axiom command, completed without warnings
in 22.5 seconds. No new module is used to meet the time limit; the full argument is in the
original module.

The dry run caught an added module-level namespace opening. Removed it and used fully
qualified monoidal operations within the proof; all module-level commands now match the base.
