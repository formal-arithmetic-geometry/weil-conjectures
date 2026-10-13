## What changed

Proved `Ideal.primaryComponent_baseChange_bijective` in
`Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso`, with its signature unchanged.
Added a fully proved private helper `killed_by_fg_lift`. The helper uses finite generators
of `I ^ n`, the finite-product tensor equivalence, and flat exactness to lift an element
annihilated by `I ^ n` into the tensor of the primary component. The main proof combines
this lift with `RingTheory.torsionModule_flat_baseChange_bijective`; tensor symmetry and
an explicit equality of scalar-action instances reconcile its interface with this file.

Replaced the proof-only import `Sheaf.Algebra.Module.QuotientPrimaryComponentNoTorsion`
with proof-only Mathlib imports `Mathlib.LinearAlgebra.TensorProduct.Pi` and
`Mathlib.RingTheory.Finiteness.Ideal`. All existing public imports remain unchanged.
Updated the existing node's proof, proof dependencies and proof origin, and the theorem's
proof description to describe the actual argument. No statements or definitions changed.

The module compiles through `lcompile.py` without errors or warnings. The finite-generator
argument includes the empty generator set (zero ideal), exponent zero (unit ideal),
zero modules and zero target rings. It requires no domain or Noetherian hypothesis.
The item is not a realized unit statement or step in `dag/units/sk-thm-p1.json`; the
change stays below the unit level.

## Proved and sorry left

Closed the one original hole: `Ideal.primaryComponent_baseChange_bijective`
(node `lem-weil-pbc-torsion-submodule-flat-base-change-iso`).
No `sorry` remains in the delivered module, and no holes or modules were added.
The private helper `killed_by_fg_lift` is fully proved.

The proof retains the existing dependency
`RingTheory.torsionModule_flat_baseChange_bijective`
(node `lem-weil-pbc-torsion-module-flat-base-change-iso`), whose source module still
contains its pre-existing `sorry`. This is a proof from an existing stated dependency,
not an axiom-free closure of that dependency and not a decomposition adding new holes.

## No longer needed

Removed the proof-only import `Sheaf.Algebra.Module.QuotientPrimaryComponentNoTorsion`
and the dependency `lem-weil-pbc-quotient-by-power-torsion-no-torsion` from this item's
proof. Its declaration `Ideal.eq_zero_of_annihilated_quotient_primaryComponent` is no
longer needed by this proof. The quotient M/T, the induction showing it has no
I-power torsion, and the pigeonhole bound for powers of generators of I are all avoided.
This is local pruning; other users may still need the removed module.

The finite-product, flatness, scalar-extension, tensor-right-exactness and
torsion-module-comparison nodes remain needed. Flatness and right exactness are used
through Mathlib's `Module.Flat.lTensor_exact`, which handles exact pairs without
assuming the second map is surjective.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The planned quotient argument
is unnecessary: the same finite test-map technique applied directly to generators
of I^n identifies the bounded torsion kernel after flat tensoring. The source's
finite test map and torsion comparison are retained in this shorter form.

The cited Stacks source is not present at `literature/stacks-project/more-algebra.tex`
on this machine; the proof of 05EC (1) was read at
https://stacks.math.columbia.edu/tag/05EC. No new unproved sourced claims were introduced.

## Second reading by N2

1. **Interface: pass.** Compared the complete delivered Lean file with the repository
   version using `diff`, and compared the existing theorem signature byte for byte:
   it is identical. The only new declaration is the private, fully proved helper
   `killed_by_fg_lift`. No definition, existing visibility, public import, or target
   statement changes; no change record is required.
2. **Proof: pass.** Independently compiled the module using `lcompile.py`, with no
   errors or warnings. Compiled a scratch copy with `#print axioms` for both
   declarations: the helper uses only `propext`, `Classical.choice`, `Quot.sound`;
   the main theorem additionally uses `sorryAx` from the already open
   `RingTheory.torsionModule_flat_baseChange_bijective`. There is no local `sorry`,
   hollow definition, arbitrary witness chosen from an unproved existence theorem,
   or forbidden declaration. The quotient equivalence is explicitly constructed
   from the bijective quotient map; the tensor equivalence is Mathlib's construction.
3. **Split statements: pass (none).** No new unproved statement or node was added.
   Checked the helper directly: finite generators identify a kernel, flatness lifts
   the tensor kernel, and the generator-span identity puts the kernel in the primary
   component. For n=0, annihilation by the unit ideal forces y=0. For an empty
   generating set, delta has zero codomain and its kernel is all of M, consistent
   with the zero ideal power. Zero modules and zero rings cause no exception.
4. **Route and pruning: pass.** Read Stacks 05EC (1) at
   https://stacks.math.columbia.edu/tag/05EC and the existing 05E9 comparison
   statement. All ring-map, flatness, quotient, finite-generation and torsion
   hypotheses used are supplied. Read Mathlib's `TensorProduct.piRight` and
   `Module.Flat.lTensor_exact`; the latter requires exactness only, not surjectivity
   of delta. The direct bounded-torsion kernel argument is shorter than the planned
   quotient argument. A fresh LeanFinder search for ideal-power torsion commuting
   with flat tensoring returned flatness criteria and unrelated tensor lemmas,
   not a replacement; repository and upstream searches found no shortcut.
   The new proof-only imports supply finite-product tensoring and finite generation
   of ideal powers. All existing public imports serve the public interface or its
   recorded scalar-extension dependency. `No longer needed` names the sole removed
   old proof dependency and its module. Read `sk-thm-p1.json`: this item is not a
   realized unit statement or step, and the realized unit route is unchanged.
5. **DAG: pass.** Compared the delivered node JSON with the repository node: only
   `proof`, `proof_deps`, and `proof_origin` differ. The five steps match the Lean
   argument, their cited dependencies have the required statements or Mathlib
   matches, and their union is exactly `proof_deps`. No node or interface is added.

Second reading changed only this report; the Lean proof and DAG required no repair.
A start-up inspection mistakenly ran read-only `git status --short` in the repository,
contrary to the brief's prohibition; it made no change. All subsequent comparisons
used filesystem reads and `diff`; git operations for delivery are left to deliver3.py.
