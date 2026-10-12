## What changed

Proved the original declaration
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_monodromy_trivializing_torsor`
without changing its signature, universes, hypotheses, or docstring.

The proof first uses `finite_locally_constant_module_values_iff` and
`lisseModuleSheaf_iff_underlying_finiteLocallyConstant` to obtain a finite locally
constant underlying set sheaf. A connected set-monodromy torsor makes this sheaf
constant after inverse image. A separate module reflection theorem supplies the
module constant-sheaf witness on the connected total space. The proof then uses
`IsFiniteSheaf.upperStar`, `IsFiniteSheaf.of_iso`, and the existing
`moduleFinite_of_isFiniteSheaf_constantSheaf` to prove finite-dimensionality and
assembles the original existential conclusion.

Added two modules, each with one public intermediate theorem. They are distinct
parts of the argument: the first concerns arbitrary finite sheaves of sets and
constructs the geometric torsor; the second concerns arbitrary module sheaves,
arbitrary commutative rings, and arbitrary scheme maps with connected source,
and lifts set constancy to module constancy. Neither is a renamed version of the
original module-sheaf theorem. Finite-dimensionality and the conversion of the
input finiteness convention are handled in the completed Lean proof.

Added five proof-only imports to the item, all used by the proof. Updated its DAG
proof, proof_deps, and proof_origin to match the reduction. No target, definition,
existing public import, or existing statement changed. All three sandbox modules
compile through lcompile.py; no non-sorry warnings remain.

## Proved and sorry left

The item's one original sorry is closed by a complete Lean reduction:
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_monodromy_trivializing_torsor`
(node `lem-weil-pbc-finite-monodromy-trivializing-torsor`). There are no direct
sorries left in the item. This is a reduction, not an unconditional closure of its
transitive axioms: it uses existing named statements which remain sorry and the
two new intermediate statements below.

The delivery leaves exactly these two new sorries, each the whole proof of its
public theorem, with its source and complete proof in words in the docstring:

- `AlgebraicGeometry.Scheme.exists_connected_torsor_constant_set_pullback`
  (`lem-weil-pbc-finite-set-monodromy-torsor`), in
  `Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor`.
- `AlgebraicGeometry.Scheme.module_pullback_isConstant_of_set_pullback`
  (`lem-weil-pbc-module-constant-of-set-pullback`), in
  `Sheaf.ConstructibleSheaf.ModuleConstantOfSetPullback`.

Edge cases: the set theorem permits an empty fibre; its monodromy group is then
trivial and the torsor is the identity. For the zero module the same construction
works, and the finite-sheaf argument proves finite-dimensionality of its value.
The module reflection statement permits zero rings and infinite modules. Its
connected-source hypothesis includes nonemptiness, which is necessary to recover
operations on a constant value. The prime-field hypothesis of the original item
ensures the coefficient ring is a field and finite. The finite module value lemma
is applied only to the nonempty connected torsor total space.

## No longer needed

No original import was removed: all five original public imports support the
unchanged statement and its instances. Each added proof import is used.

The original direct dependency `cor-galois-lisse-representations`, realized by
`Sheaf.Paper.GaloisLisseRepresentations`, is not needed by this proof. Its large
finite/adic representation correspondence is replaced by the existing underlying
finite-set characterization and the two specific geometric steps. This proof does
not request work on the integral, rational, or algebraic l-adic clauses of that
correspondence. No global unreachability is claimed: other targets may use it.

`thm-galois-fundamental` and `thm-galois-lc-etale` are still needed, in the new
finite-set torsor node, and are not pruned. The unit sk-thm-p1's locally constant
reduction route, including finite monodromy before Sylow restriction, is preserved.
No other original proof dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The module had no proof-dependency imports. Its three original DAG dependencies
state broad equivalences, but none directly states the connected set-monodromy
cover or the module inverse-image reflection used here. The Galois-lisse interface
also asks for a geometric point and fundamental-group model and bundles unrelated
adic statements. The reduction isolates the missing geometric steps rather than
restating that entire interface or proving its unrelated clauses.

The existing finite-values equivalence resolves a genuine convention mismatch:
IsFiniteLocallyConstantSheaf uses finitely generated stalks, whereas
IsLisseModuleSheaf uses finite local constant values. Over the finite coefficient
ring these conventions agree, so no statement correction is needed.

The cited Stacks sources were read in the existing local source cache: 0DV5's
finite-set correspondence and transfer of operations, and pione's Section 03SF
on connected finite Galois covers. The second helper generalizes the transfer of
operations using full faithfulness of constant set sheaves on a connected scheme;
this elaboration is marked as agent-written. Mathlib's isConstant_of_forget
supports this method but requires constant-functor full faithfulness and the
inverse-image comparison, so it is not a turnkey proof in the current interface.

## New nodes

`lem-weil-pbc-finite-set-monodromy-torsor` records the finite-set image/kernel
argument, regular transitive cover, commuting torsor action, universe transport,
and inverse-image compatibility. Its file is
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-set-monodromy-torsor.json`;
its module is `Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor`.

`lem-weil-pbc-module-constant-of-set-pullback` records the underlying-set
inverse-image comparison and transfer of module operations using connectedness.
Its file is
`dag/nodes/sec-proper-base-change/lem-weil-pbc-module-constant-of-set-pullback.json`;
its module is `Sheaf.ConstructibleSheaf.ModuleConstantOfSetPullback`.

There are no change records: no existing statement or definition was changed.

## Second reading by U2

1. **Unchanged interface: PASS.** Read the diff of the original module against the
repository. The original theorem signature is byte-for-byte identical, including
universes and all hypotheses; its docstring and five public imports are unchanged.
There are no changed definitions or change records. The only Lean differences are
the five proof-only imports and the proof replacing the original sorry.

2. **Proof and axioms: PASS as a reduction.** Compiled all three delivered modules
in import order through lcompile.py without errors or non-sorry warnings. Scratch
copies with #print axioms for each delivered theorem show exactly propext,
Classical.choice, Quot.sound and sorryAx. Removed the scratch copies afterward.
There are no forbidden declarations or hollow definitions. The original theorem
has no direct sorry; precisely the two reported new named theorems remain open.
This does not assert unconditional transitive closure.

3. **Split statements: PASS.** Read both full signatures and docstring arguments.
The finite-set statement constructs the connected torsor and permits empty fibres;
the module statement transfers operations on a connected nonempty source and
permits infinite values, zero modules and zero rings. Both are true parts of the
argument, rather than copies of the prime-field finite-dimensional conclusion.
The inverse-image comparison uses filtered neighbourhood colimits, not arbitrary
colimits of underlying sets. Connectedness makes each global section of a constant
set sheaf constant, so all scalar operations transfer even for an infinite ring.
Repeated searches with different wording using LeanFinder, Loogle and Mathlib grep,
and searched lean/ for constant-sheaf full faithfulness and pullback/forget
comparisons. Mathlib Sheaf.isConstant_of_forget still needs full faithfulness;
EtaleModulePullbackForgetNaturality compares module and abelian inverse images,
not the required set comparison and constancy reflection. Neither helper has a
turnkey existing proof that closes it in a few minutes. Each has a source, a complete
word proof and a matching node.

4. **Route and pruning: PASS.** Checked dag/units/sk-thm-p1.json, including realized;
the curve/locally-constant reduction and finite monodromy before Sylow restriction
are retained. Of the old direct proof_deps, cor-galois-lisse-representations is
pruned. thm-galois-fundamental and thm-galois-lc-etale are removed from the item's
direct dependency list but retained transitively through the finite-set helper.
Thus every old dependency absent from the new direct list is accounted for. The
five new imports supply used proof declarations. Tested removal of the new module
helper's public Adjunction import: its public signature then cannot resolve
sheafForget. Restored that required statement import; it is not proof-only.

5. **Nodes: PASS.** Checked proof_deps equals the union of the proof steps' uses for
all three nodes. The original node differs only in proof, proof_deps and
proof_origin. The two new nodes contain the required creation, source, searches,
blueprint, chapter/unit and Lean records, matching their declarations. Read the
existing finite-value, lisse-set and finite-sheaf declarations used by the reduction;
the isomorphism directions and nonempty-total-space condition are correct.

**Changes made:** added a second-reader LeanFinder search to the finite-set node,
clarified direct versus transitive pruning in this review, and recorded all five
verdicts. No final Lean changes or statement changes were necessary.
