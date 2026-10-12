## What changed
The unchanged parent theorem is reduced to its two conjuncts in new modules
`SpecAlgClosedEtaleSheafConstantCounit` and `SpecAlgClosedEtaleSheafConstantStalk`.
The second reading proved the stalk comparison directly with Mathlib's germ equality,
joint surjectivity, and coprojection naturality lemmas. Only the counit remains open.
All new imports of the parent are proof-only. Its existing public imports are unchanged.

## Proved and sorry left
`spec_algClosed_etale_sheaf_constant_stalk` is proved with only propext,
Classical.choice, and Quot.sound. The parent `spec_algClosed_etale_sheaf_constant`
has a complete conjunction proof conditional on the counit theorem, so remains
transitively dependent on sorryAx. The only sorry delivered is
`spec_algClosed_etale_sheaf_constant_counit`, node
`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant-counit`, in its own module.

## No longer needed
Removed the unused attempted import `StrictlyHenselianOpenSectionsStalk`.
Removed `ConstantSheafSetSectionsConnectedNatural` and `EtaleFibreDiscreteSeparablePoints`
from the parent; both remain in the counit module as planned geometric dependencies.
The parent's old direct proof_deps (the fibre decomposition, connected constant sections,
and four definition nodes) are replaced by the two comparison nodes. They remain
transitively needed by the counit comparison; no existing geometric module is globally pruned.
The stalk proof needs only Mathlib's EtalePoint public import, with no Sheaf lemma imports.

## Where the brief, the DAG or earlier work was wrong
The first worker's split theorem docstrings lacked the required complete proofs in words,
the parent node still described the original route, and an unused import remained.
The stalk node copied the counit geometric argument despite having a simpler direct proof.
The first worker's statement that the parent was fully proved overlooked sorryAx dependence.
These faults are repaired. The original description of the identity neighbourhood as terminal
in the pointed category is reversed: it is initial there, terminal in the opposite category.

## New nodes
`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant-counit`: one strictly smaller
conjunct, sourced to Stacks Tag 03P5, with a full geometric proof in its docstring and
its original geometry dependencies. Empty etale objects give the empty product, a singleton.
`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant-stalk`: the other conjunct,
now proved directly using the initial identity pointed neighbourhood. Its statement and
Lean record match; its proof metadata records the direct colimit argument.
No change record is needed because no existing statement or definition changed.

## Second reading by F1
1. Compared the final parent module with the repository: its theorem signature is
byte-for-byte unchanged and all public imports are unchanged. The new theorem
signatures match their DAG records and each has its own module.
2. Compiled all three delivered modules in import order with lcompile.py. Scratch
#print axioms checks show only the three permitted axioms for the stalk comparison;
the counit and parent additionally have the explicitly reported sorryAx. No forbidden
constructs or definitions with sorry occur.
3. Checked both statements mathematically. The counit is objectwise bijective by the
singleton covering and sheaf condition, including the empty object. The identity stalk
is computed by the marked lifts; the proof works even for empty section sets. Independent
leanfinder, loogle, grep searches and rg over the library found no direct counit theorem;
the stalk proof uses the Mathlib point lemmas found in the searches. The existing strictly
henselian comparison is more general geometrically and unnecessary in this special case.
4. Pruned the unused attempted import and moved the two remaining geometric dependencies
to the counit module. No unit statement or step is bypassed: sk-thm-iff realized names
the property-iff-acyclicity node, not these below-unit helper nodes. Its record is unchanged.
5. Read all three node records and the unit's realized fields. Parent proof_deps now match
its conjunction proof; the stalk node now records its direct proof and the counit retains
its geometric plan. Both new node declarations and modules agree with the Lean.

Changed: proved the stalk comparison; expanded both new theorem docstrings; moved the
new declarations into their own modules; pruned the unused import; corrected parent
and stalk proof metadata; rewrote the report to distinguish direct proofs from sorryAx.
