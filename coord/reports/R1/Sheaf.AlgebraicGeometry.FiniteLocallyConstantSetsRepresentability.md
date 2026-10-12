## What changed

`finiteLocallyConstant_sets_representable` now composes finite-local-value extraction
with representability from finite local values. Its signature and existing public
imports are unchanged. The two new modules are imported privately. Their public
imports are restricted to what their statements need: ConstructibleSheaf.Defs,
and Morphisms.Finite for the descent conclusion.

## Proved and sorry left

The item's sole theorem `AlgebraicGeometry.Scheme.finiteLocallyConstant_sets_representable`
has no direct sorry. This is a reduction, not an axiom-free completion: it still
uses sorryAx through the following two open intermediate theorems.

- `AlgebraicGeometry.Scheme.finiteLocallyConstant_exists_local_models`, node
  `lem-weil-pbc-finite-locally-constant-sets-local-models`.
- `AlgebraicGeometry.Scheme.finiteLocallyConstant_descent_of_local_models`, node
  `lem-weil-pbc-finite-locally-constant-sets-descent`.

Both have whole named public sorry proofs, sources and complete natural-language
proofs in their docstrings. No definitions or axioms were introduced.

## No longer needed

No original public import was removed. The new local-model module's unnecessary
Morphisms.Finite import was removed, and both new modules' broad TopologicalInvariance
imports were replaced by ConstructibleSheaf.Defs.

All three original direct proof dependencies of the item are now carried by the
new descent node: `lem-galois-constant-sheaf-sets-representable`,
`lem-galois-yoneda-fully-faithful`, and `lem-galois-descent`. They are not globally
pruned; the remaining descent argument needs them. The item's direct proof_deps
now name the two interfaces actually used in its Lean proof. No module becomes
unreachable through this change.

## Where the brief, the DAG or earlier work was wrong

The first worker's report incorrectly claimed the planned local-model and descent
declarations had no usable Lean declarations. `constantSheaf_sets_representable`
and `finiteEtaleDescent` are stated in the library, and Mathlib supplies Yoneda
full faithfulness. They do not directly match either new interface: finite local
values need geometric stalk comparison, while descent needs resizing, equivalence
of localized sites, construction of a scheme descent datum, and gluing the
presheaf isomorphism. The new descent node now retains those planned dependencies.
Neither of the new sorry interfaces was closed in this reading.

## New nodes

`lem-weil-pbc-finite-locally-constant-sets-local-models`: finite stalks upgrade
constant local values to finite sets, after discarding empty cover members.
It retains only the local-value part of the argument, with no representability
conclusion. The node is in dag/nodes/sec-proper-base-change/.

`lem-weil-pbc-finite-locally-constant-sets-descent`: finite constant values give
finite etale representability through coproduct models, Yoneda and effective
descent. It assumes explicit finite local values and has no stalk-finiteness
hypothesis; it is the remaining descent part, not a renamed copy of the item.
The node is in dag/nodes/sec-proper-base-change/. No statement-change record is
needed: every existing signature and definition is unchanged.

## Second reading by R1

1. Compared the delivered target module with the repository using diff. Its existing
   declaration signature and docstring are byte-for-byte unchanged; only its proof
   and two private imports differ. The new modules introduce only the two reported
   theorem signatures. No existing definition or target statement changed.
2. Compiled all three modules locally in import order. No errors or other warnings.
   Exactly the two reported named helper theorems contain sorry; neither module
   introduces a definition or a forbidden declaration. The scratch axiom checks
   show only propext, Classical.choice, Quot.sound and sorryAx for the target
   and each open helper. The delivery tool repeats its axiom probe.
3. Read both helper statements and tested their empty-base, empty-value, nonempty-
   member and unbounded-rank cases mathematically. Local extraction discards empty
   members (their arbitrary constant values need not be finite); on an empty base
   the empty cover suffices. Descent resizes each finite value to ULift of Fin n,
   permits n=0, and requires no quasi-compactness or uniform cardinality bound.
   Searched with LeanFinder, Loogle, Mathlib grep, and rg across the existing
   library. LeanSearch returned Internal Server Error, recorded as unavailable.
   Existing comparison/descent lemmas supply parts of the plan, not either new
   interface. The two steps are genuinely distinct parts of the original argument.
4. Reviewed from the target downward: the composition is the appropriate reduction
   given these interfaces; no direct library theorem closes it without a cycle
   through HenselianFiniteEtale. Existing public imports are preserved for their
   users, and the new modules use narrower statement imports. Every old direct
   proof dependency is accounted for above. Read dag/units/sk-thm-p1.json: this
   auxiliary node is not a realized unit statement or step, and the unit route
   and realized fields are unchanged.
5. Repaired the existing item's proof, proof_deps and proof_origin to record the
   exact two applications. Repaired the new nodes with self-contained statements
   and cited statement dependencies, expanded proof steps and their union of uses,
   honest recorded searches, blueprint ancestry, and lean_audit. The descent plan
   explicitly retains all three original proof dependencies. Lean signatures in
   the node records agree with the modules.

Changes made in this reading: expanded the new helper docstrings to complete
proofs including edge cases and universe resizing; narrowed new-module imports;
repaired DAG metadata and search records; corrected and completed this report.
The original target proof is retained.
