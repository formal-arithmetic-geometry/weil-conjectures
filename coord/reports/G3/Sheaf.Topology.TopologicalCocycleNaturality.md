## What changed

Proved `CategoryTheory.topological_cocycle_naturality` in
`Sheaf.Topology.TopologicalCocycleNaturality`, with its existing signature unchanged.
Added the proof-only `import all Sheaf.Topology.TopologicalResolutionCocycleLift`
and used its already proved `CategoryTheory.exists_topological_resolution_cocycle_lift`.
Repair: removed the duplicate private `CategoryTheory.sectionEquiv_apply` and
`CategoryTheory.sectionEquiv`. The proof now imports and uses those existing private
declarations from the resolution-cocycle lift module through `import all`. This
keeps the import proof-only and changes no public signature or definition.
Removed the redundant `Mathlib.CategoryTheory.Abelian.RightDerived` import.
Updated the item's proof steps and dependency edges to match the Lean proof.

All remaining local helpers are private and proved. The terminal-section bijection is checked
from the generator hypothesis using the sheafification/free/Yoneda adjunctions.
The generic null-comparison helper factors the degree-zero component through the
source differential and inductively proves the null-homotopy equations in higher
degrees. Thus it requires exactness only of the source resolution, and injectivity
only of the target terms. The Ext comparison helper transfers boundaries through
the terminal-section bijection. The main proof combines this with resolution lifts,
the assumed cocycle formula, and Mathlib's `extMk_comp_mk₀` and `extMk_surjective`.

The existing names of the two unused proof witnesses inside the cocycle-formula
hypothesis are retained; a scoped unused-variable linter option prevents those
pre-existing binder names from generating warnings after the proof is supplied.
No public definition, public helper, statement change, or forced adaptation is added.
The public import cleanup is documented in
`coord/changes/topological-cocycle-naturality-imports.md`; the sole direct importer
already publicly imports RightDerived itself, so its interface is preserved.

Sources read: Stacks Project Tags 013P and 013S, their Section 013G null-homotopy
induction (Lemma 13.18.4), and Tag 01DZ. The local literature directory does not
contain the Stacks source files, so the official Stacks pages were read directly.
The proof follows the original argument and keeps the curve-estimate unit route.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.topological_cocycle_naturality`
(node `lem-sc-topological-cocycle-naturality`).

Holes closed: 1. Holes added: 0. Holes remaining in delivered files: 0.
This is a proof, not a decomposition. The used resolution-cocycle lift is already
proved in the library. The delivered module compiles without errors or warnings
using the prescribed local compiler. The unchanged direct importer
`Sheaf.Topology.TopologicalInducedCocycleFormula` also compiles against the
delivered module; its unchanged Objectwise dependency was copied and compiled
only for this validation, then both temporary sources were removed.
Both degree-zero and positive-degree cases
are covered explicitly. No data is chosen from a holed existence theorem.

## No longer needed

Removed the duplicate local `CategoryTheory.sectionEquiv` and
`CategoryTheory.sectionEquiv_apply`; both are reused from the existing lift module.

Removed the direct import `Mathlib.CategoryTheory.Abelian.RightDerived`: the
statement and proof use the sheaf-cohomology and injective-Ext APIs instead.
This is removal of a redundant import; the Mathlib module remains transitively
available through existing imports, so no project module is claimed pruned.

Removed `def-weil-pbc-topological-inverse-image` as a direct proof dependency.
No inverse-image construction is invoked here: the already proved injective
pushforward theorem provides the required injectivity, and the terminal-section
bijection is proved directly from the generator hypothesis. That definition may
still be needed elsewhere and underneath injective preservation; it is not
claimed globally unnecessary. All other original dependency nodes remain used.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the existing private `sectionEquiv_apply`
theorem and its `sectionEquiv` definition. The original independent review missed
this duplication. Both copies are now removed; `import all` makes the existing
private declarations available to the proof. The previous second reading described
the returned version and has been removed pending a fresh independent reading.

No false statement or unusable interface was found. The original DAG argument
correctly needs only termwise injectivity of `f_*I'`, not exactness of that complex.
Mathlib's resolution-to-resolution `descHomotopy` cannot be applied to this target
complex; the delivery writes the required exact-source/injective-target boundary
argument explicitly rather than treating `f_*I'` as a resolution of `f_*G`.
The initial direct proof-dependency list omitted the existing resolution-cocycle
lift; the node now records that proved lemma, and the injective-resolution
interface used for the coefficient lifts and inductive factorization.


## Second reading by G3

1. Interface: PASS. Compared the delivered module with the repository using diff,
   and separately compared the complete existing theorem signature byte for byte.
   `CategoryTheory.topological_cocycle_naturality` has the identical signature,
   universes, visibility, hypotheses and conclusion. No existing definition changes.
   The removal of the public RightDerived import is declared in the change record;
   the sole direct importer already publicly imports RightDerived independently.
   The added `import all` is proof-only and reuses the existing private section
   equivalence instead of introducing duplicate declarations.
2. Proof and trust: PASS. Independently compiled the delivered module with the
   prescribed lcompile.py wrapper: no errors or warnings. A scratch copy with
   `#print axioms` for the main theorem, terminal_comparison_bijective,
   null_comparison_cycles, comparison_extMk_eq, and the imported
   exists_topological_resolution_cocycle_lift reports only propext,
   Classical.choice and Quot.sound for every declaration. Scanned the delivered
   source: no sorry, axiom, unsafe, opaque, implemented_by, extern or kernel-check
   bypass. No data definition is added; no unproved existence witness is chosen.
3. Split statements: PASS (none). There are no split-off statements or new holes.
   Read the three proved private helpers. The terminal comparison is a bijection
   by the existing section equivalence and restriction along an equality of opens;
   it also applies to empty spaces and the zero sheaf. The null-comparison helper
   uses only source exactness and target termwise injectivity. Its degree-zero
   branch gives zero directly; its induction gives a boundary in every positive
   degree. The Ext helper transfers that boundary through the stated bijection.
   Zero cycles and zero coefficient maps require no cancellation or nonzero
   hypotheses. Fresh leanfinder and loogle searches for augmentation-zero maps
   and null homotopies found InjectiveResolution.descHomotopyZero and associated
   helpers, whose target must itself be an injective resolution. They do not
   apply to the pushed-forward complex. Also searched the local Sheaf and
   WeilConjectures topology modules and Mathlib's homotopy/injective APIs; found
   no existing matching theorem replacing the local generalization.
4. Route and pruning: PASS. Read the main proof from the represented input class
   through coefficient lifts, matching cocycles, augmentation equality, boundary
   transfer, and extMk_comp_mk₀. No exactness of pushforward is assumed. All three
   imports are used: the public imports provide the signature's cohomology/Ext
   API and the private import provides the proved lift and section equivalence.
   `No longer needed` accounts for the only removed original proof dependency,
   def-weil-pbc-topological-inverse-image, and the redundant RightDerived import.
   No project module is claimed globally pruned. Read
   dag/units/sk-thm-curveestimate.json: its realized statement and unit route are
   unchanged; this support lemma bypasses no realized unit statement or step.
5. DAG: PASS. Compared the node with the repository. Only proof, proof_deps and
   proof_origin differ. The proof_deps are exactly the union of the recorded
   step uses, and describe the resolution API, proved cocycle lift, injective
   pushforward, and cohomology API used in Lean. The source, statement, unit,
   chapter and Lean signature record are unchanged. No new node is needed.

Changes made by this second reader: appended this independent review and recorded
fresh searches. The delivered Lean proof and node required no further repair.
Confirmed accounting: one original hole closed, zero holes added, zero remaining
holes in the delivered module; no project modules pruned.
