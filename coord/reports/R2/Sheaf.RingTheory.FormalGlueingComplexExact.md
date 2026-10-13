## What changed

Proved `RingTheory.formalGlueingComplexExact`, preserving its signature and all existing
public imports. The second reader updated its proof docstring to match the implemented route. Added three proved private helpers in the same module:
`mem_primaryComponent_iff_localizations_zero`, `formalGlueing_normalize`, and
`formalGlueing_powerFamily_descent`. Added proof-only imports of
`Mathlib.RingTheory.Finiteness.Ideal` and `Mathlib.LinearAlgebra.TensorProduct.Pi`.
Updated the existing node's proof, proof dependencies, and proof origin.

The computational route of Stacks 05EK is retained. The descent helper uses the class
of the compatible family in the ambient cokernel `M^t / range δ`, rather than building
Koszul homology. Compatibility makes this particular class ideal-power torsion.
The finite product tensor equivalence identifies its tensor as a boundary; injectivity
of the existing torsion-submodule comparison kills the class. All three helpers are
fully proved, and no new nodes or new holes are needed.

## Proved and sorry left

Closed the single original hole: `RingTheory.formalGlueingComplexExact`
(node `lem-weil-pbc-formal-glueing-complex-exact`). There are no sorries left in the
item and none added elsewhere. This is a proof from existing named dependencies,
not a decomposition. The imported `Ideal.primaryComponent_baseChange_bijective`
remains an existing holed dependency; this delivery does not claim an axiom-free
proof of the full transitive closure.

Compilation through lcompile.py passes with no warnings. The proof treats `t = 0`
uniformly: finite suprema of empty families are zero, the ambient product is zero,
and the torsion comparison for `I = 0` supplies the required lift and injectivity.
The normalization permits exponent zero; the annihilator/radical argument also
handles that case. No nonzero-generator, nonzero-ring, or nonempty-cover assumption
is added. All new helpers are private and fully proved.

## No longer needed

Removed the direct proof import `Sheaf.Paper.TorsionModuleFlatBaseChangeIso` and the
direct proof dependency `lem-weil-pbc-torsion-module-flat-base-change-iso`.
It remains transitively imported by the torsion-submodule comparison, so this does
not claim its removal from the targets' entire import closure.

The direct dependencies `lem-weil-pbc-flat-tensor-exact` and
`lem-weil-pbc-localization-module-tensor` are no longer needed by this proof.
The Koszul cycle submodule, its global annihilation, and flat preservation of its
inclusion are unnecessary: use just the torsion class in the ambient cokernel.
`lem-weil-pbc-tensor-finite-product` is retained, using piRight instead of piLeft.
The removed direct proof dependency `def-weil-pbc-flat-ring-map` remains a statement dependency; flatness is passed to
05EC(1), so no independent flatness argument is needed in this proof.
The public import `Sheaf.RingTheory.CoverModuleExact` stays: its proved
`localizationAway_map_units_of_dvd` is used in the statement and proof.
No blueprint unit realization is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original eight-step proof plan included more machinery
than needed for its Koszul-class step. Its ambient cokernel is sufficient because
only the specified compatible class, rather than every cokernel element, must be
I-power torsion. The existing 05EC(1) dependency supplies precisely the injectivity
needed for that class. Added the existing Mathlib-leaf node
`lem-weil-pbc-fg-ideal-radical-power` as a proof dependency for the annihilator
argument, avoiding manual monomial bounds and their exponent-zero edge cases.

The local literature/stacks-project/more-algebra.tex file is absent. Checked the
source's second computational proof directly at https://stacks.math.columbia.edu/tag/05EK.
No change of source statement or public API was made.

## Second reading by R2

1. **Public interface: pass.** Diffed the only delivered Lean module against the
   repository. The existing theorem signature is byte-for-byte identical; all
   existing public imports and visibility are preserved. There are no changed
   definitions, statement changes, forced adaptations, or change records.
2. **Proof and axioms: pass, relative to the existing open dependency.** Compiled
   the module locally without errors or warnings. There is no `sorry`, axiom,
   unsafe declaration, opaque declaration, foreign implementation, or holed
   definition in the delivery. A scratch copy with `#print axioms` checked the
   main theorem and each of the three private helpers. Localization/torsion
   equivalence and normalization use only propext, Classical.choice, Quot.sound.
   Descent and the main theorem additionally use sorryAx through the existing
   `Ideal.primaryComponent_baseChange_bijective`; no new hole was introduced.
3. **Split statements: pass (none).** All three helpers are proved, private, and
   strictly intermediate. Checked their arguments for t = 0, n = 0, a zero
   generator, a unit generator, and the zero ring/module. Empty products give
   zero cokernel; exponent zero makes delta diagonal and compatibility forces
   equal coordinates. No data is chosen from an unproved mere-existence theorem.
4. **Route and pruning: pass.** Read Stacks 05EK's computational proof and the
   unit sk-thm-p1, including its realized statement and steps. This node is below
   those fixed realizations; none is bypassed. Independent leanfinder search for
   module recovery from a flat extension and principal localizations found only
   local flatness criteria; loogle found no localization/primary-component
   equivalence. Also searched Mathlib and lean/Sheaf with gluing and torsion
   terminology. No existing shorter recovery theorem was found. Proof-only
   imports supply the radical-power lemma, finite-product tensor comparison,
   and torsion comparison; statement imports supply flatness, quotient maps,
   tensor scalar extension, and the overlap-unit lemma. The pruning report now
   lists every removed old proof dependency, including the flat-ring-map node
   that remains a statement dependency. Transitive pruning is not claimed.
5. **DAG: pass.** Only proof, proof_deps, proof_origin differ from the existing
   node. Read all retained dependencies and their Lean/Mathlib attachments.
   The union of the steps' uses is exactly proof_deps. The ambient cokernel,
   radical-power argument, piRight comparison, and torsion correction match
   the implemented proof. There are no new nodes to audit.

Second reading changed only documentation: replaced the obsolete eight-step
Koszul proof docstring with the actual cokernel argument, completed the removed
proof-dependency list, and appended this review. The Lean proof needed no repair.
