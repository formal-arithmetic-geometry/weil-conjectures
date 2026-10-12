## What changed

Replaced the sole sorry in
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_core` by a compiled proof
from two strictly smaller source arguments. Its signature, universes, visibility,
and conclusion are unchanged. The proof first obtains the compatible algebraization,
then extracts the original exponent, applies a quantitative bound to those fixed
witnesses, proves positivity of `4 * t`, and assembles the original conclusion.

The construction is in the new module
`Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLift` and does not
assume torsion or assert a torsion estimate. The estimate is in the new module
`Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemTorsion`: N, δ and σ
are inputs, and the conclusion is only the fixed exponent `4 * t` for δ.
Neither is a restatement of the core, and their hypotheses differ materially.
The core imports both modules privately for its proof. New nodes describe the
parts of Stacks Tag 088A that they serve and retain the original unit route.

Read https://stacks.math.columbia.edu/tag/088A and
https://stacks.math.columbia.edu/tag/0888, plus the online coherent.tex source.
The local literature checkout is absent; no source was written into the repository.
The source label for 088A is `lemma-existence-tricky`.

All three files compiled in import order through lcompile.py. No definitions,
existing interfaces, target declarations or other held modules were changed.
All statements use positive levels e+1 and n+1.

## Proved and sorry left

Closed the original declaration hole in
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_core`
(node `lem-weil-pbc-devissage-second-adic-system-core`). There is no sorry left
in the item's module.

Added two named theorem holes, each with proof exactly `:= by sorry`, source,
complete proof in words, and a separate matching node:

- `AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_lift`:
  `lem-weil-pbc-devissage-second-adic-system-lift`.
- `AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion`:
  `lem-weil-pbc-devissage-second-adic-system-torsion`.

This is a decomposition: one hole closed and two holes added, net -1 before
any effects elsewhere in the import closure. It is not an axiom-free proof
of the algebraization theorem. The new holes can be worked on independently:
the torsion theorem does not import the lifting theorem and works for any
compatible witnesses. Existing imported dependencies retain their own holes.

Edge cases checked mathematically before stating the helpers: the empty scheme
has only zero modules; K=0 reduces the lift to the supplied completion equivalence
on X, and its torsion hypothesis and conclusion are vacuous because the positive
powers of K are zero; K the unit ideal gives zero K-quotients and zero K-adic systems. For I the unit ideal,
the assumed equivalences force every K-thickening to have only zero coherent
modules. Taking M=H=0 gives the zero construction and both bounds. No case
requires exponent zero. The bound theorem keeps hthick because without
faithful completion, coherent summands outside V(I) could be invisible.

## No longer needed

Removed the core's direct proof imports
`Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence` and
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated`, replacing them with
the two new helper imports. Their nodes
`lem-weil-pbc-closed-immersion-coherent-equivalence` and
`lem-weil-pbc-formal-systems-annihilated-by-power` remain needed by the helper
proof plans and remain in the transitive import closure. They are not pruned.

Removed the redundant direct proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian` from the core; the required
declarations are already available through its imports. The new helpers likewise
compile without a duplicate direct import of this module.

The old proof dependency `def-weil-pbc-coherent-formal-module` is no longer a
direct step of the core proof, but remains a statement dependency, a public
import, and a proof dependency of both helpers. It is not pruned.

No module or mathematical dependency was eliminated from the targets' transitive
closure. No unit realization was bypassed. Global pruning: none.

## Where the brief, the DAG or earlier work was wrong

The original dependencies give equivalences and annihilation results, but do not
state the compatible second-ideal algebraization or the quantitative reflection
estimate for an arbitrary fixed comparison square. The two new source arguments
make these missing steps separate Lean obligations. No false statement or
interface defect was found. LeanSearch returned Internal Server Error; its actual
failed searches are recorded as unavailable, while LeanFinder and Mathlib grep
ran successfully and found no exact statements. Loogle rejected the unqualified
query Functor.IsEquivalence; that preliminary search is not used as evidence
for the new nodes.

## New nodes

`lem-weil-pbc-devissage-second-adic-system-lift`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-devissage-second-adic-system-lift.json`,
states the algebraization and comparison-square part of Tag 088A without a
torsion assumption. Its Lean file is
`lean/Sheaf/AlgebraicGeometry/GrothendieckDevissageSecondAdicSystemLift.lean`.
Its proof plan uses the existing closed-immersion equivalences and coherent formal
module definitions. Choices are through equivalences with their comparison data;
no arbitrary witness is used as data in a definition.

`lem-weil-pbc-devissage-second-adic-system-torsion`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-devissage-second-adic-system-torsion.json`,
states only the `4 * t` bound for supplied compatible witnesses. Its Lean file is
`lean/Sheaf/AlgebraicGeometry/GrothendieckDevissageSecondAdicSystemTorsion.lean`.
It records reduction, the natural scalar reverse maps, and reflection through the
thickening completion equivalence. Both nodes inherit chapter sec-proper-base-change
and unit sk-thm-p1. Whole-blueprint searches for compatible algebraization,
annihilation completion and 088A found no duplicate blueprint nodes; local searches
of both Lean roots and the DAG found no existing declarations for these parts.

The existing core node's proof, proof_deps and proof_origin now follow the actual
Lean assembly. No change record is required: no existing interface changed.


## Second reading by G1

1. **Interface check: pass.** Read the repository and delivered core side by side
   and checked their diff. The entire existing theorem signature is byte for byte
   identical, including the universal thickening hypothesis, positive indexing,
   supplied theta, its projection equation, comparison square, and existential
   uniform bound. Its universes, visibility, and three public imports are unchanged.
   There are no definition changes or forced adaptations. Checked that the existing
   node changes only its stage-3-owned fields and that no open change record names
   this module or its declaration.
2. **Proof and axioms: pass as a decomposition.** Compiled all three delivered
   files in import order with lcompile.py, without errors or warnings. The core
   obtains the same N, delta, sigma and square from the lift, extracts t from the
   original torsion assumption, and applies the bound to these fixed witnesses;
   omega proves positivity. The only delivered sorries are the two named helper
   theorems listed above, each with body `:= by sorry`. No definitions are added,
   and no arbitrary existence witness becomes definitional data. Searched all
   delivered Lean files for forbidden declarations and attributes. Scratch-copy
   `#print axioms` checks of all three theorems report exactly propext,
   Classical.choice, Quot.sound and sorryAx. This is one existing hole closed,
   two new holes added, net -1; it is not an axiom-free proof of the item.
3. **Split statements: pass.** Independently read Stacks Tags 088A and 0888 and
   the closed-immersion, formal-module and annihilation dependencies. The lift
   isolates the algebraization and natural comparison construction before the
   source chooses t, and does not claim torsion. The torsion theorem takes the
   constructed witnesses as inputs and establishes only the quantitative estimate;
   its comparison square suffices without the projection equation on theta.
   Neither helper restates the core. Both have matching nodes and source proofs
   in their docstrings. Checked empty X, K=0, K the unit ideal, I=0, and zero
   objects: positive indexing imposes no level-zero condition, and the uniform
   annihilation conclusion is valid in these cases. For I the unit ideal the
   thickening equivalence forces the coherent categories on the thickenings to
   be zero, so it does not create a spurious counterexample. Also checked the
   lowest exponent t=1 and arbitrary supplied isomorphisms in the torsion
   square: transport across module isomorphisms preserves ideal annihilation.
   New LeanFinder searches used the phrases “Lift a system of coherent sheaves
   on nilpotent closed subschemes” and “Reflect a fixed ideal annihilator bound”;
   an additional Mathlib grep used scalar/reverse-map and adic-annihilator words.
   Results included affine scheme limit lemmas and AdicCompletion.map_exact,
   which supplies an underlying exactness ingredient, but no complete helper
   statement. Searched both local Lean roots using secondAdicSystem, devissage,
   coherentFormal and quantitative-exponent words. Existing annihilation TFAE
   gives existential exponents, not the required fixed quantitative estimate;
   no direct application closes either helper in a few minutes.
4. **Route and pruning: pass.** The core's two private helper imports are precisely
   its two proof steps. Public imports are used in its unchanged signature.
   The helpers retain the existing closed-immersion and annihilation route, and
   the scalar reduction module supplies the explicit quantitative source argument.
   All three old proof dependencies are accounted for under No longer needed;
   none disappears from the transitive closure. Read sk-thm-p1.json, including
   realized: this core is not itself a unit statement or a realized unit step,
   and the split retains the original route beneath the unit. No unit record
   changes and no module is globally pruned.
5. **DAG agreement: pass.** Mechanically checked each node's verbatim Lean
   signature, every statement and proof dependency reference, and equality of
   proof_deps with the union of the proof steps' uses. Checked the new nodes'
   source, origin, three recorded search kinds, created record, blueprint ancestry,
   chapter, unit and complete Lean records. The core node accurately describes
   the existential assembly, with no change to its statement.

Second reading changed the torsion helper's proof docstring and its node's last
proof step to explain ideal-action image compatibility via flat Noetherian
completion, then reflection of zero by the global thickening equivalence. This
avoids relying on any unstated faithfulness of completion on individual affine
opens. Expanded No longer needed to account explicitly for the old formal-module
proof dependency, and added this independent review. No Lean signature, proof
term, import, or hole count was changed by the second reading.
