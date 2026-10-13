## What changed

Reduced `AlgebraicGeometry.RingedSpace.exists_local_internalHom_of_stalkLinearMap`
without changing its signature. The main module chooses Mathlib finite-presentation data,
lifts the generator map, proves that its composite with the relation map has zero germ
action, shrinks it to zero, and uses the preserved cokernel universal property to descend.
It delegates the final germ comparison for the already constructed descent to a
separate theorem, which uses the proved local epimorphism germ lift and stalk evaluation.

Added four modules: `FiniteFreeLocalStalkMapLift`, `FiniteFreeLocalHomZero`,
`LocalModuleEpiGermLift`, and `LocalStalkFactorizationGermComparison`.
`LocalModuleEpiGermLift` is proved using the existing source-library forgetful
colimit preservation and Mathlib local surjectivity. The two finite free steps remain as independent public statements with source, complete
proof sketches and DAG nodes. The second reader proved the final comparison.
Proof-only imports were added; every existing public import and signature is retained.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.RingedSpace.exists_local_internalHom_of_stalkLinearMap`
(node `lem-weil-pbc-stalk-linear-map-local-lift-finite-presentation`).
This is a decomposition, not a sorry-free proof of the entire dependency closure:
one upper hole is closed and two strictly smaller holes are added (net -1 hole).

Also proved `AlgebraicGeometry.RingedSpace.exists_local_module_epi_germ_lift`
(node `lem-weil-pbc-local-module-epi-germ-lift`) and
`AlgebraicGeometry.RingedSpace.exists_internalHom_of_local_stalk_factorization`
(node `lem-weil-pbc-local-stalk-factorization-germ-comparison`).
The latter was an added hole in the first worker's draft and was closed during second reading.
Both helpers have only propext, Classical.choice and Quot.sound in their axiom probes.

The final delivery leaves exactly these two new holes:

- `AlgebraicGeometry.RingedSpace.exists_finiteFree_local_stalkMap_lift`
  (node `lem-weil-pbc-finite-free-local-stalk-map-lift`).
- `AlgebraicGeometry.RingedSpace.exists_finiteFree_local_hom_zero`
  (node `lem-weil-pbc-finite-free-local-hom-zero`).

No sorry remains inside the item's proof or any private helper, and no definitions,
axioms or existing statements are changed.

## No longer needed

Removed the two original proof-only imports
`Sheaf.Algebra.Homology.ModuleStalkExact` and `Sheaf.Topology.PresheafModuleStalkFunctor`.
The added direct import `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` was redundant
and was also removed during second reading. The item imports the three refinement modules;
the comparison module imports `LocalModuleEpiGermLift` and `StalkInternalHomEvaluation`.
The five original public imports are retained, with no visible interface change.

The old proof_deps entries no longer used directly by this item's proof are
`lem-weil-pbc-module-stalk-exact`, `def-weil-pbc-module-stalk`, `def-pur-sheaf-hom`, and
`def-pc-module-stalk-functor`. The last three remain statement dependencies or are needed
by the refinement modules, and are not globally pruned. The exactness theorem is replaced
by the proved local-epimorphism helper using the upstream forgetful-colimit instance.
No claim is made that a removed module is unreachable from every other target.

The new finite-free modules use `Sheaf.Free` and `Sheaf.PushforwardContinuous` instead of
the unnecessary `Sheaf.Quasicoherent` import. The new epimorphism and comparison modules
use `Sheaf.PushforwardContinuous` instead of `Sheaf.Quasicoherent`. Duplicate imports of
`Mathlib.Geometry.RingedSpace.Basic` and `Mathlib.Algebra.Category.ModuleCat.Stalk` were
removed from all four new modules; their public ModuleStalkFunctor import supplies them.
All remaining public imports of new modules support their signatures. All proof-only
imports are plain imports.

No unit statement or realized unit step is bypassed. The item and its refinements
lie below the realized nodes of `sk-thm-p1`; that unit's record is unchanged.
No claim is made that any dependency is unreachable from all other targets.

## Where the brief, the DAG or earlier work was wrong

The original proof-dependency list consists mostly of definitions. It does not state
the two substantive finite free steps (local lifting, and simultaneous zero shrinking)
that the prose plan needs. These are now separately stated; the cokernel descent and
the factorization equation are written in Lean. The final comparison is separately
stated with the lift and descent as hypotheses, without any finiteness assumption.

The local `literature/stacks-project/modules.tex` file is absent on this machine.
Read the named source directly at `https://stacks.math.columbia.edu/tag/01CP`:
its third paragraph gives the finite-coordinate kernel argument and its second
paragraph the finite-type vanishing argument. The supplied node already expands
that argument categorically; the new nodes make those expanded steps explicit.
LeanSearch returned Internal Server Error, recorded as unavailable, not no match.

Edge cases checked: empty generator or relation index sets use the zero coproduct;
zero source/target and a trivial stalk ring are allowed; no Noetherian, scheme,
finite-generation assumption on G, or sectionwise-surjectivity assumption was added.
The epimorphism helper requires only a neighborhood of x, not a global section lift.
For a one-point space the two finite free facts are just the universal property
of a finite free module and equality of a map on its basis.

## New nodes

`lem-weil-pbc-finite-free-local-stalk-map-lift` records only lifting a stalk map after
a specified finite free local-source map; it gives no quotient descent and requires
no presentation of F. Module: `Sheaf.AlgebraicGeometry.FiniteFreeLocalStalkMapLift`.

`lem-weil-pbc-finite-free-local-hom-zero` records only simultaneous vanishing after
shrinking for a given finite free local map with zero germ action. It constructs no
lift and assumes no finite presentation. Module: `Sheaf.AlgebraicGeometry.FiniteFreeLocalHomZero`.

`lem-weil-pbc-local-module-epi-germ-lift` records the proved local lifting of section
germs through an arbitrary epimorphism on the localized site. It is used to compare
the descended map and χ and has no finiteness assumptions.
Module: `Sheaf.AlgebraicGeometry.LocalModuleEpiGermLift`.

No change records or forced adaptations are required.

`lem-weil-pbc-local-stalk-factorization-germ-comparison` takes an arbitrary local
epimorphism, an already lifted map, and an already descended factorization. It asserts
only that the descended map has the required germ action. Thus it does not restate
the original finite-presentation lifting theorem: it constructs neither of the two
input maps and has no finite presentation assumption. Module:
`Sheaf.AlgebraicGeometry.LocalStalkFactorizationGermComparison`.

## Second reading by R3

1. Compared the main Lean module and its node with the repository versions using diff.
   The sole existing public declaration's signature is byte-for-byte unchanged, as are
   its docstring and all five public imports. There are no definitions or interface
   changes, no forced adaptations, and no change records. The new private helpers are
   theorem proofs only. Verdict: unchanged mathematical contract.
2. Compiled all five delivered files in import order using lcompile.py. Inspected every
   proof and searched for forbidden declarations and sorry occurrences. Exactly the two
   named finite-free theorems retain `:= by sorry`; no definition, anonymous theorem,
   private helper, or partial proof has a hole. Scratch axiom probes show only propext,
   Classical.choice and Quot.sound for the epimorphism helper and the now-proved germ
   comparison; the item and two open finite-free facts additionally show sorryAx.
   The presentation is actual Mathlib presentation data, the cokernel descent is an
   actual construction, and no public data definition chooses an arbitrary witness of
   an unproved existence statement. Verdict: sound reduction, not closure of the item
   without assumptions on the two remaining facts.
3. Read Stacks Tag 01CP (`lemma-stalk-internal-hom`) at
   https://stacks.math.columbia.edu/tag/01CP, including the finite-type vanishing and
   finite-presentation paragraphs. The first new finite-free statement only represents
   finitely many basis images; it assumes no quotient presentation. The second only
   shrinks an already given map whose germ action is zero; it constructs no lift. Their
   conclusions hold for an empty basis, the zero ring, and zero modules. Epimorphism
   germ lifting assumes categorical epi, not sectionwise surjectivity, and chooses a
   covering member containing x. The comparison requires the already constructed psi
   and theta and has no finite-presentation assumption: it is strictly smaller than
   the item, and is now proved. Independently searched with LeanFinder for vanishing
   of a finite direct sum map and simultaneous representatives of stalk elements, with
   Loogle for overFunctorMap, and with rg in Mathlib, the repository, and upstream
   module-sheaf files. Hits supply free sections, germ criteria and restriction
   isomorphisms, not either open finite-free assertion. No duplicate or restatement
   was found. Verdict: the two remaining splits are true, needed, and strictly smaller.
4. Followed the proof from the item down: choose a finite presentation at x; use the
   free lift on generators; evaluate a relation to get chi(0) = 0; shrink the finite
   relation map; preserve its cokernel under both restrictions; descend by the actual
   cokernel universal property. In the final comparison, overFunctorMap gives the
   section phi, the proved epi helper lifts a source germ, and the proved evaluation
   formula transports equality of germs. The factorization equation evaluated on the
   lift gives the required comparison. Closed this final hole in a few minutes.
   Removed redundant imports and corrected the incomplete pruning report above.
   Checked sk-thm-p1.json realized: none of this item's refinement nodes is a realized
   unit statement or step, and the unit record is unchanged. Verdict: route retained.
5. Read every delivered JSON node against its Lean signature and docstring. The item
   proof_deps matches the three refinement calls and the presentation/restriction
   definitions. The new nodes have their source, creation, blueprint, search, lean,
   chapter and unit records. Updated the comparison node's proof and proof_origin to
   describe the now-checked restriction-isomorphism proof, and updated the item's
   proof_origin to say that only the two finite-free steps remain open. Statement
   fields and statement dependencies are unchanged. Verdict: DAG matches the proof.

Changes in this reading: proved the factorization germ comparison; minimized imports
of the four new modules; removed the redundant kernel-preservation import; corrected
both missing original-import removals and all removed old proof_deps in the report;
updated the two affected proof records. The item closes 1 of 1 original holes, adding
2 open finite-free statements; the two other new public helpers are proved outright.
