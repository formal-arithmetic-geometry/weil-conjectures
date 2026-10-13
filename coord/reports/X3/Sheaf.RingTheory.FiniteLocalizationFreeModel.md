## What changed

Replaced the sole sorry in `Sheaf.RingTheory.FiniteLocalizationFreeModel`,
`DerivedCategory.exists_finite_localization_free_model`, by a compiled proof.
Its statement and original docstring are unchanged. The empty family is proved
immediately using the explicit zero complex. For the general family the proof
unpacks pseudo-coherence, transfers upper cohomology bounds through the derived
isomorphisms, obtains a common bound using finiteness, proves the zero starting
approximation, and uses dependent recursion to form compatible descending stages.
It then applies a fully proved degreewise-colimit assembly theorem.

Added `Sheaf.RingTheory.StabilizedFiniteFreeTower` with a complete proof of
`DerivedCategory.exists_model_of_stabilized_finite_free_tower`. The proof builds
the diagram with `Functor.ofSequence`, proves eventual constancy in each degree
by induction, constructs its colimit, and transports finite freeness and the
upper bound along the eventually invertible inclusions. In each degree the
localized inclusion is invertible on three adjacent terms, hence a
quasi-isomorphism at that degree. Colimit factorization and cancellation prove
the localized quasi-isomorphism of the final map. No new data definition selects
an arbitrary witness of a postponed theorem: the assembly uses the colimit
universal property, and stage witnesses are used only inside an existential
proof, as in the existing `FiniteConeFreeModel` proof.

Added `Sheaf.RingTheory.FiniteLocalizationFreeStep` to isolate the only remaining
part: adjoining a single finite free term and retaining the existing higher terms.
Its hypotheses explicitly describe one bounded approximation, and its conclusion
improves that approximation by one degree. This is strictly one finite induction
step, not the infinite-model statement under a new name. The docstring supplies
the finite local cone cohomology argument, the actual denominator/torsion
clearing calculation, attachment coordinates, and the cohomology argument.

Updated the item's node to record the bound, recursive steps, and proved assembly.
All three sandbox modules compile without errors or warnings with `lcompile.py`.
The assembly also applies when localizations are zero rings. The step's empty-family
case uses zero new generators; no unit ideal or global vanishing was introduced.

## Proved and sorry left

Closed 1 original hole:
`DerivedCategory.exists_finite_localization_free_model`
(node `lem-sc-finite-localization-free-model`). Its empty-family branch is fully
proved independently of the remaining intermediate statement.

Proved the new auxiliary declaration
`DerivedCategory.exists_model_of_stabilized_finite_free_tower`
(node `lem-sc-stabilized-finite-free-tower`), with no sorry.

Added exactly 1 hole:
`DerivedCategory.exists_finite_localization_free_step`
(node `lem-sc-finite-localization-free-step`), whose entire proof is `by sorry`.
There are no holes in definitions, private helpers, or the main theorem's proof.
There are no other sorries in the delivery. This is a decomposition: one upper
hole closed and one strictly smaller hole added, net zero holes, with the common
bound, base case, recursion and assembly actually formalized. It is not claimed
as an axiom-free proof of the full mathematical result; the main theorem still
transitively depends on the one-step hole.

## No longer needed

Removed direct proof imports `Sheaf.RingTheory.ConePseudoCoherent` and
`Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent` from the main module. These
remain planned dependencies of the single-step module, which imports them;
their nodes `lem-sc-cone-pseudo-coherent` and `lem-sc-finite-cohomology` are still
needed there. Thus no existing DAG nodes or modules are claimed globally pruned.
An exploratory `Mathlib.Order.Bounds.Basic` import was removed after confirming
that the current public imports already provide the finite-range bound lemma.

The global `FiniteConeFreeModel`, `FiniteConeFreeExtension`,
`FiniteConeCycleAttachment`, and `StabilizingConeTower` route is not imported:
it requires global cone vanishing or global finite obstruction groups, absent
here. These are alternative candidates, not dependencies pruned from this item's
original plan. In particular `exists_model_of_stabilizing_cone_tower` does not
supply the needed localized-map statement; the new assembly proves precisely
that variant without additional derived-category assumptions.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies establish finite local cone cohomology but do not expose
a declaration for the one-degree denominator-clearing attachment or the final
assembly. The old steps 3 and 4 therefore could not be Lean applications of the
listed dependencies alone. This delivery states the finite step explicitly and
proves the assembly from Mathlib. No mathematical error in the statement was found.

The local literature file is absent; the source proof was checked at
https://stacks.math.columbia.edu/tag/08EE. Its induction step and finite family of
principal opens agree with the new statement. Blueprint searches for finite-free
localization and stabilizing cone towers found no blueprint statement to reuse.
The ancestor tool returned no ancestor because the remote created-item chain is
broken; the new nodes preserve the existing item's recorded ancestor
`lem-sc-finite-duality` and its via chain. The unit's realized route is unchanged.
LeanSearch returned HTTP Internal Server Error for both relevant queries; the
search records honestly mark this unavailable. LeanFinder, Loogle and scoped
Mathlib grep were also run and recorded.

## New nodes

`lem-sc-finite-localization-free-step` in
`dag/nodes/sec-picard-framework/lem-sc-finite-localization-free-step.json` records
one degree of the Tag 08EE induction, including cone finiteness and denominator
clearing. Its single new module and named theorem carry the only remaining hole.
The old cone pseudo-coherence and finite-cohomology nodes remain its dependencies.

`lem-sc-stabilized-finite-free-tower` in
`dag/nodes/sec-picard-framework/lem-sc-stabilized-finite-free-tower.json` records
the fully proved localized tower assembly. It needs no pseudo-coherence or derived
category hypothesis; its proof uses Mathlib's explicit colimit constructions and
three-term quasi-isomorphism criterion. No statement or definition was changed,
so there is no change record or forced adaptation.

## Second reading by X3

1. **Visibility and statements.** Compared all delivered modules with the repository versions. The existing declaration `DerivedCategory.exists_finite_localization_free_model` has the identical signature and docstring interface; no existing declaration was weakened or given extra hypotheses. The two added declarations are new split/assembly statements recorded by their nodes.

2. **Compilation and axioms.** Compiled all three modules with `lcompile.py --all`; they compile without errors or warnings. The proved assembly theorem has only `propext`, `Classical.choice`, and `Quot.sound` in `#print axioms`. The sole remaining `sorry` is the named, documented one-step theorem, and there are no hollow definitions or forbidden declarations.

3. **New statements.** The finite-localization step is a strict one-degree induction step: it lowers the cutoff by one while retaining the old degrees and records the required localized isomorphism, epimorphism, finite freeness, and compatibility. The stabilized-tower theorem is the degreewise colimit assembly and does not restate the main theorem. Both statements are true in the empty-family and zero-ring edge cases and are exactly what the main proof applies.

4. **Pruning and route.** The main module now imports the one-step and assembly modules privately; direct cone and finite-cohomology imports remain only in the one-step module. The node proof and `proof_deps` match the actual applications, and the unit's realized route is unchanged. No existing dependency node can be pruned globally because the one-step theorem still uses the cone and finite-cohomology results.

5. **DAG and sources.** The two added node files carry their statements, source, proof steps, dependencies, Lean records, and search records. The updated main node records the explicit empty-family branch, recursive one-step construction, and assembly application. The source is Stacks Project Tag 08EE; no conflicting upstream or Mathlib declaration was found.

Changed during this reading: added this second-reading record only; no Lean proof or statement required repair after compilation.
