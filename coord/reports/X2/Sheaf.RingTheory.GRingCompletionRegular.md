## What changed

Proved `AdicCompletion.isRegular_of_isGRing` in
`lean/Sheaf/RingTheory/GRingCompletionRegular.lean`, without changing its signature.
Added proof-only imports of Mathlib's completion local-ring and completion flatness
modules. Updated the existing node's proof to match
Lean's argument; its proof dependencies are unchanged.

The proof reduces to maximal target localizations, proves the maximal-ideal extension
and residue-field bijection by representatives modulo the completion projection's
kernel, and applies the existing flat-local-completion isomorphism theorem.
It composes the target local ring's completion map with the inverse isomorphism.
The resulting triangle identifies the composite with the G-ring's regular local
completion map. The second map is flat and local, hence faithfully flat; existing
regular permanence gives the desired local regularity.

Source checked: Stacks Project Tag 0AH2,
https://stacks.math.columbia.edu/tag/0AH2, especially the displayed descent diagram.
Searches through launcher leanfinder, loogle and grep found completion flatness and
quotient tools, but no direct regularity theorem. The blueprint unit's route is kept.

## Proved and sorry left

Proved: `AdicCompletion.isRegular_of_isGRing`
(node `lem-weil-pbc-g-ring-completion-regular`), the sole original sorry.
No sorry remains in the delivered module. No new modules or sorries were introduced.

The proof uses existing staged declarations
`RingHom.isRegular_iff_localRingHom_prime_and_maximal` and
`RingHom.isRegular_of_isRegular_comp`, whose separate modules still contain sorry.
`RingHom.flat_local_completion_iso` and `AdicCompletion.isNoetherianRing` are already
proved in the library; their upstream proof dependencies remain separate work items.
This is a stage-3 proof from the named dependencies, not a claim of axiom closure.

Edge cases: the argument requires no properness assumption on I and no nontriviality
assumption on A. For I = top, or a trivial completion, the maximal-local criterion has
no maximal ideals to check. For I = bot the same representative calculation works.
The contracted ideal is prime by comap; its maximality is not needed anywhere.

## No longer needed

Removed the redundant added proof-only import
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`; its declarations are already available
through the existing imports. None of the original imports, proof dependencies,
nodes or modules were pruned.
The standalone regularity-transport step is unnecessary: the inverse completion
isomorphism identifies the composite exactly with the given regular map. There was
no separate node or imported module for that step. All original dependency nodes are
still used, directly or through their recorded Mathlib leaves.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original DAG step 4 proved
maximality of the contracted ideal, but the Lean proof only needs it to be prime;
its residue-field bijection is proved directly. Steps 7–9 were rewritten to use the
inverse completion isomorphism, as in Stacks Tag 0AH2, rather than transporting
regularity of fibres across the forward isomorphism. Statements and unit realization
are unchanged.


## Second reading by X2

1. Compared the complete Lean module and node JSON against the repository versions.
   The sole existing declaration, `AdicCompletion.isRegular_of_isGRing`, has its
   signature byte for byte unchanged: arbitrary `A : Type u`, `CommRing A`, arbitrary
   ideal `I`, and `hA : IsGRing A`, concluding regularity of the canonical map to
   `AdicCompletion I A`. No definition, public import, target statement, or additional
   module changed. Only the proof, its explanatory docstring, proof-only imports,
   and permitted node proof fields differ. Verdict: pass; no change record needed.
2. Compiled the delivered file locally without errors or warnings. A scratch copy
   with `#print axioms AdicCompletion.isRegular_of_isGRing` reports exactly `propext`,
   `sorryAx`, `Classical.choice`, and `Quot.sound`. There are no local sorries or
   forbidden declarations/attributes, and no definitions with postponed data.
   The `sorryAx` is inherited from staged dependencies, including the existing
   maximal-local criterion and regularity-descent theorem. Verdict: pass as a proof
   from existing open dependencies, not full transitive axiom closure.
3. No statements were split off, and no new declarations or nodes were introduced.
   Read the signatures of the five imported Sheaf modules. The completion-isomorphism
   theorem receives flatness, locality, the extended-maximal-ideal equality, and
   a bijective residue-field map, all supplied explicitly. The residue-field
   surjectivity argument uses maximality of q, not of its contraction p; p need
   only be prime. For I = top or a zero ring the maximal-ideal branch is empty;
   I = bot causes no division or properness assumption. Verdict: pass.
4. Read Stacks Tag 0AH2 at https://stacks.math.columbia.edu/tag/0AH2 (the local
   literature source is absent on this machine), and compared its descent diagram
   with `htriangle` and the final application of regular permanence. Searched the
   Sheaf and upstream RingTheory sources for G-rings, completion regularity, and
   `isRegular_of_isGRing`; no applicable shorter proved theorem was found.
   Inspected the Mathlib completion-flatness and completion-local-ring modules.
   The direct faithfully-flat algebra import is redundant: an independent scratch
   compile succeeds without it. Removing either completion import fails on its
   required theorem or flatness instances. The four existing proof imports supply
   the explicitly used named declarations. `dag/units/sk-thm-p1.json` and its
   `realized` statement/steps are unchanged; this argument is below the unit level
   and retains its route. Verdict: pass after removing the redundant added import.
5. Compared the node's nine proof steps with the Lean: Noetherianity and flatness;
   maximal-local reduction; kernel containment via completeness/Jacobson radical;
   representatives and ideal extension; local flat map and residue-field bijection;
   completion isomorphism; inverse-isomorphism triangle; flat local second map and
   spectrum surjectivity; descent. Every original proof dependency is still used,
   either as a Sheaf declaration or its recorded Mathlib leaf. The proof-origin
   field correctly names Tag 0AH2 and the inverse-isomorphism route. Other node
   fields are unchanged. Verdict: pass; no DAG correction required.

Second-reading changes: removed only the redundant proof-only import
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, corrected the import descriptions
above, and added this review. The proof itself required no repair.
