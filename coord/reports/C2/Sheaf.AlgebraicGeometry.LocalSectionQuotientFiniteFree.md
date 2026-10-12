## What changed

Proved `AlgebraicGeometry.exists_local_section_of_shortExact_finiteLocallyFree` in
`Sheaf.AlgebraicGeometry.LocalSectionQuotientFiniteFree` using two fully proved private
helpers. The proof chooses a member of the local basis cover containing the point,
uses `RingedSpace.module_exactness_local_lifting` to lift its finitely many generators,
intersects their neighborhoods, constructs a free-sheaf morphism from the lifts,
and verifies the quotient equation on every basis section. It then composes with
the inverse basis map and transports the section through `Scheme.Modules.overEquiv`
and `Scheme.Modules.overFunctorEquiv`. The empty basis gives U = V and the zero map;
no nonempty index hypothesis is used.

Corrected the reversed composition in the original Lean signature:
`s ≫ restrict(g) = 𝟙` is the right inverse the unchanged node states.
Change record: `coord/changes/local-section-quotient-composition.md`.
The node copy updates only its Lean record. No import changes or caller adaptations.

## Proved and sorry left

The original hole in `AlgebraicGeometry.exists_local_section_of_shortExact_finiteLocallyFree`
(node `lem-sc-local-section-quotient-finite-free`) is removed after correcting its
false stage-2 signature; the corrected theorem is fully proved. This does not claim
a proof of the original false left-inverse assertion. Both private helpers,
`section_transport` and `finite_free_lift`, are fully proved. Holes closed: one;
holes added: zero. No `sorry` remains in any delivered module.

Single-file compilation passes without warnings. Lean's axiom probe and the delivery
dry run provide the final verification. The original sole direct importer is also
compiled against the changed module without modifying it.

## No longer needed

None. All original imports are used, and all original proof dependencies remain
needed: `def-amb-finite-locally-free-module`, `def-weil-pbc-exact-sequence`,
`lem-weil-pbc-ringed-space-module-exactness-local-lifting`, and
`def-weil-sheaf-of-modules-category`. The unit route is unchanged. No new nodes,
no decomposition, and no pruned modules.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original Lean signature asserted `restrict(g) ≫ s = 𝟙`
on the middle term rather than `s ≫ restrict(g) = 𝟙` on the quotient. The projection
𝒪² → 𝒪 over Spec of a nonzero field is a counterexample to the original assertion.
The DAG statement and proof are correct. Its `reviewed_lean` note incorrectly treats
Lean's forward categorical composition as ordinary right-to-left composition.
The correction agrees with the node and the cited determinant local-splitting
argument. No downstream source uses the old declaration, so no adaptation is forced.
The source blueprint file cited by the node is absent on this machine; the complete
node statement and numbered proof were read, and the implementation follows them.
Searches: LeanFinder found only generators and free-sheaf interfaces, Loogle found
`SheafOfModules.freeHomEquiv`, and grep located the relevant Mathlib interfaces.


## Second reading by C2

1. Compared the sole delivered module and node with the repository using `diff`.
   The sole existing signature change is the declared reversal of the section equation,
   covered by `coord/changes/local-section-quotient-composition.md`. All other binders,
   universes and visibility are retained. The correction matches the unchanged mathematical
   node: categorical `s ≫ g` means `g ∘ s`. The projection from the rank-two free sheaf
   onto rank one over a field disproves the original equation. Independently ran
   `tools/downstream.py --uses`: 304 importers, no external source use of the theorem.
   No target statement or definition changes; no caller adaptation is necessary. Pass.
2. Compiled the delivered module with `lcompile.py` without errors or warnings.
   A scratch copy with `#print axioms` for the public theorem and both private helpers
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   Compiled the unmodified sole direct importer against the corrected scratch module.
   Searched the delivered source for holes and forbidden declarations: none.
   The lifts are explicitly assembled into compatible sections and a free-sheaf morphism;
   no definition chooses arbitrary data from an unproved existence theorem. Pass.
3. No statement is split off, no new public statement or node is added, and both private
   intermediate lemmas have complete proofs. Checked the finite intersection construction
   for an empty basis: its intersection is top, so U = V. In rank one and for an identity
   quotient the construction gives a right inverse. An empty scheme makes the conclusion
   vacuous. No nonzero rank, affine, or extra freeness hypothesis is introduced. Pass.
4. Independently searched LeanFinder for a local right inverse of an epimorphism onto a
   finite locally free sheaf, and searched the existing sheaf modules and Mathlib locally
   free interfaces by `rg`. Results provide generators/free-sheaf interfaces, not a shorter
   local splitting theorem. The proof uses the planned local lifting node, finite
   intersection, freeHomEquiv and natural-isomorphism transport. Every original import is
   needed for the statement or this proof; the proof-only lifting import is plain `import`.
   No original proof dependency is abandoned, so No longer needed is complete.
   Read `dag/units/sk-thm-picard-rr.json`: its realized lists are empty and unchanged;
   the determinant local-splitting route is retained. Pass.
5. Read all three node proof steps, proof_deps and proof_origin alongside the Lean.
   They describe the implemented trivialization, finite basis lifting and section
   construction. The delivered node changes only its Lean record to the corrected
   equation, consistent with the change record; mathematical statement and route remain
   unchanged. No new nodes need auditing. Pass.

Second reading changed only the misleading active `STATEMENT-DISPUTED` marker into a
historical comment (the corrected statement is true), reformatted the change record's
Old/New signatures as verbatim source excerpts, and appended this review. No proof changes
were needed. One corrected theorem is proved; zero new holes or split-off statements.
The original false assertion is not counted as proved.
