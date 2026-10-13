## What changed

Proved `AlgebraicGeometry.coherentFormalModule_affine_open_sections_adic` in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineOpenSectionsAdic`, with its signature
unchanged. The proof works directly on the affine open: coherence supplies quasi-coherence
and finite type; affine multiplication ranges compute ideal powers acting on sections;
affine cokernel exactness and the defining quotient isomorphism compute the transition.
Updated the theorem docstring and its existing DAG node to this route.

The three proof imports are CoherentFiniteTypeLocallyNoetherian,
QuasicoherentFiniteTypeAffine, and Modules.IdealTimesQuasiCoherentAffineSections.
QuasiCoherentCokernelImage is available through the last `import all`; its theorem
is used but its explicit import is redundant. The two `import all` declarations use existing proved
private helpers (`finite_sections_of_finiteType`, `multiplication_range`, `product_qc`),
without copying them or changing their visibility. All helpers are used only in a theorem
proof; the public signature uses no private declarations.

LeanFinder searched finite sections of coherent modules on affine opens; Loogle searched
`Module.Finite, SheafOfModules` (zero hits); Mathlib grep searched `idealSheafPower` and
`isFiniteType_iff` (zero hits). Repository rg located the existing affine finite-type,
ideal-product, tensor, and cokernel results. These provide the shorter route.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.coherentFormalModule_affine_open_sections_adic`
(node `lem-weil-pbc-formal-module-affine-open-sections-adic`).
No holes added, no split-off statements, and no `sorry` left in this delivery.
The module compiles cleanly with the launcher against the current compiled library.
No definition, existing signature, target, or visibility changed.

## No longer needed

Removed the original proof imports:
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects`
  (`lem-weil-pbc-coherent-formal-modules-restriction-objects`).
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineSectionsAdic`
  (`lem-weil-pbc-coherent-formal-module-affine-sections-adic`).

Neither theorem nor the restriction/Spec transport argument is needed for this item.
The alternative route remains below the unit level: none of the unit's realized statements
or steps is bypassed. These modules may remain reachable through other library users;
this report claims pruning only of this item's direct proof dependencies.
The second reader also removed the redundant explicit import
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`; its theorem and DAG
dependency remain used via the ideal-product `import all`.
Trial proof imports QuasiCoherentTensorProductAffineSections and the source-library
Modules.QuasicoherentCokernel were also removed because the final proof does not use them
directly. Their results remain internal dependencies of existing proved helpers.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan is mathematically valid but its transport glue is unnecessary:
the existing ideal-product and cokernel results already quantify over arbitrary affine opens.
The public finite-type affine theorem expresses finite type on an over-site; its proved
private `finite_sections_of_finiteType` helper gives precisely the global finite-type
implication needed here. `import all` reuses this implementation without another lemma.
No disputed statement or interface correction was needed. The argument covers empty affine
opens, zero modules, zero and unit ideals, and n = 0 (power one), without extra hypotheses.


## Second reading by H2

1. PASS: diffed the sole delivered module against the repository. The existing
   theorem signature is byte for byte unchanged; there are no new declarations,
   definitions, visibility changes, or change records. Both public imports remain.
2. PASS: independently compiled the module and an axiom-check scratch copy with
   lcompile.py. `#print axioms AlgebraicGeometry.coherentFormalModule_affine_open_sections_adic`
   gives exactly propext, Classical.choice, Quot.sound, with no sorryAx. No forbidden
   declaration or sorry occurs. The quotient is a cokernel construction; the supplied
   quotient isomorphism is used only in the proof, with no arbitrary data selection.
3. PASS: no statements were split off and no holes added. Read the actual finite-section,
   multiplication-range, power-quasi-coherence, and cokernel helper statements and proofs.
   The local n = 0 case uses positive power 1; empty affines and zero/unit ideals introduce
   no extra premise. Independent repository searches for affine transitions and finite
   sections, and msearch grep for affine epi/finite-section criteria, found no shorter
   existing statement that replaces this argument. Checked the cited source paragraphs
   at https://stacks.math.columbia.edu/tag/087W and https://stacks.math.columbia.edu/tag/087X.
4. PASS after import pruning: the proof reduces directly to existing proved affine
   section results. Both original proof-dependency nodes are listed as no longer needed.
   Inspected dag/units/sk-thm-p1.json realized statements and every realized step: neither
   removed node is a unit realization, and the finite-level helper does not change that
   route. Removed the redundant explicit QuasiCoherentCokernelImage proof import;
   compilation and the axiom check still pass because import all of the ideal-product
   module already supplies it. A trial removal of CoherentFiniteTypeLocallyNoetherian
   failed with an unknown coherence criterion, so retained that required import.
5. PASS: the node changes only proof, proof_deps, and proof_origin. Its three steps
   describe the actual finite-type, multiplication-range, and cokernel/isomorphism
   argument; the four proof_deps are exactly the theorem-bearing nodes used, including
   the cokernel node still used through a transitive import. Statement and unit unchanged.

Changed only the redundant explicit proof import and this report. Closed one original
hole, added zero holes; no proof repair was needed.
