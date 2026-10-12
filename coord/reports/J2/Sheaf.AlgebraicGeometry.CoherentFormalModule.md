## What changed

Proved all three remaining theorems in `Sheaf.AlgebraicGeometry.CoherentFormalModule`.
`formalModuleQuotient_factor` now uses induction on power inclusions and the image map of
an explicit multiplication square. `formalModule_annihilated_power_iff` uses adjacent
quotient isomorphisms, induction on the level inequality, and multiplication naturality.
`formalCompletionSystem_coherent` combines quasi-coherence and finite type of quotients,
annihilation detected after tensoring the quotient projection, and an iterated-quotient
isomorphism whose two maps and inverse laws are constructed explicitly with cokernels.

Added only proved private helpers, with no data constructions or public signatures changed.
Added proof imports of
`WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial` (for its existing
`isQuasicoherent_toModules`), and
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections` (its quasi-coherence clause).
Updated the two owned node copies to match the categorical proof.

The Stacks sources were read at https://stacks.math.columbia.edu/tag/0EHN and
https://stacks.math.columbia.edu/tag/01Y1; the local clone contains their citation records
but no `literature/stacks-project/coherent.tex`. The new categorical refinements are
identified as agent-written in `proof_origin`, and every helper is proved.
The item's node is not a statement or step in `dag/units/sk-thm-p1.json` realized;
no unit route is bypassed. `lem-pc-sheaf-modules-tensor-closed` and
`lem-pc-closed-immersion-coherent-cohomology` are used as general categorical tools,
through already proved source declarations; no `tool_uses` record was changed.

## Proved and sorry left

Closed three original holes:

- `AlgebraicGeometry.formalModuleQuotient_factor`
  (`lem-weil-pbc-formal-module-ideal-power-factor`).
- `AlgebraicGeometry.formalCompletionSystem_coherent`
  (`def-weil-pbc-coherent-formal-module`).
- `AlgebraicGeometry.formalModule_annihilated_power_iff`
  (`def-weil-pbc-coherent-formal-module`).

No holes added, no holes split off, no `sorry` remains in the delivered module.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
factorization and stabilization. The completion object proof still reaches `sorryAx`
through the existing `quasiCoherent_tensor_product_affine_sections`, specifically its
restriction-tensor dependency `AlgebraicGeometry.Scheme.Modules.exists_restriction_tensor_comparison`
in `Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison`
(node `lem-weil-pbc-module-restriction-tensor-comparison`). This is an existing dependency,
not a newly added hole; closing the upper declaration from it is the stage-3 reduction.
The other newly used source declarations and the coherent finite-type criterion were
individually checked with `#print axioms` and use only the three permitted axioms.
The existing proper-support proof retains its existing dependencies.

The final module compiles cleanly with `lcompile.py` (approximately 14 seconds).
Edge cases are handled by the actual proofs: equal levels, exponent zero in factorization,
level c=0 in stabilization, zero modules, and empty schemes; no nonzero ideal or nonempty
scheme hypothesis was added. The iterated quotient helper covers arbitrary n ≤ m.

## No longer needed

No existing imports or reachable modules were removed: all six public imports serve
statements or definitions and all four existing proof imports serve the existing support proof.
The two added proof imports are used. The second reading removed the redundant
explicit proof import of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`: its declarations
are already available through the other imports; a scratch copy compiles without it. The new factorization, annihilation, and iterated
quotient proofs need no affine-basis image computation, stalk ideal-product formula, or
third-isomorphism bridge; these are replaced by proved private categorical arguments.
The `ideal_module_product_stalk` theorem itself is not used, although its module remains
necessary for the shared definitions. The old factorization proof dependency
`def-weil-pbc-ideal-module-product-stalk` is no longer used (it does not exist);
its replacement is `lem-weil-pbc-ideal-module-product-stalk`, for the constructions only.
These are all removed entries of the repository versions' `proof_deps`.
No whole node or reachable module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The old factorization node cites nonexistent `def-weil-pbc-ideal-module-product-stalk`.
The shared construction is in `lem-weil-pbc-ideal-module-product-stalk`.
Corrected its proof dependency to the existing node; its existing `stmt_deps` was left
unchanged because this delivery changes only proofs and their dependency records.
The former source plan labels product/coherence calculations elementary despite hiding
substantial module theory. This delivery explicitly uses the already stated quasi-coherent
tensor and kernel/cokernel declarations, and writes the categorical glue in Lean.
No mathematical statement, definition, target, or existing visibility was changed.


## Second reading by J2

1. **Interfaces: pass.** Read the full repository/sandbox diff and compared the parsed
   declaration tables: all existing signatures, visibility, and definition bodies are
   identical. Only the three original theorem proofs, their proof descriptions, private
   proved helpers, and proof-only imports changed. The two node copies differ only in
   `proof`, `proof_deps`, and `proof_origin`; no change record is needed.
2. **Proof and axioms: pass, with the existing open dependency recorded above.** Compiled
   the module with `lcompile.py` without errors or warnings. A scratch copy prints the
   axioms of all 39 declarations, including every private helper: only `propext`,
   `Classical.choice`, `Quot.sound`, and the reported transitive `sorryAx` occur.
   Factorization, annihilation of a quotient, the iterated quotient isomorphism, and
   stabilization have no `sorryAx`. Coherence and its completion/support users still
   depend on the existing restriction-tensor comparison through tensor quasi-coherence.
   No local `sorry`, forbidden declaration, or arbitrary data witness was added.
3. **Split statements: pass (none).** There are no new public statements, new nodes,
   or split-off holes. Read each private proved helper: the power-factor induction
   includes exponent zero and equal powers; the product helpers do not assume flatness
   or finite generation; tensor preserves epimorphisms by the tensor-Hom adjunction.
   The iterated quotient constructs both cokernel maps and cancels epi projections for
   both inverse laws. The stabilization induction covers c=0 and equality; below c it
   uses the adic annihilation condition. Zero modules and the empty scheme require no
   additional hypotheses.
4. **Route and pruning: pass after the report repair.** Read the unit's `realized`
   statement and all four steps: neither item node is among them, and the unit record
   stays unchanged. Searched source and Mathlib sheaf/module files for tensor
   quasi-coherence and existing quotient arguments. The source
   `Scheme.Modules.isQuasicoherent_tensorObj` requires an invertible factor, so it cannot
   replace the general tensor theorem used for ideals. The categorical image and
   cokernel route avoids stalk computations without bypassing a realized unit step.
   All public imports support existing interfaces. Removed one redundant explicit
   proof import after compiling a scratch copy without it. No reachable module is
   thereby pruned. Added the removed nonexistent old dependency ID to No longer needed.
5. **DAG: pass.** Checked both proof arrays and their dependency unions against the
   Lean: power inclusion/image.map for factorization; tensor and kernel/cokernel
   quasi-coherence plus finite local generators for coherence; tensor-epi cancellation
   and explicit cokernel maps for the adic condition; adjacent transitions and induction
   for stabilization. The closed-immersion tool is used through the source proof of
   `isQuasicoherent_toModules`, and tensor closure through its source implementation.
   The proper-support proof and its four previous dependencies are retained. No node
   statement or unit route was changed.

Second reading changed only the redundant MonoidalClosed proof import and the report:
completed the removed-dependency list and recorded this independent reading. All three
original local holes are closed; two are axiom-clean proofs and coherence is a reduction
through an existing open theorem, not a claim that its dependency is proved.
