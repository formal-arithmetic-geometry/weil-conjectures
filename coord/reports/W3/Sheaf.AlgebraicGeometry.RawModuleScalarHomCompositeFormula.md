## What changed

Proved `AlgebraicGeometry.Etale.rawModuleScalar_hom_composite_formula` in
`Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula`, with its statement unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation` and used
its already proved `rawModuleScalarHom_evaluate` equation. A proved private generic lemma
`map_three_factors` substitutes the raw module pullback factorization, distributes the
forgetting functor over the three factors, and reassociates. Updated the item's DAG proof
and proof dependencies to match these two existing lemmas.

The file compiles cleanly through `lcompile.py` (31.9 seconds after final option scoping). Keeping the functor calculation
abstract avoids the expensive concrete rewrite/unfold comparisons; no time limit or heartbeat
limit was raised. The elaboration option is scoped to the theorem, and no file-level instance
registrations were needed. The static interface comparison reports no changes. Zero classes, degree zero, identity arrows, and zero coefficients all use
the same proof, which introduces no additional hypotheses.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.rawModuleScalar_hom_composite_formula`
(node `lem-sbc-raw-module-scalar-hom-composite-formula`), the item's only original hole.
Added: none. No `sorry` remains in the delivered module. The private helper is fully proved.
The existing imported theorem `AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula`
(node `lem-sbc-raw-scalar-pullback-module-formula`) remains a dependency; this delivery does
not add or move its hole. This is one hole closed and zero holes added.

## No longer needed

No imports or modules were removed, and no module is pruned. The old direct proof dependency
`def-sbc-raw-module-abelian-hom-map` is replaced by
`lem-sbc-raw-scalar-hom-evaluation`; the definition node remains needed by the unchanged
statement and transitively by evaluation, so it is not pruned. The proof uses the existing
raw module pullback factorization and the proved scalar Hom evaluation lemma. It does not use source coherence,
inverse-comparison naturality, or the coefficient-square theorem; the original public
coefficient-factor import supplies definitions appearing in the statement and is retained.
`RawModuleScalarMapFormula` is not imported: its duplicate factor declarations are unnecessary.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The earlier searches mentioned the factor-name conflict in
`RawModuleScalarMapFormula`; the library now also contains the compatible, already proved
`RawModuleScalarHomEvaluation` module. The DAG proof is updated to use it. Direct concrete
rewrites initially reached the time or heartbeat limits; the generic proved helper gives
the same categorical calculation within the existing limit. No definitions, target
statements, other groups' modules, or unit routes were changed. The unit record
`sk-lem-failure-field` has no realized entries assigned to this auxiliary node.

## Second reading by W3

1. **Interface unchanged — pass.** Read the complete repository/sandbox module diff.
   The existing theorem signature is byte-for-byte identical and agrees verbatim with
   the node's Lean statement. Its docstring and all definitions are unchanged. The only
   added import is proof-only; the helper is private and the transparency option is
   scoped to the theorem. No change record or consumer adaptation is needed.
2. **Proof and axioms — pass.** Independently compiled the delivered module through
   `lcompile.py` without errors or warnings (32.3 seconds). A scratch copy with
   `#print axioms` compiled in 46.9 seconds: `map_three_factors` uses only `propext`,
   and `rawModuleScalarHom_evaluate` uses only the three permitted axioms. The main
   theorem and existing pullback formula use the three permitted axioms and `sorryAx`;
   the pullback formula is still open in the library. No `sorry` or prohibited
   declaration/attribute occurs in the delivered module; no definition or chosen data
   was added. This closes one local hole without claiming that its import closure is
   axiom-free.
3. **Split statements — pass, none added.** There are no split-off statements or
   new nodes. Read the two existing dependency declarations and their DAG nodes.
   The fully proved private helper is a generic consequence of functoriality and
   associativity, and has no nonzero, positive-degree, or invertibility hypothesis.
   Thus degree zero, zero classes, identity arrows and zero coefficient sheaves are
   covered without case restrictions. Independent Loogle, LeanFinder and Mathlib grep
   searches found `Functor.map_comp` and `Functor.map_comp_assoc`, which give this
   categorical calculation, not a replacement for the concrete pullback equation.
4. **Route and pruning — pass after report correction.** The proof first uses the
   already proved evaluation equation, then the existing pullback formula, and combines
   them by two `Functor.map_comp` rewrites and associativity. This is a real reduction
   using existing statements. The three public imports supply the named map and factor
   definitions in the unchanged signature; both private imports are used by the proof.
   Local/upstream searches found no shorter compatible concrete theorem; the older
   `RawModuleScalarMapFormula` redeclares the factor names. The old direct definition
   dependency is replaced by evaluation and is now explicitly accounted for above;
   no module becomes unnecessary. Read `dag/units/sk-lem-failure-field.json`:
   its realized statement and step lists are empty, and this auxiliary node is not
   assigned to a realized entry. No unit route or record is changed.
5. **DAG agrees with Lean — pass.** The only changed node fields are `proof`,
   `proof_deps`, and `proof_origin`. The two proof steps describe evaluation followed
   by the generic three-factor expansion, and their cited dependencies have exactly
   the declarations applied in Lean. The statement, statement dependencies and Lean
   signature record remain unchanged. No new-node fields need checking.

Second reading changed only this report: completed `## No longer needed` by naming
`def-sbc-raw-module-abelian-hom-map` as the replaced direct proof dependency, explained
why its module remains needed, and appended the independent checks above. The Lean proof
and DAG were correct and were retained.
