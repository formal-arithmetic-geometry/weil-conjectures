## What changed

Proved AlgebraicGeometry.Etale.rawModuleAbelianHomMap_target_formula with its
signature and docstring unchanged. Apply rawModuleScalar_pullback_abelian_formula,
rewrite with rawModuleScalarHom_evaluate, unfold rawModuleScalarSourcePrefix,
and use Functor.map_comp and Category.assoc.

Added the proved evaluation helper rawModuleScalarHom_evaluate in the new module
Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation. It imports the canonical
source and coefficient factor definitions. Its proof is rfl, the same argument
as the already proved rawModuleScalar_map_formula in RawModuleScalarMapFormula.
That existing module cannot be imported here because it duplicates both canonical
factor declarations; importing it gives an environment collision. The helper's
new name avoids colliding with that still-existing theorem. No new mathematical
obligation is introduced, no proof hole is split off, and no existing module
besides the item is changed or deleted.

Added the evaluation module as a proof-only import and updated the item's node
accordingly. The unit's realized statement and steps remain unchanged. The
previous version of this pair compiled without warnings in 47.5 seconds for the
evaluation helper and 42.4 seconds for the item; the final dry run compiles and
probes the renamed declarations. The item's signature was compared textually
with the repository version and is identical. All Lean lines are at most 100
characters and neither delivered file contains sorry.

## Proved and sorry left

Closed the item's only hole:
AlgebraicGeometry.Etale.rawModuleAbelianHomMap_target_formula
(lem-sbc-raw-module-abelian-hom-target-formula).

Added and fully proved AlgebraicGeometry.Etale.rawModuleScalarHom_evaluate
(lem-sbc-raw-scalar-hom-evaluation). No holes added, none split off, and no sorry
remains in either delivered module. Net change in holes: one closed, zero added.

The proof uses the existing abelian pullback formula and the actual source and
coefficient factor definitions. It does not use their coherence-square theorems.
Zero classes, identity arrows, degree zero and empty test objects are covered
by the same calculation, with no extra assumptions.

## No longer needed

The old direct proof dependency def-sbc-raw-module-abelian-hom-map is replaced
by lem-sbc-raw-scalar-hom-evaluation. The definition remains an indirect proof
dependency through that helper and remains necessary in the target statement;
its module is not pruned.

No original import of the item is removed. Its public imports supply the data
in the unchanged statement, and its original proof import supplies the abelian
pullback formula. No planned module is newly pruned from the target closure.

Sheaf.AlgebraicGeometry.RawModuleScalarMapFormula is not needed or imported by
this proof. Its factor definitions duplicate the canonical modules and prevent
its evaluation theorem from being jointly imported with them. It has no importing
modules according to downstream.py and the local library import search. It is
left in the repository for maintainer pruning; no deletion is delivered.

The source and coefficient coherence squares and scalar-map invertibility are
not used, as already specified in the original node. Their modules are not
pruned because the statement still uses the factor definitions they supply.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report claimed completion without a passing compile. Its
private evaluation lemma and main calculation together exceeded the 60-second
limit. Profiling separated fast tactic elaboration from costly kernel checking
of the derived-Hom definitions. The existing separate evaluation API solves
this without changing definitions or raising the compile limit; it remains
fully proved and is used as the original planned evaluation step.

RawModuleScalarMapFormula could not be imported alongside the canonical factor
modules: it redeclares scalarCoefficientFactor and scalarSourceFactor. Its
landed change record raw-module-scalar-map-formula.md explains that these were
copied in because a dependency was absent at the time. That dependency exists
now. The proved canonical-factor helper reuses its rfl argument and introduces
no unproved theory or arbitrary data choice.

A first dry run attempted to withdraw the obsolete duplicate module under brief
step 8b. The current preflight refuses deletions and renames, including this
withdrawal, although deliver3.py accepts deleted.txt. The delivery now makes no
deletion: the unused module remains for maintainer pruning. No tools were changed.

The existing evaluation theorem's docstring references
lem-sbc-raw-scalar-map-formula, but no such node or matching lean record exists
in the repository. The new helper has its own complete matching node instead.

## New nodes

lem-sbc-raw-scalar-hom-evaluation records the fully proved canonical-factor
evaluation helper in RawModuleScalarHomEvaluation. This is strictly the
additive-map evaluation step, with no pullback or source-prefix conclusion.
Its docstring supplies the source and complete argument. Three search kinds
are recorded, with LeanSearch explicitly unavailable. It adds no sorry.


## Second reading by N4

1. PASS: compared the target module with the repository by diff and compared its
   theorem signature byte for byte. Only the proof and one plain proof import
   differ. The existing docstring, public imports, definition bodies and all
   parameters are unchanged. No target or other existing interface is changed.
   Both node lean.statement strings match their delivered Lean signatures.
2. PASS: independently compiled both files through lcompile.py --all, without
   warnings (helper 47.4 seconds; item 38.3 seconds). Neither file contains sorry
   or a forbidden declaration form. A scratch module importing the compiled
   delivered modules ran #print axioms on rawModuleScalarHom_evaluate and
   rawModuleAbelianHomMap_target_formula: each uses exactly propext,
   Classical.choice and Quot.sound, with no sorryAx. No data is introduced or
   chosen from an unproved existence statement.
3. PASS: no statement is split off with sorry. Read the new evaluation helper
   against rawModuleAbelianHomMap, scalarSourceFactor and scalarCoefficientFactor:
   its c ≫ V(z) ≫ b is precisely evaluation of the three composed additive maps.
   Its rfl proof includes q = 0, zero z, zero sheaves and identity maps without
   cancellation or nonemptiness assumptions. It is strictly the evaluation step,
   not a restatement of the pullback target. Its docstring gives the full argument
   and its new node supplies the source and required metadata. Independent
   LeanFinder and Loogle searches for Preadditive.leftComp/rightComp evaluation,
   and msearch grep for those names and mapAddHom, found the generic additive-map
   API. Local rg over Sheaf and WeilConjectures found only the older concrete
   rawModuleScalar_map_formula. Reading that file and its landed change record
   confirms its duplicate factor declarations make it unusable with the canonical
   modules imported by this target. The helper uses the canonical factors and
   reproduces the existing definitional argument without duplicating definitions.
4. PASS: read the proof from the target downward. The first step applies the
   existing rawModuleScalar_pullback_abelian_formula to the scalar class. The
   helper exposes its evaluation; map_comp and assoc then give exactly the
   defined rawModuleScalarSourcePrefix and two coefficient factors. Each public
   import supplies declarations in the unchanged signature (or their canonical
   definitions); both plain imports supply proof lemmas. No coherence-square
   theorem or invertibility assumption is used. The old direct definition
   dependency is now indirect through the helper; clarified this under No longer
   needed. No module is pruned. Read sk-lem-failure-field.json: its realized
   statement and step lists are empty, and this delivery changes no unit record
   or chapter route. The existing factor-calculation route is retained.
5. PASS: the target node changes only proof, proof_deps and proof_origin.
   Its steps and dependency union match the two imported proof lemmas and the
   source-prefix unfolding. The helper node's statement, declaration, canonical
   definition dependencies, rfl argument, source, search records, chapter, unit,
   created and blueprint fields agree with the delivered module. No unsupported
   mathematical obligation is added.

Changed in this reading: added the missing blueprint tag to the new helper's
module docstring; clarified the replaced direct DAG dependency under No longer
needed; added this independent review. No Lean proof or signature needed repair.
