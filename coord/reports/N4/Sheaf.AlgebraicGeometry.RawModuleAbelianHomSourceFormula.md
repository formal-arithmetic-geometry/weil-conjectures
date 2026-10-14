## What changed

Replaced the original hole in rawModuleAbelianHomMap_source_formula by a
complete categorical recombination of two strictly lower statements: expansion
of the scalar Hom map on the module raw pullback, and source/class coherence
before attaching coefficients. The proof postcomposes the source/class equation
with the common coefficient tail, then uses transitivity and associativity.
No existing statement, definition, signature or public import changes.
The second reader replaced the new Hom composite module's public SourcePrefix
import by SourceFactors, and the new source/class module's public
CoefficientSquare import by CoefficientUnshifted: their statements need only
those definitions.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.rawModuleAbelianHomMap_source_formula
(one original hole).
Added: AlgebraicGeometry.Etale.rawModuleScalar_hom_composite_formula and
AlgebraicGeometry.Etale.rawModuleScalar_source_class_formula (two holes).
This is a decomposition: one closed hole and two strictly lower holes added,
net minus one hole. The first statement evaluates the scalar map and module
raw pullback, without source coherence. The second proves source/class
coherence without either coefficient factor or the raw scalar map. Neither
alone has the assigned theorem's conclusion. No sorry occurs in a definition,
private helper or partial proof. Both remaining named theorems have complete
proofs in words and matching DAG nodes.

## No longer needed

The original node's five direct proof dependencies are no longer directly used
by the recombination proof: def-sbc-raw-module-abelian-hom-map,
lem-sbc-raw-scalar-pullback-module-formula,
lem-sbc-raw-scalar-sheaf-composition,
lem-sbc-raw-scalar-source-square-core, and
 def-sbc-raw-module-scalar-source-prefix. The definitions remain in the unchanged
signature, and the lower statements retain the pullback, sheaf-composition and
generic source-square steps. These nodes remain required transitively; none is
pruned from the targets' import closure.

Removed direct proof imports from the item: RawModuleScalarPullbackModuleFormula,
RawModuleScalarSheafComposition and RawModuleScalarSourceSquareCore. Their
modules remain imported by the two lower modules. In the new Hom composite
module SourceFactors replaces SourcePrefix; in the new source/class module
CoefficientUnshifted replaces CoefficientSquare. Neither shorter import drops a
module from the targets' closure because the item still needs SourcePrefix and
CoefficientSquare in its signature. No coefficient-square theorem, abelian raw
pullback formula or concrete source-square theorem is used. No unit step is
bypassed. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The inherited report claimed success although the inherited proof still had
sorry. The inherited sandbox also had stale compiled copies of dependencies
without corresponding source edits; these were removed from the active compile
overlay. Final checks use the published library plus the delivered sources.
RawModuleScalarMapFormula redeclares scalarSourceFactor and
scalarCoefficientFactor and cannot coexist with the assigned imports. The
concrete source-square module similarly conflicts on derivedPullbackIso.
The generic core avoids this conflict. Direct proofs encountered expensive
conversion between ModuleSheaf and explicit Sheaf derived-category instances;
no compiler limits, public interfaces or reducibility settings were changed.
The two extracted equations hold for zero classes, degree zero, identity
arrows, zero coefficients and empty objects by the same naturality equations.

## New nodes

lem-sbc-raw-module-scalar-hom-composite-formula: evaluate the explicit bundled
additive scalar map, apply rawModuleScalar_pullback_module_formula, distribute
derived scalar forgetting with map_comp. Source: Stacks Tags 03FD and 03Q8,
and the explicit library constructions.

lem-sbc-raw-module-scalar-source-class-formula: attach the generator to the
sheaf composition square, derive it using plus_single_source_square_core,
then use inverse derived-comparison naturality on the class. It stops before
both coefficient factors. Source: Stacks Tags 03D7 and 03Q8.

No change record or forced adaptation is needed.

## Second reading by N4

1. PASS. Read the complete diff against the repository. The only changes to the
   existing module are three proof imports replaced by two proof imports and the
   original theorem's proof. Its declaration signature and existing docstring
   are byte for byte unchanged; all existing public imports are retained. There
   are two new theorem modules and two new nodes, no definition changes, no
   forced adaptations and no change records.
2. PASS. All delivered files compile locally in import order. The original
   theorem has no sorry; the only delivered holes are the two named theorems
   listed above. No axiom, unsafe, opaque, implemented_by, extern, private hole,
   data hole or arbitrary choice of an unproved existence witness is added.
   Scratch #print axioms checks show only the standard axioms and sorryAx.
3. PASS. Read both lower signatures and their full docstring arguments against
   rawModuleAbelianHomMap, source/coefficient factor definitions,
   rawModuleScalar_pullback_module_formula, rawModuleScalar_sheaf_composition,
   plus_single_source_square_core and inverse naturality. Zero classes and zero
   coefficient sheaves give zero composites; q = 0 removes the shift; identity
   arrows obey the same canonical comparison equations; empty objects require
   no extra hypothesis. The first equation retains every module factor and
   does not commute the source. The second stops before coefficients and
   does not expand the scalar Hom map. Neither restates the item. Repeated
   LeanFinder, Loogle and grep with different queries (searches.jsonl), plus
   local searches. Found the existing rfl map formula and proved concrete
   source square; their modules collide with required factor/comparison names.
   The generic composition, single-square and naturality lemmas support the
   reduction but do not by themselves state either concrete equation.
4. PASS. The top proof combines expansion and source/class coherence by
   congrArg, transitivity and associativity. Proof imports are non-public.
   Narrowed two new signature imports to the modules actually providing their
   definitions. Enumerated every old proof dependency above, distinguishing
   removed direct use from retained transitive use. The unit record
   dag/units/sk-lem-failure-field.json is unchanged (its realized lists are
   empty); this calculation is below the unit and preserves the inherited
   route. No target-closure pruning or net proof progress is claimed.
5. PASS after repair. The existing node's proof and proof_deps match the two
   applications in Lean. The new nodes match their theorem signatures, parent,
   chapter, unit, source, creation record and full lower proof plans. Replaced
   the source/class node's context-dependent prose by a self-contained
   statement and recorded its narrower definition dependency. Added the
   second-reader search evidence to both new nodes.

Changes by the second reader: narrowed the two new modules' public imports,
made the source/class node self-contained, corrected the complete accounting of
old direct proof dependencies, and recorded independent search evidence.
Attempted both lower proofs in scratch work. The sheaf square and generic
single-complex specialization typechecked, but final class conversion requires
bridging the cached ModuleSheaf/raw-Hom and explicit sheaf single/shift
presentations. Bundled scalar evaluation has the same conversion cost. Attempts
failed with conversion errors or the fixed 60-second limit; no failed attempt,
compiler option, reducibility change or partial proof is delivered. Thus the
final result remains the reported decomposition: one original hole closed,
two strictly lower named holes added, net minus one hole, no modules pruned.
