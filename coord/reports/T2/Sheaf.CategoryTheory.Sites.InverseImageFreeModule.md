## What changed

Proved the five theorems of Sheaf.CategoryTheory.Sites.InverseImageFreeModule from
the already stated dependencies, keeping every theorem signature unchanged:
existence and uniqueness, simultaneous coefficient/generator naturality, product
generator compatibility, identity, and composition.

Extracted ring, moduleSets, free, generatorRaw, generator, change and changeSets
unchanged into Sheaf.CategoryTheory.Sites.FreeModuleSheafConstruction. The original
module publicly re-exports them. FreeModuleUniversalProperty,
GeometricFreeModuleHomEquivalence and NormalizedFreeModuleComparison now publicly
import the construction module instead of the parent theorem module, breaking the
cycle that otherwise prevents the parent from using its stated proof dependencies.
The support theorem statements and existing proofs are unchanged. The final claim read identifies W4, X2 and X3 as their respective holders.

The existence proof explicitly removes the canonical ULift, applies the normalized
universal-realization theorem to the transported restriction bijections, and restores
the ULift. Naturality and composition instantiate the stated conditional calculus.
Products use naturality of the free functor on its generators directly. For identity,
the graph laws for addition and scalar multiplication make moduleUnderlying.inv
linear over the identity ring comparison; uniqueness on generators finishes.

Local cached HasSheafCompose instances avoid repeated expensive typeclass searches
in the comparison-calculus module and the item. These have no global instance effect.
A diagnostic with a reduced instance-heartbeat budget identified those searches.

Change record: coord/changes/T2-free-module-construction-extraction.md.

## Proved and sorry left

Closed 5 of 5 original holes, with no new proof holes and no split-off theorems:

- CategoryTheory.SheafFreeModule.inverseFreeModule_existsUnique
- CategoryTheory.SheafFreeModule.inverseFreeModule_naturality
- CategoryTheory.SheafFreeModule.inverseFreeModule_products
- CategoryTheory.SheafFreeModule.inverseFreeModule_identity
- CategoryTheory.SheafFreeModule.inverseFreeModule_composition

The item and new construction module have zero sorry. W4 proved and landed all five universal-property holes during this session; its
latest proofs are preserved unchanged in the import-adapted support module.
The following pre-existing support holes are retained unchanged:

- geometricFreeModule_hom_chain (lem-trf-geometric-free-module-hom-equivalence).
- normalizedFreeModule_change_semilinear, normalizedFreeModule_naturality,
  normalizedFreeModule_generators, normalizedFreeModule_products,
  normalizedFreeModule_identity, normalizedFreeModule_composition
  (lem-trf-normalized-free-module-comparison-calculus).

Validation: the item compiled with no errors or warnings in 46.9 seconds.
All five original theorem signatures and all existing support signatures were
compared textually and are unchanged. The complete five-module packet compiled cleanly in dependency order; individual
files took 2.2 to 26.1 seconds in that run. The unchanged direct consumer InverseImageDifferentials also compiled cleanly
against the packet in 42.6 seconds; its temporary identical sandbox copy was removed.

All these names have the prefix CategoryTheory.SheafFreeModule. The proof is an
assembly from the stage's stated dependencies, so their sorry axioms remain in its
transitive axioms until those separate items are proved.

## No longer needed

Removed the item's direct private import Sheaf.CategoryTheory.GeometricModuleTransport;
that tool is used by the transported-Hom dependency, not directly by the assembly.
Deleted the stale top-level tool_uses approval for lem-weil-pbc-geometric-module-transport
from the parent node: its real use stays in the transported-Hom node and module.

The product proof does not need normalizedFreeModule_products or its projection-square
and arbitrary-generator machinery: freeModule_restrict_naturality and hp suffice.
The identity proof does not need normalizedFreeModule_identity, because its source
module includes a nontrivial algebraic presentation; the graph laws supply the needed
linear morphism directly. The comparison-calculus node/module remains needed for
naturality and composition. No entire theorem node or module is withdrawn or claimed
pruned from the target closure. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The three stated dependencies imported the theorem module which their parent's proof
had to import. The stage-2 review notes already identified this import cycle. Moving
only the shared data declarations resolves it without duplicating constructions or
changing mathematical statements. tools/import_direction.py on the unchanged source
confirms that importing GeometricFreeModuleHomEquivalence into the item would close
a cycle; the delivered source import graph breaks that reverse edge.

The normalizedFreeModule_identity theorem is stated only for a literal endomorphism
of the free module, whereas this item's identity theorem also retains an arbitrary
normalized algebraic presentation F. Its use therefore needs a linearity argument
from F.moduleAdd and F.moduleSMul; the proof supplies that argument explicitly.
Edge cases remain unchanged: empty generators, zero coefficient ring, empty finite
product, identity inverse image and arbitrary noninvertible coefficient maps.

## Forced adaptations

Sheaf.CategoryTheory.Sites.FreeModuleUniversalProperty (W4),
Sheaf.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence (X2), and
Sheaf.CategoryTheory.Sites.NormalizedFreeModuleComparison (X3) require the
following import adaptations.


The original support modules import InverseImageFreeModule, while the completed
parent must import those same modules to use their stated lemmas. The resulting
original source graph has a cycle. Against the extracted construction overlay, an
original compiled dependency also brings the former parent definitions, producing:
`environment already contains CategoryTheory.SheafFreeModule.free from
Sheaf.CategoryTheory.Sites.FreeModuleSheafConstruction` (item compile, 2026-10-23).

Changed only the public import in FreeModuleUniversalProperty (W4, line 8) and
GeometricFreeModuleHomEquivalence (X2, line 3). Changed the same import in
NormalizedFreeModuleComparison (X3, line 8), and locally cached existing
HasSheafCompose instances after the site variables. Its adapted source otherwise
repeatedly exceeded 60 seconds; a low-heartbeat diagnostic located the repeated
HasSheafCompose searches. Caching brought it to 53 seconds. All existing signatures,
visibility, constructions and theorem proofs in these support modules are unchanged.

## New nodes

The definition node def-trf-free-module-sheaf-construction records the seven existing
data declarations moved into their shared construction module. It introduces no new
mathematical notion, no choice of an arbitrary existence witness, and no sorry.
The parent node's proof and Lean attachment now reflect the actual assembly and the
relocation. No new theorem node is introduced.

## Forced adaptations

### Sheaf.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

### Sheaf.CategoryTheory.Sites.NormalizedFreeModuleComparison
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
