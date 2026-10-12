## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_trivial`
in `Sheaf.ConstructibleSheaf.TorsorInvariantSections`, with its original signature unchanged.
The explicit constant-to-invariant linear map is locally injective by surjectivity of the
torsor and locally surjective on the open fibers of an invariant section upstairs, using
the injective half of the proved `diagonalEvaluation_bijective`. The proved
`equivariantModulePresheaf_isSheaf` and Mathlib's locally bijective sheaf criterion finish.
Both added imports are proof-only. Updated the existing node's proof, proof dependencies,
and proof origin to this actual route. No public definitions or statements changed.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_trivial`,
node `lem-weil-pbc-torsor-invariant-sections` (one of one original holes).
Added holes: none. Remaining holes in delivered modules: none.
The first worker's proposed split
`AlgebraicGeometry.Scheme.GaloisCover.invariantFunction_descends` and its new module/node
were removed from the delivery. This is a proof, not a decomposition: net one hole closed.
The target and the two library lemmas used have only `propext`, `Classical.choice`,
and `Quot.sound`, verified by `#print axioms` in a scratch copy through `lcompile.py`.

## No longer needed

Every old proof dependency is retained: `def-weil-pbc-torsor-associated-module` remains used.
No repository import, existing DAG node, or existing module is pruned.
Discarded the draft proof-only import/module `Sheaf.ConstructibleSheaf.TorsorInvariantFunctionDescent`
and the undelivered node `lem-weil-pbc-torsor-invariant-function-descent`.
Removed the redundant draft import `Mathlib.CategoryTheory.Sites.LocallyBijective`;
its declarations are already available from the retained imports, checked by compilation.
Removed the unused private `trivial_equivariance` helper.

## Where the brief, the DAG or earlier work was wrong

The draft needlessly left global descent of invariant functions as a new hole. Local
surjectivity only needs equality on each open fiber upstairs, and the existing proved
`diagonalEvaluation_bijective` supplies exactly the graph injectivity needed there.
The draft also omitted the existing item's updated DAG proof/dependencies; these now
record both actual library lemmas used. The original unit route is preserved.

## Second reading by V2

1. Compared the delivered module against the repository with `diff`. The existing theorem
   signature is byte-for-byte identical, also checked by extracting text before `:= by`.
   No interface change, statement change, definition change, or forced adaptation. Pass.
2. Compiled the draft's two modules and then the repaired module through `lcompile.py`.
   The final scratch axiom check compiles without warnings; the target and both invoked
   library lemmas use only the three permitted axioms. No sorry or forbidden declaration
   form remains. The private map's data is explicitly constructed from constant functions,
   with no witness chosen from an unproved existence theorem. Pass.
3. Read the proposed function-descent statement and its docstring. It is true even for
   empty W, empty value types when a section exists, and the trivial group, and omits
   scalar and sheafification assertions. However, it is unnecessary: searches using
   Loogle (`LocallyConstant, Function.Surjective`), Lean Finder (graph evaluation of
   equivariant locally constant sections), and `rg` in the library found the proved
   diagonal-evaluation route. Removed the split theorem/module/node. No splits remain.
4. The revised proof starts at the original hole and uses only already proved library
   lemmas and Mathlib, with no new intermediate statement. The sole old proof dependency
   stays used; the report lists every removed draft import. Both remaining proof imports
   are needed for their invoked lemmas. Read `dag/units/sk-thm-p1.json` and its `realized`
   route: the unit statements and steps are unchanged; only this lower node's proof
   is shortened. Empty objects use the empty covering; no nonzero coefficient or
   nonempty base assumption is introduced. Pass.
5. Updated `lem-weil-pbc-torsor-invariant-sections` so its proof, proof_deps and proof_origin
   follow the explicit map, local injectivity, open-fiber cover, diagonal evaluation,
   sheaf condition and sheafification argument. No new nodes remain. Pass.

Second reading changed the local-surjectivity argument, removed the added descent hole,
its module and node, removed an unused private helper and a redundant Mathlib import,
restored exact signature whitespace, and supplied the missing existing-node proof record.
