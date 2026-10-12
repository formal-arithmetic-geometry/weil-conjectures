## What changed

Proved all seven remaining theorem proofs in
`lean/Sheaf/CategoryTheory/ExtensionByZeroPresheaf.lean`, without changing any declaration
signature, definition, import, or existing docstring. Added one proved private computational
helper, `extensionByZeroPresheafRestrictAdd_of`, which permits specifying the destination
summand by an equality of indices. It follows directly from `DirectSum.toAddMonoid_of`.
Restriction laws are proved by direct-sum induction and the existing presheaf laws for `G`.
Naturality uses `PresheafOfModules.naturality_apply` on each summand. Morphism identity
and composition use Mathlib's `DirectSum.lmap` laws. The unique-index isomorphism is
component evaluation with inverse the sole injection, composed with `ULift.moduleEquiv`.
The existing empty-index proof remains valid. Local compilation succeeds without warnings.

## Proved and sorry left

Proved these seven formerly unfinished declarations, all realizing
`def-weil-extension-by-zero-presheaf`:

- `SheafOfModules.extensionByZeroPresheafRestrict_smul`
- `SheafOfModules.extensionByZeroPresheafMap_id`
- `SheafOfModules.extensionByZeroPresheafMap_comp`
- `SheafOfModules.extensionByZeroPresheafHom_naturality`
- `SheafOfModules.extensionByZeroPresheafHom_id`
- `SheafOfModules.extensionByZeroPresheafHom_comp`
- `SheafOfModules.extensionByZeroPresheafSection_unique`

No sorry remains in the module; no new sorry or module was added.
`SheafOfModules.extensionByZeroPresheafSection_isEmpty` was already proved.
The private computational helper is also fully proved.

## No longer needed

None. The original two public imports are needed for the unchanged definitions and
statements. No proof imports were added. The node has no proof dependencies or numbered
proof plan; its definition and the unit route are unchanged. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

None. The explicit construction and both empty/unique index cases are valid. Specifying
the destination index separately avoids rewriting a dependent summand index underneath
an `Over.homMk` proof; this is proof elaboration glue, not a statement correction.

## Second reading by R1

1. Compared the complete module with the repository using `diff -u`: all existing
   declaration signatures, definition bodies, imports and docstrings are byte-for-byte
   unchanged. Only seven theorem bodies and one private computational helper are added.
   No statement change or change record is needed. Verdict: pass.
2. Compiled the delivered module locally with `lcompile.py`, without errors or warnings.
   A scratch copy with `#print axioms` for every declaration, including the private helper,
   reports only `propext`, `Classical.choice`, and `Quot.sound`. Checked absence of sorry,
   axiom, unsafe, opaque, implemented_by and extern. No hollow definitions. Verdict: pass.
3. No split-off statement, new module, or new sorry exists. The private helper computes
   restriction on a generator using `DirectSum.toAddMonoid_of`; substituting its index
   equality makes it definitional, so it is elaboration glue rather than a new mathematical
   dependency. Checked the empty-index case and the unique-index equivalence: component
   evaluation and the sole injection are inverse, including zero modules. Verdict: pass.
4. Read the proofs from the functor laws down to the restriction generators. They use
   Mathlib direct-sum induction, lmap laws, and the existing presheaf identity, composition,
   semilinearity and naturality laws, with no unproved project theorem. Searched Mathlib
   DirectSum and the upstream/library extension-by-zero declarations for a shorter route.
   `DirectSum.lid` treats a constant family; the short component-based equivalence here
   handles the dependent family directly. Both public imports occur in unchanged definitions
   or signatures. The old node has empty proof_deps, so No longer needed is complete.
   Read `dag/units/sk-def-sf-operations.json`: its realized statement/steps are empty,
   and the extension-by-zero construction and ambient route are preserved. Verdict: pass.
5. Read `def-weil-extension-by-zero-presheaf`: its explicit sectionwise construction,
   scalar action, restriction, componentwise morphisms and empty/unique special cases
   agree with Lean. As a definition node it has proof=[], proof_deps=[], and
   proof_origin=null; the proofs merely verify the laws of that unchanged construction.
   No DAG update or new mathematical node is needed. Verdict: pass.

Second reading changed only this report; the Lean proofs required no repair.
