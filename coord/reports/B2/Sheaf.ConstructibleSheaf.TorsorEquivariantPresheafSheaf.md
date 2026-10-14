## What changed

Retained the duplicate-removal repair: this module publicly imports
`Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf` and declares no theorem of
its own. Added a module-documentation sentence recording that the imported theorem is
the unique implementation of this compatibility API. This makes the delivery a
reviewable change while preserving the public compatibility path and all signatures.

## Proved and sorry left

There are no declarations or `sorry`s in this module. No holes were closed and no
holes were added; the retained theorem is already sorry-free.

## No longer needed

No imports, nodes, or modules are newly pruned by this delivery. The earlier
landed duplicate-removal repair already removed the copy-pasted proof and private
helper; their implementation is retained in `TorsorEquivariantModuleIsSheaf`.
The compatibility module still needs its sole public import to expose that theorem.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1428 correctly identified the duplicate theorem. The prior delivery
was semantically correct but byte-for-byte unchanged, so preflight rejected it as an
unchanged item. This delivery records the same repair with an explicit compatibility
documentation update; no target statement or DAG route is changed.

## Second reading by B2

1. Compared every delivered Lean file with the repository using `diff -u`.
   The sole difference is one sentence in the module docstring. There are no
   declarations in either version, so existing signatures, definitions, imports,
   visibility, and target statements are unchanged. The prior interface repair is
   recorded in the already landed
   `coord/changes/equivariantModulePresheafSheaf-duplicate.md`.
2. The delivered compatibility module compiles locally without errors or warnings.
   It contains no `sorry`, definitions, or forbidden declarations. A scratch copy
   with `#print axioms` checks the re-exported
   `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`:
   only `propext`, `Classical.choice`, and `Quot.sound` occur, with no `sorryAx`.
   Read the retained implementation: continuous functions form a sheaf under
   base change, equivariance is local by separatedness, and the natural isomorphism
   and module forgetful functor transport and reflect the sheaf condition.
3. There are no split-off statements or new nodes to validate or search for.
   Searched the constructible-sheaf sources for the theorem and compatibility
   import; the theorem has one implementation and callers use its retained
   restricted-scalars signature. No arbitrary existence witness or hollow
   construction is introduced. The proof imposes no primality, connectedness,
   or finite-generation assumptions; discrete coefficients and local equivariance
   work also for the zero module, trivial group, and empty scheme.
4. The shortest compatibility route is the existing public re-export. Its sole
   import is necessary to preserve the public API; changing it to a proof-only
   import would remove that API. No dependency is newly removed. Read
   `dag/units/sk-thm-p1.json`, including `realized`: the documentation-only edit
   changes no unit statement, step, or realization.
5. Read both torsor-equivariant sheaf nodes. Both Lean records point to the
   retained theorem in `TorsorEquivariantModuleIsSheaf`; the compatibility node's
   proof dependency names that implementation node. Its direct re-export route
   agrees with the file, and the implementation node describes the continuous
   sheaf/subfunctor/natural-isomorphism argument. No metadata edits are needed.

Second reading changed the report's pruning claim to distinguish the already
landed duplicate removal from this documentation-only delivery, and added this
review record. No Lean proof or interface repair was necessary. Holes closed: none;
holes added: none; remaining holes in the delivered module: none.
