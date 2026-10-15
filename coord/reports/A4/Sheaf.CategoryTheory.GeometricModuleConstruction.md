## What changed

Proved `SheafOfModules.geometric_module_construction` in
`Sheaf.CategoryTheory.GeometricModuleConstruction` without changing its statement,
its existing public imports, or any other module. All added implementation helpers
are private. No data is chosen from an unproved existence theorem.

The proof constructs the transported additive groups, scalar actions, section
modules, restriction maps, module sheaves, and functors explicitly. It uses
Mathlib's `Functor.mapCommGrp`, Cartesian monoidal product comparisons, and the
proved source-library `Functor.modObjObj` and `Mod.scalarRestriction` for the
multiplicative action laws. The two distributivity diagrams are proved directly.
`MonObj.ext` forces unit compatibility of the ring isomorphism from its
multiplication compatibility. Binary-operation mates and terminal uniqueness
prove the scalar map for the right adjoint preserves the required operations.
The final product comparisons and both projections of `k` are proved explicitly.

Added proof-only imports:
- `Mathlib.CategoryTheory.Sites.CartesianMonoidal`
- `Mathlib.CategoryTheory.Monoidal.CommGrp_`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`

Updated the item's node proof, proof dependencies, and proof origin to this route.
The preflight-required record for the private-support namespace/open/local-instance
commands is `coord/changes/geometric-module-construction-private-support.md`.
No existing public signature or definition changes; no forced adaptations.
The existing named nondependent forall binder `hRing` is preserved verbatim;
the unused-variable style linter is disabled only for this declaration because
it reports that pre-existing binder independently of its use after `intro`.

## Proved and sorry left

Closed: `SheafOfModules.geometric_module_construction`
(node `lem-weil-pbc-geometric-module-construction`), the module's sole original hole.

Added holes: none. Remaining holes in the delivered module: none.
This is a proof, not a decomposition. Every added private helper is proved.

The complete module compiles through `lcompile.py` within the single-file limit.
The declaration signature was checked byte-for-byte against the starting module.
The delivery dry run additionally checks axioms of all delivered declarations.

## No longer needed

Removed the three unused proof-dependency imports from the repository version:
`Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian`,
`Sheaf.CategoryTheory.CartesianScalarDistributivityTransport`, and
`Sheaf.CategoryTheory.TransportScalarActionDiagrams`.
The two public statement imports are preserved. The second reading also removed
the redundant added import `Mathlib.CategoryTheory.Adjunction.Limits`: its API is
already publicly imported through `Sheaf.CategoryTheory.RingedSiteModules`.
The following planned dependencies are not used or imported by this proof, and
were removed from the item's `proof_deps`:

- `lem-weil-pbc-sheaf-algebraic-structures-abelian-component`, module
  `Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian`;
- `lem-weil-pbc-cartesian-scalar-distributivity-transport`, module
  `Sheaf.CategoryTheory.CartesianScalarDistributivityTransport`;
- `lem-weil-pbc-transport-scalar-action-diagrams`, module
  `Sheaf.CategoryTheory.TransportScalarActionDiagrams`.

Their use for this item is pruned; other callers may still need them. The retained
module-category definition is `def-weil-sheaf-of-modules-category`, from
`Sheaf.CategoryTheory.RingedSiteModules`. No blueprint unit statement or realized
unit proof step is bypassed. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed interface was found. The proposed general
operation-transport helpers were unnecessary: existing internal commutative-group
and multiplicative-action APIs, together with direct Cartesian diagram
calculations, suffice. In particular the missing explicit unit hypothesis on the
ring comparison is harmless: monoid-structure uniqueness supplies it.

## Second reading by A4

1. Interface: PASS. Compared the delivered module with the shared repository
   using `diff`. The sole existing theorem signature and its existing docstring
   are byte-for-byte identical, including `hRing`. Both public imports are
   unchanged. All added implementation declarations are private, and there are
   no changes to other modules or existing definitions. The support-command
   change record describes the namespace, options and local instance accurately.

2. Proof and constructions: PASS. Read the complete implementation, including
   the sectionwise additive group, transported monoid action, both distributivity
   diagrams, linear restriction maps and morphisms, the underlying natural
   isomorphisms, ring-unit compatibility, adjunction mates, and both projections
   of `k`. The module compiles without errors or warnings through `lcompile.py`.
   A scratch copy with `#print axioms
   SheafOfModules.geometric_module_construction` compiles after import pruning
   and reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
   No `sorry`, forbidden declaration, hollow definition or arbitrary witness of
   an unproved existence theorem occurs. The products and monoidal comparisons
   come from universal properties, and the module data is explicitly constructed.

3. Split statements: PASS, none. The only original hole is closed and no hole is
   added. Every private helper has a complete proof. The construction uses only
   product, terminal and algebraic identities, so zero rings, zero modules and
   empty sites introduce no exceptional hypothesis or element choice.

4. Route and pruning: PASS after the changes below. Repeated LeanFinder search
   for "finite product functor internal commutative groups sheaf modules
   reconstruction", Loogle search for
   `CategoryTheory.Functor, CategoryTheory.CommGrp`, and local `rg` searches for
   sheaf/module reconstruction and `mapMod` APIs. The hits provide the
   `mapCommGrp` already used, specialized continuous-site constructions, or
   monoidal module objects; none directly replaces this arbitrary set-sheaf
   functor construction with its sectionwise operation comparisons. Checked all
   three discarded proof dependencies against the unit records: none realizes
   any unit statement or step. The proper-base-change unit's `realized` route is
   preserved. The remaining proof imports supply the sheaf Cartesian monoidal
   structure, internal commutative-group transport, and monoidal action transport.

5. Nodes: PASS. Only `proof`, `proof_deps`, and `proof_origin` differ from the
   repository node. Its stored Lean statement matches the unchanged theorem
   signature exactly. Its six proof steps describe the actual construction,
   and `proof_deps` retains precisely the module-category definition. The three
   discarded planned dependencies are all listed under `## No longer needed`.
   No new node or statement-change record is needed.

Second-reading changes: removed the redundant proof import
`Mathlib.CategoryTheory.Adjunction.Limits`, whose public import chain already
runs through `RingedSiteModules`, `ModuleCat.Sheaf.Abelian`, and
`CategoryTheory.Abelian.Transfer`. Corrected the report's claim that no imports
were removed: the current repository includes the three discarded planned
proof-dependency imports. No proof body or theorem statement needed repair.
