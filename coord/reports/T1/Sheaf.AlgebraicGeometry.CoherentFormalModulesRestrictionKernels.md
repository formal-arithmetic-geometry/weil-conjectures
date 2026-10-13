## What changed

Completed `AlgebraicGeometry.coherentFormalModules_restriction_preservesKernel` in
`Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionKernels`, with its original signature
unchanged. Second reading removed a redundant direct public import, with the
change record below; its public declarations remain available through the unchanged
restriction-objects import. No formal abelian-category instance is used.

The proof takes the existing shifted-image kernel construction, proves its limiting-fork
property using the existing factorization and transition-zero monicity helper, and transports
its image and quotient presentations to U. Three proved private helpers supply the ordinary
restriction quotient comparison, its projection identity, and the restricted image
presentation. The quotient comparison reuses the proved private `powerQuotientIso`,
`powerQuotientIso_π`, and `quotientMap_π` in `FormalSystemsPullback` via a proof-only `import all`;
the monicity argument reuses `formalMono_of_kernel_transition_zero` in
`CoherentFormalModuleKernel` the same way. Restriction of the transition-zero bound supplies
uniqueness on U; the existing factorization theorem supplies existence there. Mathlib then
extends preservation of this constructed limiting fork to every limiting fork.

Added proof-only imports of `FormalSystemsPullback` and the source's
`Modules.QuasicoherentKernel` and `Modules.QuasicoherentCokernel`. Changed the existing
proof-only kernel import to `import all` to reuse its proved monicity helper. Updated only
`proof`, `proof_deps`, and `proof_origin` of
`lem-weil-pbc-coherent-formal-modules-restriction-kernels` to this actual route.

Read Stacks 087X and 0887 online because the source TeX is not populated in this clone.
The additional comparison is a tool from 0887, not a bypass of any realized unit step;
this item is not itself in `dag/units/sk-thm-p1.json`'s `realized` lists.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.coherentFormalModules_restriction_preservesKernel`
(node `lem-weil-pbc-coherent-formal-modules-restriction-kernels`). No `sorry` remains in
the item; no hole or new public statement was added. This is a proof from existing library
declarations, not a decomposition into new holed declarations. Existing holes reachable
through the original construction and object-condition dependencies remain work for their
owners; this delivery does not claim the theorem's entire axiom closure is sorry-free.

The file compiles cleanly through `lcompile.py` in about 13 seconds.
`deliver3.py T1 Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionKernels --no-push`
prints `OK (dry run)`; its worker-mode exception leaves only the second reading for the
independent reader. Nothing was pushed. The proof handles c=0,
zero or unit ideals, zero modules, and empty opens without extra hypotheses: the quotient
comparison covers positive powers uniformly; the image and fork arguments are categorical;
and the transition-zero helper also allows an identity transition.

## No longer needed

Removed the redundant direct public import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`; it remains in the public
import closure through `CoherentFormalModulesRestrictionObjects`. Second reading
also removed the first worker's redundant direct proof imports
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelConstruction` and
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelFactorization`: both remain used
and are accessible through `import all CoherentFormalModuleKernel`. No globally
reachable module was pruned. The direct planned edge to
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` is replaced by the proved quotient
comparison in `lem-weil-pbc-formal-systems-pullback`; that ideal-product node remains a
transitive dependency, so this is not a claim of global pruning. The full public
`coherentFormalModule_kernel` theorem is not applied, but its module stays needed for its
proved transition-zero monicity helper. No abelianness or finite-limit preservation theorem
for the formal category is needed or imported.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The existing `coherentFormalModules_restriction_limits` would
imply this result but cannot be imported: `import_direction.py may` reports that its imports
already reach this item. The chosen proof therefore establishes preservation before formal
abelianness, as the item's interface requires. The DAG's affine ideal-product step can be
implemented using the already proved power-quotient comparison instead of rebuilding it.
LeanFinder, Loogle and source grep searches found no applicable shorter theorem; the
existing finite-limit theorem was the sole tempting circular route.


## Second reading by T1

Independent second reader; the proof was written by another worker.

1. **Unchanged statements: PASS.** Compared the sole delivered module and node with
   the repository using `diff`. The existing theorem signature, from `theorem` to
   `:= by`, is byte for byte identical. There are no changed definitions, new public
   statements, or adapted modules. The final import change is declared in
   `coord/changes/coherentFormalModules_restriction_preservesKernel-imports.md`.
   Every affected downstream module retains the same public declarations through
   the unchanged public restriction-objects import; the record lists all 235.
2. **Proof and axioms: PASS, conditional on existing dependencies.** Compiled the
   delivered file using `lcompile.py`, and compiled a scratch copy with `#print axioms`
   for the main theorem and each private helper. No local `sorry`, forbidden command,
   or hollow definition occurs. The three new helpers, the imported power-quotient
   comparison and projection helper, and the transition-zero monicity helper use
   only `propext`, `Classical.choice`, and `Quot.sound`. The main theorem additionally
   has `sorryAx` from existing open dependencies, not a new local hole. Its local
   kernel object is eliminated from the existing construction theorem within a
   proposition; no arbitrary witness is installed as a definition. The quotient
   comparison is constructed from existing functors and the unique comparison of
   left adjoints, whose adjunctions are proved.
3. **Split-off statements: PASS (none).** No new holed theorem or node was added.
   Read all three proved private helpers: quotient comparison, its projection
   identity, and restriction of an image presentation. The image argument uses the
   preserved ordinary kernel followed by a restricted epi-mono factorization; it
   requires no formal abelian instance. For c=0 all used inequalities and transitions
   specialize to reflexive inequalities and identities; zero ideals, unit ideals,
   zero modules, and empty opens add no hypothesis. The quotient comparisons use
   n+1 uniformly and do not demand a nonzero ideal or nonempty scheme.
4. **Route and pruning: PASS after import cleanup.** Read the target proof top down,
   the construction and factorization interfaces, the proved transition-zero helper,
   and the quotient-comparison implementation. Verified the source route against
   [Stacks 087X](https://stacks.math.columbia.edu/tag/087X) and its quotient comparison
   against [Stacks 0887](https://stacks.math.columbia.edu/tag/0887). Independent
   LeanFinder, Loogle, and grep searches used image-preservation and kernel wording
   different from the first worker's search. Mathlib's `Abelian.PreservesImage.iso`
   also compares ordinary images, but still needs the kernel-domain comparison in
   this application; the existing epi-mono argument is valid and was retained.
   No shorter theorem establishing formal kernel preservation was found. Checked
   `dag/units/sk-thm-p1.json`: this item is below the realized unit steps, and none
   is bypassed. The only old proof-dependency edge no longer used directly is the
   affine ideal-product node, already listed above; it remains transitive.
5. **DAG agreement: PASS.** Only `proof`, `proof_deps`, and `proof_origin` differ in
   the existing node. Checked that `proof_deps` is exactly the union of step uses.
   The steps match the killed inclusion, limiting fork on X, restricted image and
   quotient presentations, transported transition-zero bound, limiting fork on U,
   and Mathlib's preservation-of-one-limit-cone criterion. The formal-kernel node is
   used for its proved private monicity helper, not its full kernel theorem; the
   pullback node is used for its proved quotient helpers. No new node is needed.

Changed only the three redundant imports identified above and this report; retained
all proof bodies. The import change record is
`coord/changes/coherentFormalModules_restriction_preservesKernel-imports.md`.
Closed holes: `AlgebraicGeometry.coherentFormalModules_restriction_preservesKernel` (1).
Added holes: none (0). Globally pruned modules: none.
