## What changed

Proved `SheafOfModules.module_pullback_tensor_iso_tail` in
`Sheaf.CategoryTheory.ModulePullbackTensorIsoE`, with its original signature unchanged. Redundant direct public imports were removed
in the second reading without changing the transitive public import closure. Its proof now recovers the algebraic inverse-image interface from hI, uses the existing
`SheafOfModules.canonicalRingedTensorComparison_nonempty`, and identifies the resulting insertion
maps with the specified q using their insertion-of-one formulas. Naturality and normalization then
follow from the existing comparison fields. Both added imports are proof-only.

Added `Sheaf.CategoryTheory.AlgebraicInverseImageOfTransport`, containing the fully proved
`SheafOfModules.algebraicInverseImage_of_module_transport`. Its module graph equations follow
from hI and binary-product comparisons. On the regular module, the inverse image of the unit gives
an injective scalar action: it is the composite of eR and eI. Cancellation recovers ring addition,
multiplication, zero and one without assuming extra ring-compatibility hypotheses. The resulting
record has exactly the given I, eI and eR.symm. The binary graph helper is reused from its existing module; the product lift uses Mathlib directly.

Updated the item's proof route and added the recovery lemma's node. Read Stacks Project
`sites-modules.tex`, Tags 03D2, 03D7 and 03EL, and the algebraic-structure transport discussion
in `sites.tex`, Tag 00YV. The regular-module argument expands compatibility between existing
interfaces; it does not replace the proper-base-change unit or any of its realized steps.

Both delivered modules are compiled independently again during the second reading.
A declaration-scoped heartbeat allowance permits elaboration of its explicit scalar-extension
casts. No library interface or existing definition changes, and no consumer adaptations or
statement/definition change records are needed. The second reading adds the required import-only
record `coord/changes/module-pullback-tensor-tail-import-pruning.md`.
A source search for the item declaration finds only its unchanged parent
`Sheaf.CategoryTheory.ModulePullbackTensorIso` as an external user.

## Proved and sorry left

Closed 1 of 1 original textual holes:
`SheafOfModules.module_pullback_tensor_iso_tail`
(node `lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail`).
Added 0 holes; split off 0 unfinished statements. Neither delivered module contains a sorry.
The new recovery theorem is fully proved and introduces no private declarations.

Independent axiom inspection shows exactly propext, Classical.choice and Quot.sound for
`SheafOfModules.algebraicInverseImage_of_module_transport`. The item still depends transitively
on sorryAx through the pre-existing
`SheafOfModules.canonicalRingedTensorComparison_nonempty`
(node `lem-weil-pbc-canonical-ringed-tensor-comparison-construction`, module
`Sheaf.Paper.RingedTopoiTensorComparisonConstruction`). That existing obligation is reused,
not added, renamed or claimed as proved by this delivery. This is a proof of the item from an
existing named construction, rather than a transitive proof of the final targets.

## No longer needed

Removed the item's proof-only direct import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
Its former direct proof dependencies
`lem-pc-sites-sheaf-tensor-bilinear-universal` and
`lem-weil-pbc-sheafification-sets-exact` are replaced by the recovery lemma and the existing
normalized comparison construction. The tensor universal property remains needed inside that
construction, so this delivery claims no whole module pruned from the targets' import closure.
The explicit Hom/bilinear reconstruction, direct-image operation witnesses hP, module adjunction
am and mate equation hAdj are unnecessary in this proof; all existing binders stay identical.
The second reading additionally removed the redundant direct public imports
`Mathlib.CategoryTheory.Sites.Sheafification` and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` from the item: both remain
publicly available through `Sheaf.CategoryTheory.RingedSiteModules` and its public import
of `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
From the new recovery module, removed the redundant public import
`Mathlib.CategoryTheory.Limits.Preserves.Finite` and the redundant proof imports
`Mathlib.CategoryTheory.Limits.Types.Products` and `Mathlib.CategoryTheory.Sites.Limits`.
All three are already publicly reachable through `Sheaf.CategoryTheory.AlgebraicInverseImage`.
Its public import serves its statement; the proof-only
`import all Sheaf.CategoryTheory.RingedToposKFlatPullback` reuses the existing private graph helper.
These five direct-import removals
prune no additional whole module from the target closure.

## Where the brief, the DAG or earlier work was wrong

The original route repeated an available normalized comparison construction under a different
interface. The missing interface implication is genuine but provable: hI on the regular module
already forces the required ring graph equations. Merely assuming adjunctions would not do so;
this proof uses hI essentially and retains the corrected statement unchanged.

The blueprint ancestry utility returns no ancestor for the item because its created.item contains
a module name. The new node records the actual ancestry read from the parent node's blueprint:
`def-weil-pbc-four-corners`, through the underived and derived tensor comparison nodes.

Checked the recovery statement against the identity inverse image, the zero ring, and sites or
test sheaves with no sections. It assumes neither a nonzero ring nor a chosen global section:
the injectivity argument is at an arbitrary existing t, and equations with no such t are vacuous.
No source statement is disputed.

## New nodes

`lem-weil-pbc-algebraic-inverse-image-of-module-transport` records the fully proved recovery
lemma, with its exact Lean signature and detailed regular-module proof. This is not a new
unfinished item. No existing declaration had this direction of implication: the algebraic inverse
image node defines the compatible data, and geometric module transport constructs module data
from a compatible ring, whereas this lemma verifies ring compatibility from the given module
operations. Mathlib searches via LeanSearch, LeanFinder, Loogle and grep found product-comparison
APIs and generic module transport, but no recovery theorem. The search results are recorded in
the node and the sandbox search log. The import-only change record is
`coord/changes/module-pullback-tensor-tail-import-pruning.md`.


## Repair of the recorded return

The prior repair merely renamed the copied helpers. That did not address the landing tool's
explicit instruction to reuse existing statements. This second reading removes all three copied
private declarations. `graph_sections` (and its internal `graph_binary`) is reused through the
proof-only `import all Sheaf.CategoryTheory.RingedToposKFlatPullback`. The product-element step
uses Mathlib's `surjective_of_epi`, the isomorphism `prodComparison`, and
`Types.binaryProductIso` directly. Importing the other existing private helper from
`RingedTopoiCanonicalTensorPullback` was tested but removed: that module would add two unrelated
pre-existing holes to the target import closure. No such additional holes are imported now.

Also moved the recovery theorem's source-and-proof docstring from the first private helper to
`algebraicInverseImage_of_module_transport`, which it actually describes.

The source import graph adds only the recovery module and the existing comparison data and
construction modules to `TargetsCheck`. The latter construction's pre-existing hole becomes
reachable, while the item's original hole closes: net zero textual holes in that source closure
against the current shared tree. There are no new written holes and no whole modules pruned.
The pinned sorry ledger and the maintainer's global build remain the authoritative counts.

## Second reading by G4

1. **Signatures and public interface: pass.** Diffed the existing module against the shared
   repository. The entire signature of `module_pullback_tensor_iso_tail` is byte-for-byte
   identical. The recovery theorem is new. No definitions or target statements change.
   The public-import closure contains the same 1746 modules before and after the redundant
   direct-import removals. The import-only change record documents these removals; there
   are no forced adaptations.

2. **Proof and axioms: pass after repair.** Read the explicit construction of the
   `AlgebraicInverseImage` record, the cancellation argument on the regular module, and the
   tensor comparison's cast cancellation and insertion-map identification. All data are
   explicitly the supplied I, eI and eR.symm. The existing comparison's existential is
   eliminated only within a proof of a proposition. Both modules contain no sorry or
   forbidden construct. Fresh compilation and printed axiom results are recorded below.

3. **New statements: pass.** No unfinished statements are split off. The proved recovery
   theorem requires no nonzero ring or inhabited test section: the scalar action on the
   transported unit is injective because its underlying map is a composite of isomorphisms,
   even for the zero ring. With no test section its graph equations have no instance. The
   identity inverse image recovers ordinary module and ring operations. Repeated LeanFinder,
   Loogle and grep searches with free rank-one modules, coefficient-ring compatibility,
   epimorphism surjectivity and product comparisons found no existing recovery theorem.
   Project searches did identify the three duplicated private helpers; they have been
   removed and replaced with existing declarations and Mathlib APIs.

4. **Route and pruning: pass.** The existing canonical normalized comparison is the shorter
   available route. Its hypotheses are supplied by recovery and hTmap; q_one and hq identify
   the insertion maps, and its naturality and pure fields give the original conclusion.
   Checked the old proof_deps against `No longer needed`: both removed dependencies are
   listed. The proper-base-change unit's realized statement and three steps are unchanged;
   this auxiliary interface proof bypasses none of them. No whole-module pruning is claimed.

5. **DAG agreement: pass.** Both node Lean signatures match the code exactly. The existing
   node changes only proof, proof_deps and proof_origin. Its dependencies are the recovery
   theorem and existing normalized comparison construction. The new node has the source,
   regular-module argument, searches, creation and ancestry records, chapter/unit and exact
   Lean declaration. Its graph step now explicitly reuses the existing private helper and
   its pair-lifting step uses Mathlib's surjectivity API.

Second-reading changes: removed the three duplicated private helpers, reused the existing graph
helper through a proof-only import, used Mathlib directly for product lifting, placed the proof
docstring on the correct theorem, and corrected this report's dependency and progress accounting.

Independent validation after the repair: the recovery theorem compiled cleanly in 14.8 seconds;
the item compiled cleanly in 29.6 seconds. A fresh scratch copy printed exactly
`[propext, Classical.choice, Quot.sound]` for the recovery theorem. The unchanged direct consumer
`Sheaf.CategoryTheory.ModulePullbackTensorIso` compiled against the delivered modules in
24.2 seconds. The item's fresh scratch copy compiled in 28.0 seconds and printed exactly
`[propext, sorryAx, Classical.choice, Quot.sound]`, as expected from the existing comparison
construction's named hole.
