## What changed

Completed and compiled a reduction of `AlgebraicGeometry.Scheme.Modules.orderedCech_module_retraction`
into two independent cochain-map constructions. The item's statement and public imports
are unchanged. Added proof-only imports of `OrderedCechModuleRestrictionMap` and
`OrderedCechModuleSignedSection`.

The first new theorem constructs restriction with its ordered-coordinate equation; the
second constructs signed extension with its ordered-coordinate equation. Neither asserts
the retraction identity, nor takes the other map as input. The item's proof derives the
identity by injectivity of `a`, pointwise extensionality, and zero negative terms.

Validation: all three delivery modules compile through `lcompile.py --all`, with no
compiler errors. The delivery dry run also passes its compilation, axiom probe and
preflight checks, except for the second reading reserved for the next worker. The previously missing coordinate dependency is now available in the
published snapshot. The full combining proof and the two new theorem signatures are
therefore checked by Lean. Scratch checks of the assembly and degreewise naturality
remain outside the delivery.

## Proved and sorry left

Decomposition: one original hole is closed by a compiled combining proof, with two
strictly smaller holes added. There are no sorries left in the item module. Progress measured as holes closed minus holes added is -1 (one closed, two added);
no net reduction is claimed.

Original declaration whose body was replaced:
`AlgebraicGeometry.Scheme.Modules.orderedCech_module_retraction`
(node `lem-pc-ordered-cech-module-retraction`).

Sorries left in new modules:

- `AlgebraicGeometry.Scheme.Modules.orderedCech_module_restriction`
  (`lem-pc-ordered-cech-module-restriction-map`), in
  `Sheaf.AlgebraicGeometry.OrderedCechModuleRestrictionMap`.
- `AlgebraicGeometry.Scheme.Modules.orderedCech_module_signedSection`
  (`lem-pc-ordered-cech-module-signed-section`), in
  `Sheaf.AlgebraicGeometry.OrderedCechModuleSignedSection`.

Each has exactly a whole-theorem `by sorry`, a source, and a complete natural-language
proof. There are no definitions or additional holes in the delivery. The corresponding
map constructions are independent parts of the existing three-step plan.

## No longer needed

No module is pruned. Both old immediate proof dependencies are accounted for:
`def-pc-ordered-cech-module-coordinates` remains a statement dependency and is used
by both new construction nodes; `lem-pc-signed-cech-extension-differential` moves
to the signed-section node. The coordinate definitions remain necessary for both statements. The signed
extension differential remains necessary below the signed-section construction. It has
moved from the item's immediate proof dependencies to that new node's dependencies; it
is not pruned. No original import is removed and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked because its required coordinate module was absent
from the published compiled snapshot. That publication issue is resolved: all delivery
modules now compile against the available dependency. No source dependency was copied
or changed to work around the publication issue.

No mathematical error was found in the statement. Checked the empty family (all ordered
coordinate products are trivial), degrees greater than the family size, the zero module,
degree zero, and the negative-degree boundary. For signed extension, repeated tuples
must be zero and their surviving faces cancel; this remains precisely the existing
`signedCechExtension_differential` dependency. The constructions use local ring linearity,
not only linearity over global sections.

Searches: LeanFinder returned Moore-normalization and simplicial splitting theorems,
which do not identify the ordered complex here; Loogle returned complex extensionality;
LeanSearch was unavailable (Internal Server Error); msearch grep had no hits. Direct rg
and source reading found the existing coordinate lemmas and signed-extension theorem,
but no module-sheaf map assembly theorem. Blueprint searches for ordered Cech and signed
extension found no blueprint nodes. The unit's realized arrays are empty; its route is
preserved by splitting only the existing local retraction argument.

## New nodes

`lem-pc-ordered-cech-module-restriction-map` isolates construction of ordered restriction
as a module cochain map and its coordinate equation, without any extension or splitting
assertion. Its degreewise naturality and scalar assembly were independently tested in
scratch Lean. The differential transport is still part of this named hole.

`lem-pc-ordered-cech-module-signed-section` isolates signed extension as a module cochain
map and its increasing-coordinate equation, without mentioning a restriction map or
asserting a retraction identity. It uses the existing signed differential theorem.

Both follow Stacks Tags 01FJ and 01FK and retain the item's chapter, unit and blueprint
ancestor. No statement, definition, visibility or interface of an existing declaration
changes, and there are no change records or forced adaptations.


## Second reading by U1

1. PASS. Diffed the existing module against the repository. Its full theorem
signature is byte-for-byte identical. Only its proof and two plain proof imports
change. Diffed its node: only proof, proof_deps and proof_origin change. There are
no target, definition, interface or forced-adaptation changes.

2. PASS as a decomposition, not a completed axiom-free proof. Compiled the three
modules locally and compiled a scratch copy with #print axioms for all three
public theorems. Each reports precisely propext, Classical.choice, Quot.sound and
sorryAx. The latter is expected from the two named, whole-theorem holes listed
above. Scanned all delivered Lean for forbidden declarations and attributes;
there are no definitions, hidden holes or extra axioms in this delivery. The
existential maps are eliminated inside a Prop proof, not chosen as data of a
definition from an undetermined existence witness.

3. PASS. Read both new statements and their complete construction docstrings.
Restriction and extension are independent proper parts of the old argument;
neither restates the retraction nor assumes the other map. Checked r=0, p+1>r,
the zero module, degree zero, and the -1 boundary: empty ordered coordinates force
K's nonnegative section groups to be zero; restriction is zero and signed
extension is zero above the family size, where repeated-face cancellation still
applies. No covering hypothesis is used. Local scalar compatibility is supplied
by hl and hlinear, and naturality by hn and e. Verified the underlying routes
against [Stacks 01FJ](https://stacks.math.columbia.edu/tag/01FJ) and
[01FK](https://stacks.math.columbia.edu/tag/01FK); their coordinate arguments extend
to arbitrary families since they use no cover-dependent operation.
Independent msearch queries used "natural locally linear morphism from all tuples
Cech cochains to increasing index cochains" (LeanFinder), SheafOfModules.Hom
(Loogle), and alternating restriction / Cech section / Cech retract (grep).
Results give generic morphism constructors, no matching module-sheaf theorem.
Direct rg and source reading found AlternatingCechSection and AlternatingCechComputes:
they concern additive section complexes, so still require the naturality, local
scalar and product-transport assembly isolated here. Neither split hole can be
closed by a few-minute application of those results.

4. PASS after a dependency-import repair. Read the target combining proof from
its two coordinate identities downward; injectivity and extensionality suffice
and negative components follow from hK. The public coordinate import is needed
by the signature, and both new plain imports are used by the proof. Accounted
for both old proof dependencies under No longer needed. No module is pruned.
The unit sk-thm-picard-coherence has empty realized statement and step arrays;
no unit realization or step is bypassed or altered.

5. PASS. Checked each node's proof_deps equals the union of its proof-step uses,
its Lean declaration and statement match its module, and each new node has its
source, searches, split status, creation provenance, blueprint ancestor, chapter,
unit and Lean record. The original node now describes exactly the compiled
combining proof. The new signed-section node retains the existing differential
lemma as a proof dependency.

Changes by the second reader: added a plain import of SignedCechExtension to the
new signed-section module so that its planned differential dependency is present;
corrected the author line of both newly created modules to U1; made the list of
old dependencies explicit in No longer needed. Kept all mathematical statements,
the combining proof and the two construction holes unchanged. No additional
holes were closed or added in this second reading.
