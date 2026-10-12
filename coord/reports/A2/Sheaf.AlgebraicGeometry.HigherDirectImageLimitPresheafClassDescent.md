## What changed

Replaced the proof hole in
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent` with a complete
Lean proof from the new affine representative theorem. The original signature and
docstring are unchanged, and both public imports are unchanged.

The proof constructs the affine open cover as etale S-objects, proves its generated
sieve covering using `Scheme.ofArrows_mem_smallEtaleTopology_iff` and
`Cover.iUnion_range`, and factors every sieve arrow through a generator with
`Sieve.mem_ofArrows_iff`. It obtains an actual stage higher-direct-image section on
that affine generator, transports it through `(eK i).inv`, uses `hη` and inverse/hom
cancellation to identify its image, and restricts along the factorization arrow.
Naturality of both `η` and the sheafification comparison proves the final equality.
The stage transition equation `hK` is unnecessary for this local lifting argument;
its binder remains unchanged.

Added `Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep`, with one
public theorem for the geometric part on affine objects. This theorem concerns
actual stage higher direct images and the canonical `abelianHigherDirectImageMap`;
it has no K, eK, hK, eta or h-eta parameters and no covering-sieve conclusion.
Its source and complete proof in words are in the docstring and its new DAG node.
The affine helper retains the planned comparison and complex-continuity imports.
Updated the original node's proof, proof dependencies and proof origin to match
its Lean proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_higherDirectImage_limit_presheaf_class_cover`
(node `lem-sbc-higher-direct-image-limit-presheaf-class-cover`). The item's module
contains no remaining sorry.

Added exactly one hole:
`AlgebraicGeometry.Etale.exists_higherDirectImage_limit_affine_class_rep`
(node `lem-sbc-higher-direct-image-limit-affine-class-rep`) in
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep`.
Its whole proof is `:= by sorry`.

This is a decomposition, not a completed geometric proof: one hole closed, one
added, net zero. The affine continuity and natural comparison compatibility remain
to be formalized. The cover construction, presentation transport and all-arrow
restriction argument are now proved in Lean.

Both delivered modules compile locally in import order. The new statement was
checked against Stacks Tags 09Z1 and 03Q8. Its affine hypothesis ensures the
base-changed stages are qcqs; it only claims representation of raw cohomology
classes, not of arbitrary higher-direct-image sections. The comparison is chosen
existentially and naturally, not asserted compatible for every abstract isomorphism.
For an empty affine U the assertion gives the zero section at any index (I is
nonempty); for p = 0 it specializes to section continuity. A singleton index system
reduces to the canonical pullback comparison along its limit projection. No
additional uniform cohomological bound is needed: the coefficient complexes are
concentrated in degree zero.

## No longer needed

Removed these direct proof imports from the item's module:
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`

They are retained as proof dependencies of the new affine helper, hence remain in
the import closure. The corresponding nodes
`sbc-lem-higher-direct-image-presheaf` and
`lem-weil-pbc-etale-cohomology-limit-complex-systems` are moved one level down,
not pruned. No node or module becomes unnecessary in the targets' closure.
No unit statement or realized step is bypassed; this follows the original affine
continuity route and completes its covering-sieve step.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The existing sheafification theorem
provides `Nonempty` of an isomorphism, with its natural construction private; its
public signature alone does not give the canonical comparison compatibility needed
for affine stage representatives. The new helper therefore packages that specific
natural comparison with affine cohomology continuity. The final cover argument
uses Mathlib's etale cover criterion and naturality directly.

LeanSearch returned Internal Server Error. LeanFinder, Loogle, Mathlib grep, and
searches in both library roots found no theorem supplying the missing affine
representative assertion. Loogle did find the Mathlib sieve coverage API used in
the completed proof.

## New nodes

`lem-sbc-higher-direct-image-limit-affine-class-rep`, at
`dag/nodes/sec-smooth-base-change/lem-sbc-higher-direct-image-limit-affine-class-rep.json`,
is the affine cohomology-continuity and natural-comparison part of original steps
1-3, before transporting into the presentation K or building a covering sieve.
It is stated in `Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep`.
Its proof uses the same presheaf comparison, complex cohomology continuity, and
canonical higher-direct-image map nodes as the original plan. It has the same
chapter and unit as the original node. There are no statement changes, definition
changes, adapted downstream modules, or change records.

## Second reading by A2

1. PASS: Diffed both delivered modules against the repository. The existing theorem's
   signature is byte-for-byte unchanged, as is its docstring. Its two public imports
   are unchanged; only private proof imports and its proof body differ. The helper is
   new. No definitions, target statements, or downstream modules are changed, so no
   statement-change record is required.
2. PASS as a decomposition: compiled both modules in import order with lcompile.py,
   without errors or warnings (8.4 s and 19.2 s). Scratch copies with #print axioms
   report only propext, Classical.choice, Quot.sound and sorryAx for both theorems.
   The item's proof has no sorry; the helper has exactly the reported named theorem
   with whole proof by sorry. No forbidden declaration or hollow definition occurs.
   The proof obtains existential witnesses locally within a theorem; it defines no
   data by choosing an arbitrary witness from an unproved existence theorem.
3. PASS: Checked the affine helper against Stacks 09Z1, 03Q8 and 0EZM. Base change
   to an affine U makes the stages qcqs and preserves affine transitions and limits;
   degree-zero coefficients have uniform lower bound zero. Continuity represents z
   by a stage cohomology class, whose natural comparison supplies y. Naturality of
   derived adjunction gives precisely the displayed canonical map. Empty U gives
   zero; p = 0 gives section continuity; a singleton system gives projection
   pullback. The one comparison e works naturally for all U. The helper removes
   K, eK, hK, eta, all covering sieves and all-arrow restriction conclusions; it is
   strictly the affine geometric part of the argument, not a renamed target.
   Repeated LeanFinder with a filtered-colimit/derived-Hom query, Loogle with
   cohomologyPresheaf, Mathlib grep, and rg over both Lean roots. The generic Ext
   cohomology presheaf, fixed-base continuity, and complex continuity theorems do
   not supply this canonical-map affine representation directly. Closing it requires
   formalizing the base-changed system and comparison compatibility, beyond a short
   repair. Its docstring and node provide the source and complete mathematical route.
4. PASS: Read the proof from its conclusion backward: factorization of sieve arrows,
   restriction naturality, inverse/hom cancellation under h-eta, and affine-cover
   coverage are all checked by Lean. There is no shorter existing geometric theorem
   found. Public imports support the signature; the affine helper is a private proof
   import. The two removed direct proof imports and both old dependency nodes are
   completely listed under No longer needed, and remain in the helper's closure.
   No module is pruned. Read sk-lem-failure-field's unit record: its realized fields
   are unchanged; affine continuity still follows the higher-direct-image limit
   route used by its step. No unit statement or step is bypassed.
5. PASS: Compared the existing node JSON: only proof, proof_deps and proof_origin
   changed. Their steps match the affine helper, cover criterion, transport and
   restriction argument. Both proof_deps lists equal the union of their step uses.
   The new node has the required source, searches, creation, blueprint ancestry,
   chapter/unit, status and verbatim Lean statement. No new dependency cycle is
   introduced: its dependencies are the original geometric dependencies.

Changed only this report by adding the independent second reading. No Lean or DAG
repair was necessary. One upper hole closed and one strictly simpler hole added;
net zero, with no fully axiom-clean geometric theorem claimed.
