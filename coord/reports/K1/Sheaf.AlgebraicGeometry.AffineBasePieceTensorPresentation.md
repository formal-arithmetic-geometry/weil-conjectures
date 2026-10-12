## What changed

The item's statement and existing docstring are unchanged. Its proof now uses
`exists_affineOpen_directedRingSystem` at k and the inverse image W_k of W, followed by
`exists_affine_base_piece_tensor_comparison`. It specializes that comparison to the cone leg
and every later transition. Cone naturality and functoriality identify the composites with
the original base-change morphisms.

The new module `Sheaf.AlgebraicGeometry.AffineBasePieceTensorComparison` proves the finite-type
coordinate-ring construction. The private `stageLft` proves local finite type of the
`Over.pullback` map by pullback pasting. The private `specModel` explicitly constructs the
base algebra maps from global sections, proves finite type by `finiteType_appLE`, and proves
the two spectrum compatibilities by naturality of `isoSpec` and the Spec–global-sections
counit. The public comparison theorem applies these to the affine target and source opens.
Only the remaining geometric base-change comparison is isolated in
`Sheaf.AlgebraicGeometry.AffineBasePieceTensorBaseChange`.

Both new statements are independent of inverse systems, cones, directedness and colimits.
The remaining geometric theorem is independent also of finite type and affineness hypotheses:
it starts with specified compatible spectrum models. Thus it is a strictly geometric part
of the original argument, rather than a renamed presentation theorem.

## Proved and sorry left

The item's one original hole is replaced by a proof of
`AlgebraicGeometry.exists_affine_base_piece_tensor_presentation`, node
`lem-weil-pbc-affine-base-piece-tensor-presentation`. This is a decomposition, not a claim
that the entire import closure is sorry-free: one hole closed and one new hole added, net 0.

New proved declaration:
`AlgebraicGeometry.exists_affine_base_piece_tensor_comparison`, node
`lem-weil-pbc-affine-base-piece-tensor-comparison`, including the finite-type algebra
construction and its spectrum compatibilities. Its private helpers `specModel` and `stageLft`
are proved without holes.

The delivery leaves exactly one new sorry:
`AlgebraicGeometry.affine_base_piece_tensor_base_change`, node
`lem-weil-pbc-affine-base-piece-tensor-base-change`. Its proof is exactly `by sorry`; its
complete intended argument and sources are in its docstring and node. The existing
`AlgebraicGeometry.exists_affineOpen_directedRingSystem`, node
`lem-weil-pbc-affine-open-directed-ring-system`, is used unchanged; it is an existing
statement, not an added hole.

Validation (2026-10-12): the missing existing ring-system module has reached the
compiled-library cache. The prescribed `lcompile.py --all` now compiles all three delivery
modules without warnings (2.3, 2.8 and 3.8 seconds). In particular, the actual presentation
proof is checked against the existing declaration, rather than a parameterized scratch test.
The earlier five retries were blocked on that missing artifact; the blocker is resolved.
The existing ring-system theorem is proved in the current source and is reused unchanged.
`deliver3.py K1 Sheaf.AlgebraicGeometry.AffineBasePieceTensorPresentation --no-push`
printed OK: the delivery compiles and passes preflight except for the second reading,
which the next reader supplies. Nothing was pushed.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.LimitAffineTransition`. Its
mathematics remains needed through the reused ring-system theorem; this is not a claim
that the module disappears from the targets' transitive closure.

The item's direct proof dependencies no longer separately list
`lem-weil-pbc-affine-morphism-permanence`,
`lem-weil-pbc-morphism-into-affine-scheme`,
`lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-spec-colimit-limit`,
`def-weil-pbc-category-colimit`, `lem-weil-pbc-lft-base-change`,
`lem-weil-pbc-lft-affine-pairs`, `lem-weil-pbc-open-fibre-product`,
`lem-weil-pbc-cartesian-square-pasting`, and `lem-weil-pbc-fibre-product-affine-spectra`.
They are incorporated into the ring-system theorem and the two new comparison nodes,
where needed. None is asserted globally unnecessary. No public imports were removed and
no additional module is claimed globally pruned.

The finite-presentation-only `Sheaf.AlgebraicGeometry.AffineChartTensorComparison` and
`Sheaf.AlgebraicGeometry.AffineChartDirectedRingModel` were inspected but are not imported:
the item's local finite-type hypothesis does not imply local finite presentation.

## Where the brief, the DAG or earlier work was wrong

The DAG's four-step plan is mathematically usable, but does not itself provide the
finite-type compatible-spectrum base-change lemma. The related existing chart lemma
requires finite presentation and is therefore too restrictive here. The construction in
step 3 is now proved directly, and the geometric portion of step 4 is isolated explicitly.

The local literature/stacks-project TeX files named by the nodes are absent on this machine.
The cited sources were read from the official Stacks pages instead:
[01ZO](https://stacks.math.columbia.edu/tag/01ZO),
[01YX](https://stacks.math.columbia.edu/tag/01YX),
[01YW](https://stacks.math.columbia.edu/tag/01YW),
[01JR](https://stacks.math.columbia.edu/tag/01JR),
[01I4](https://stacks.math.columbia.edu/tag/01I4), and
[01T2](https://stacks.math.columbia.edu/tag/01T2).

Searches used msearch.py with LeanFinder, Loogle and grep. LeanSearch returned an internal
server error and is recorded as unavailable, not as a negative result. The unit
sk-thm-p1's realized statement and steps are unchanged; this work refines only an auxiliary
node below them. No statement or definition of the library was changed.

## New nodes

`lem-weil-pbc-affine-base-piece-tensor-comparison` records the new proved finite-type
single-base-piece construction and universal comparison. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineBasePieceTensorComparison.lean`. The rings and algebra
map are built explicitly in Lean; the geometric compatibility is delegated to the next
node. The affine stage is guaranteed by the given affine transition and affine base-changed
morphism. Empty V or W gives zero coordinate rings, and is admitted throughout.

`lem-weil-pbc-affine-base-piece-tensor-base-change` records the remaining geometric
comparison, in `lean/Sheaf/AlgebraicGeometry/AffineBasePieceTensorBaseChange.lean`. It takes
arbitrary original schemes and opens, specified compatible spectrum models and an arbitrary
further base morphism with its compatible spectrum model. It asserts the resulting tensor
arrow isomorphism, without a finiteness or limit assertion. For t=id it specializes to the
original spectrum model; zero rings and empty charts obey the same pullback identities.
The base compatibilities are explicit, so arbitrary algebra structures cannot be substituted.

No change record is needed: no existing signature, definition, or public import was changed.

## Second reading by K1

1. **Visible declarations: pass.** Read all three delivery modules and diffed each
   against the repository. The comparison and base-change modules are new. The existing
   presentation module changes only two private proof imports and the proof body; its
   declaration signature and existing docstring are byte for byte unchanged. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`. No definition, existing
   statement, target, or public import changes; no change record is required.
2. **Proof and axioms: pass as a decomposition.** Independently ran the prescribed
   `lcompile.py --all`: all three modules compile without warnings. Scratch copies under
   `scratchpad/second-reading` print axioms for every delivered public theorem and both
   private helpers. `specModel` and `stageLft` use only `propext`, `Classical.choice`, and
   `Quot.sound`. Each public theorem additionally uses `sorryAx`, accounted for by the
   named geometric hole. Scanned every delivery Lean file: exactly one `sorry`, in
   `affine_base_piece_tensor_base_change`, and no prohibited declaration or implementation
   mechanism. There are no holed definitions or arbitrary data chosen from an unproved
   existence theorem: B, C, the base algebra maps and phi are explicitly constructed.
3. **Split statements: pass.** The remaining statement separates geometry from the
   proved finite-type algebra construction and the reused directed-ring/limit construction;
   it has no finiteness, inverse-system or colimit claim. It is strictly a part of the
   original argument, not a renamed presentation. Its specified spectrum models and the
   three compatibility equations determine the structure maps used by the pullbacks.
   Checked t=id, d=id, empty V, empty base open and zero rings: the same universal
   properties apply, with no omitted nonemptiness requirement. Read the complete docstring
   argument and matching node. Independently verified the open and affine pullback
   ingredients against [01JR](https://stacks.math.columbia.edu/tag/01JR) and
   [01I4](https://stacks.math.columbia.edu/tag/01I4), and the finite-type affine-pairs
   criterion against [01T2](https://stacks.math.columbia.edu/tag/01T2).
   Ran fresh LeanFinder, Loogle and local searches with different queries. In particular,
   read the proved `exists_affineChart_baseChangeIso`: it supplies individual chart
   isomorphisms, but still requires composite pullback pasting and map compatibility here.
   The existing chart tensor comparison requires local finite presentation. No duplicate
   or immediate application closes the remaining geometric statement in a few minutes.
4. **Route and pruning: pass.** The proof uses the proved ring-system theorem first,
   then the explicit coordinate-ring construction; only the geometric comparison remains
   open. Checked the cone naturality and transition composition equalities used in the
   two specializations. Every Mathlib import of the new modules supplies types, operations
   or instances needed by their public signatures; the comparison helper import is private.
   The existing public imports are preserved. Compared old and new direct `proof_deps`:
   all ten removed entries are listed in `## No longer needed`; the removed direct
   LimitAffineTransition import remains transitively needed, so no globally pruned module
   is claimed. Read `dag/units/sk-thm-p1.json` and its `realized` route: this auxiliary
   refinement changes none of the unit's statement or steps.
5. **Nodes: pass.** Read all three delivery nodes against Lean. The presentation's
   new proof steps describe the actual ring-system and comparison applications. The
   comparison node records the explicit algebra construction, finite-type criterion,
   spectrum naturality and remaining geometric dependency. The base-change node records
   the still-open universal-property argument. Both new nodes have the source, searches,
   creation, blueprint, chapter/unit and Lean records required by the standing brief.

Second reading changed no Lean proof or statement. Corrected the base-change node's
misleading provenance note, which said the algebra construction was verified in that node:
the geometric theorem is still open, and the algebra construction is verified in the
separate comparison module. Added independent search evidence to that node and this review.
The hole accounting remains one original hole closed, one new geometric hole added,
net zero: a decomposition, not a sorry-free proof of the import closure.
