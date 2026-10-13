## What changed

In `Sheaf.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization`, replaced the
proof of `AlgebraicGeometry.Scheme.Modules.higherImageCohomologyPresheaf_isLocalized`
by an application of the existing
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_isLocalized_away`.
Added its module as a proof-only import. All existing signatures, public imports,
and definitions are unchanged. Updated the item's node proof and direct proof
dependencies to match this application. Both nodes belong to
`sk-thm-picard-coherence`, whose realized statement and steps are untouched.

The existing theorem includes precisely the same qcqs morphism, quasi-coherent
module, injective resolution, degree, affine open, and defining section. Its
explicit restriction-of-scalars instance is the instance already inferred in the
item's statement. Its two let-bindings merely name the same complex and presheaf.

## Proved and sorry left

Closed the only local hole (both sandbox modules compiled cleanly on second reading):
`AlgebraicGeometry.Scheme.Modules.higherImageCohomologyPresheaf_isLocalized`
(node `lem-pc-higher-image-cohomology-presheaf-localization`).
No holes added or split off. No sorry remains in the delivered module.

This is reuse of an existing statement, not an independent proof of localization:
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_isLocalized_away`
(node `lem-pc-section-cohomology-principal-localization`) already contains sorry
in the library and remains the outstanding localization obligation. The delivery
consolidates duplicate obligations without introducing a renamed new statement.

## No longer needed

No existing imports removed; they are public statement dependencies.
No modules are claimed globally pruned.
The item's direct proof no longer separately invokes
`lem-sc-invert-s-cohomology` (`Sheaf.AlgebraicGeometry.InvertSCOhomology`) or
`lem-weil-pbc-higher-direct-image-presheaf`
(`Sheaf.Paper.HigherDirectImagePresheaf`). The first remains a dependency of the
reused localization theorem. The second is not needed as a separate comparison
in this wrapper; no claim is made that it disappears from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The two independently introduced nodes
`lem-pc-higher-image-cohomology-presheaf-localization` and
`lem-pc-section-cohomology-principal-localization` state the same localization
assertion. Their only Lean presentation differences are binder order and explicit
let-bindings. Reusing the existing latter theorem avoids duplicating its lengthy
localization and resolution-comparison proof. No mathematical statement is disputed.

Validation: the scratch theorem in `scratch/ScalarCheck.lean` compiled with
`lcompile.py` (2.8 seconds, no warnings), checking that an arbitrary presheaf map's
inferred scalar structure agrees definitionally with the explicit
`Module.compHom` structure of the reused theorem. The dependency module
`Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalLocalization` was compiled in
the sandbox together with the item because its shared `.olean` was absent; both
modules then compiled cleanly with `lcompile.py --all`. The required
`deliver3.py M3 Sheaf.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization
--no-push` dry run printed OK. Nothing was pushed.


## Second reading by M3

1. **Unchanged interface — pass.** Compared both sandbox modules with the repository
   using `diff -u`. The item changes only one proof body and adds one plain,
   proof-only import. Every existing signature, definition, docstring and public
   import is byte-for-byte unchanged. The auxiliary sandbox copy of
   `SectionCohomologyPrincipalLocalization` is identical to the repository and is
   present only to compile the dependency missing from the shared cache; it adds
   no delivered change. No change record is required.
2. **Proof and trust — pass with the reported upstream hole.** Ran `lcompile.py
   --all` in import order: both modules compiled without warnings or errors.
   The item has no remaining `sorry`, forbidden trust declaration or definition
   change. Scratch-copy `#print axioms` checks for both localization declarations
   returned exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter remains because the existing reused localization theorem is open;
   this delivery does not establish an axiom-free localization theorem.
3. **Split statements — pass (none).** No new declaration, statement, node or hole
   is introduced. Checked the reused theorem's binders, complex, presheaf and
   scalar action against the item: the only differences are binder order and
   reducible let-bindings. The direct application compiles, confirming the
   inferred scalar structure agrees. Degree zero, zero or unit defining section,
   empty affine open and zero coefficients do not change this reduction.
   Independent LeanFinder search for localization of derived sections on preimages
   of distinguished affine opens found structure-sheaf localization lemmas only.
   Repository searches for `IsLocalizedModule.Away` and both declaration names
   found the existing reusable localization theorem and its already-used application
   in `HigherDirectImageSectionDenominators`, with no shorter proved result.
4. **Route and pruning — pass.** A direct application of the existing exact
   assertion is the shortest available reduction. The added import is proof-only;
   retained public imports supply statement vocabulary and instances. The report
   lists both old proof dependencies omitted by this direct proof, and makes no
   unsupported claim of global pruning. Both nodes belong to the same coherence
   unit. Its statement and single step are untouched; its existing `realized`
   arrays are empty, and this delivery does not alter or bypass them.
5. **DAG agreement — pass.** The updated node has one application step and exactly
   `lem-pc-section-cohomology-principal-localization` as its direct `proof_deps`.
   Its `proof_origin` records reuse, not an independent localization argument.
   Its Lean statement and all non-proof fields agree with the repository. There
   are no new nodes to validate and no relevant interface change records.

Second reading changed only this report: removed the obsolete pending-compilation
claim and recorded independent comparison, compilation, axiom, search and route
checks. The Lean proof and node were correct and are retained. Holes closed: one
local named theorem; holes added: zero; split off: zero. The reused existing
localization theorem remains open.
