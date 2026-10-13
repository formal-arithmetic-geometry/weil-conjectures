## What changed

Proved `AlgebraicGeometry.exists_nonempty_open_flat_finitePresentation_restrict` without
changing its signature. It combines the existing generic-flatness theorem with a proved
new generic local finite-presentation theorem, intersecting their nonempty opens and
transporting both properties through restriction isomorphisms.

The new module `Sheaf.AlgebraicGeometry.GenericLocallyOfFinitePresentation` proves local
finite presentation using a finitely presented approximation with torsion kernel. The
existing algebraic generic-flatness theorem makes this approximation torsion free after
localization, so the localized surjection is an isomorphism. Finite presentation transports
across this isomorphism. Finitely many affine charts and source locality give the scheme
result. The torsion-cover theorem is reused directly from
`Sheaf.RingTheory.GenericFlatness` through a proof-only `import all`, which exposes
its private helper to this module. The private affine-cover helpers adapt the proved
argument in `Sheaf.AlgebraicGeometry.GenericFlatness`.

Updated the original node's proof route and added a node for the proved intermediate.
Both modules compile without warnings. The delivery dry run checks their axioms as well.
Empty source schemes and zero chart algebras are included: the finite cover may be empty,
and the ring argument makes no nontriviality assumption on the target algebra. No data
is defined by choosing a witness from an unproved existence theorem.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_nonempty_open_flat_finitePresentation_restrict`
(node `lem-sbc-generic-flat-finite-presentation`).

Also proved the new theorem
`AlgebraicGeometry.exists_nonempty_open_locallyOfFinitePresentation_restrict`
(node `lem-sbc-generic-flat-finite-presentation-lfp`). All private helpers are proved.
No holes added, no `sorry` left in either delivered module.

## No longer needed

No original imports were removed. The proof reuses the existing generic
flatness modules rather than adding new generic-freeness obligations. During construction,
removed unused imports of `WeilConjectures.Mathlib.RingTheory.FinitePresentation` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` from the new module;
also removed the now-unused
`Mathlib.RingTheory.MvPolynomial.Localization` import during this repair. These were
temporary imports, not removals from the existing library's target closure. No existing
module is claimed pruned. The duplicate private declarations
`RingHom.exists_fg_subideal_localized` and
`RingHom.exists_finitePresentation_torsion_cover` in the new module were deleted; the
existing torsion-cover theorem is imported and used instead.

The original node's old proof dependencies
`def-weil-finite-type-morphism`, `def-weil-flat-morphism`,
`def-pc-integral-scheme`, and `def-sbc-locally-finite-presentation` are no longer
separate proof dependencies of this argument: the two generic-open theorems now
carry those steps. They remain statement dependencies; their definitions still
occur in the unchanged signature. This removes no module from the target closure.

## Where the brief, the DAG or earlier work was wrong

Repaired the landing return: the earlier delivery duplicated two private theorems
already proved in `Sheaf.RingTheory.GenericFlatness`. Both copies are removed and the
existing torsion-cover theorem is now imported and used directly. No mathematical error found. The original plan did not list an algebraic generic-flatness
lemma among its dependencies; that lemma already exists and is used for the finitely
presented approximation. The new node makes the finite-presentation component explicit.
The unit route and target signature are preserved.

## New nodes

`lem-sbc-generic-flat-finite-presentation-lfp` states the generic local finite-presentation
component, fully proved in `Sheaf.AlgebraicGeometry.GenericLocallyOfFinitePresentation`.
Its proof depends on `lem-sbc-finite-type-algebra-generic-flatness`. No change record is
needed: no existing public interface changed.

## Second reading by V1

1. Compared the existing module byte for byte with its repository version using
   `diff`: only two proof-only imports and the theorem body changed. The existing
   declaration signature, docstring, visibility and all public imports are unchanged.
   The finite-presentation module and its node are new; no change record or forced
   adaptation is required. Verdict: pass.

2. Compiled both modules locally in import order with `lcompile.py --all`; both
   pass without warnings. Scratch copies printed axioms for the original theorem,
   the new public theorem, and all four private helpers: only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Text scans found no
   `sorry`, forbidden declaration, or kernel-check bypass. The approximation
   witness comes from a fully proved existence theorem; no unproved choice is
   used to define data. Verdict: pass.

3. There are no split-off unproved statements. Reviewed the proved new theorem
   and its helpers: torsion in the approximation kernel is killed by flatness
   over the domain; the localized surjection is therefore bijective and finite
   presentation transports by composition. Checked the empty source/empty affine
   cover, zero target algebra, and field base cases: none requires nontriviality
   of the target or an inhabited chart index. The new public theorem is only the
   finite-presentation component and is not a restatement of the conjunction.
   Independent LeanFinder, Loogle and grep searches using localization and scalar
   inversion terminology found localization/finite-presentation transport lemmas,
   but no generic finite-presentation theorem. Repository searches likewise found
   no replacement; the existing private torsion-cover theorem is reused directly.
   Checked Stacks Tags 051T and 052A against the written argument. Verdict: pass.

4. Read the proof from the original theorem downward: intersect the two generic
   opens, then use restriction locality and canonical arrow isomorphisms. The new
   component uses the existing proved algebraic generic-flatness theorem rather
   than adding obligations. Public imports in the new module supply signature
   notions; its torsion and generic-flatness imports are proof-only. All original
   public imports are preserved. The unit `sk-prop-normal-form` has no realized
   node pointing to this auxiliary lemma; its statement, steps and `realized`
   fields are untouched, and the slicing route is retained. Completed the report's
   list of all four replaced old proof dependencies, distinguishing these from
   pruning modules. Verdict: pass after this reporting repair.

5. Compared both node records to the declarations and proof steps. The original
   proof dependencies are exactly the two generic-open theorems applied; the new
   node records the algebraic generic-flatness dependency, source, full proof,
   searches, creation provenance, blueprint origin, chapter, unit and Lean
   declaration. The old node changes only `proof`, `proof_deps`, and
   `proof_origin`. No node statement changed. Verdict: pass.

Second reading changed only the report: corrected its claim about unchanged
existing dependencies and explicitly listed all replaced old proof dependencies.
The Lean proofs and DAG records required no repair.
