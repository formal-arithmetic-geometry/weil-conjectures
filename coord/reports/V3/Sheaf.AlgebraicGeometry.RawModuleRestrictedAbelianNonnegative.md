## What changed

The unchanged theorem `AlgebraicGeometry.Etale.exists_rawModule_restrictedAbelian_nonnegative`
now composes the module-to-abelian raw-Hom comparison with
`exists_raw_restricted_cohomology_natural_iso`. Its bundled naturality square follows by
`AddCommGrpCat.ext`, the scalar comparison equation, and the existing abelian comparison
equation. The restricted coefficient, group, and map agree definitionally with the abelian
constructions. Both new proof imports are private imports.

The new module `Sheaf.AlgebraicGeometry.RawModuleAbelianHomComparison` states only the
scalar-forgetting step, with an abelian raw-Hom group as its codomain. It does not assert a
restricted-cohomology comparison. This is a decomposition, not a fully closed proof.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.exists_rawModule_restrictedAbelian_nonnegative`
(node `lem-sbc-raw-module-restricted-abelian-nonnegative`).

Added one hole:
`AlgebraicGeometry.Etale.exists_rawModule_abelianHom_comparison`
(node `lem-sbc-raw-module-abelian-hom-comparison`).
There is no remaining sorry in the item's module and no new definition or axiom.
Net holes closed minus added in this delivery: zero; one scalar comparison is split off.
The existing abelian comparison may itself depend on previously stated open lemmas.

## No longer needed

No original imports were removed: both public imports are required by the signature.
No module is claimed pruned from the targets' closure. The old proof-dependency theorem
`higherDirectImageRawOverPullback_toSheaf`
(node `sbc-lem-higher-image-raw-over-naturality`) is not used by this proof: it concerns
sheafification, whereas the proof works directly on raw groups. Its module remains
transitively imported for the raw definitions. The old dependencies `lem-weil-pbc-injective-module-abelian-acyclic` and
`lem-weil-pbc-inverse-image-composition` are retained below the scalar-forgetting step,
not pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan conflated scalar forgetting with the already available abelian
raw-Hom/restricted-cohomology comparison. The new route separates them and reuses the latter.
The acyclicity theorem named by the original plan uses the SheafOfModules encoding, whereas
this module uses ModuleCat-valued sheaves; its application requires the existing constant-ring
module-sheaf equivalence. Forgetting scalars does not preserve injectives in general; only
sections acyclicity is required. The new statement respects this distinction.

The unit `sk-lem-failure-field` has no realized statement or step assigned to this node;
the new route does not bypass a unit-level statement. The new comparison is true in degree
zero by the ordinary sections adjunction, for a zero ring both raw groups vanish, and on an
empty etale object both section complexes vanish. It imposes no extra scheme hypotheses.

## New nodes

`lem-sbc-raw-module-abelian-hom-comparison` is stated in
`lean/Sheaf/AlgebraicGeometry/RawModuleAbelianHomComparison.lean`. It isolates scalar forgetting
between two raw derived-Hom presentations and their five-factor pullbacks. Its source is
Stacks Tags 03FD and 03Q8 and the latter's cited restriction lemmas; its docstring records the injective-resolution, sections,
and adjunction-naturality argument. No existing interface changes or forced adaptations.

## Second reading by V3

1. Compared the delivered module with the repository version. The existing theorem signature
is unchanged; only proof-only imports and proof text were added. The added comparison has its
own declaration and node.
2. Compiled both delivered modules with `lcompile.py`; the proofs contain no definition-level
`sorry`, axiom, unsafe, opaque, extern, or implemented_by declaration. The split comparison is
the only remaining sorry and is named in the report and DAG. Explicit `#print axioms`
on a scratch copy of the target and on the split declaration returned only `propext`,
`Classical.choice`, `Quot.sound`, and expected `sorryAx`; both compiled. The delivery
dry run passed, with review class CODEX for the new node and module.
3. Checked the split statement against the raw-Hom definitions and its stated sources. It is a
strict scalar-forgetting reduction, rather than a restatement of the target; its edge cases are
covered by the degree-zero and empty-object observations in the docstring.
4. Checked the proof route and imports. The target composes the scalar comparison with the
existing abelian restricted-cohomology natural isomorphism, and the bundled naturality proof
uses `AddCommGrpCat.ext` and the two pointwise naturality equations. The unit route is retained.
5. Checked the DAG records, proof dependencies, proof origins, and the `realized` unit route;
they agree with the Lean declarations. No shorter existing library theorem was found.

Changed the stale staged report to match report.md; corrected the new lemma's source citation
(Tag 09Z1 is a limit theorem, not the scalar comparison); restored original signature whitespace.
No Lean statement or definition was changed. Fresh leanfinder search for change of coefficients
on Ext returned general Ext equivalences only; fresh Mathlib grep for freeHomEquiv returned
ordinary module adjunctions only. Local rg confirmed the derived-direct-image comparison has
a different interface and does not supply the raw-Hom naturality equation.
