## What changed

The original theorem `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_coordinate_representatives` now constructs its coordinates with the prescribed termwise complexes. The representative isomorphisms are actual composites of quotient/localization comparisons, inverse pinned counits, and derived images of `c.e` and `c.e'`. The chain map is explicitly the underived composition comparison followed by inverse-spectrum pullback of `c.t`.

Added proof-only imports of `IsomorphismPullbackCounit`, `AffineSpectrumRepresentativeMap`, and `KFlatPullback`. The public imports and every original declaration signature are unchanged. The original node's proof and proof dependencies now describe this construction.
Module-local opacity and backward transparency settings prevent expensive unfolding during
elaboration. The dry-run tool treats those commands conservatively as an interface change;
`coord/changes/affine-spectrum-representatives-local-elaboration.md` records their exact
old/new forms and the complete downstream inventory. No exported signature changes and
no downstream adaptations are made.

Added and proved `isIso_counit_of_isIso` and exported its shared K-flat computation
`counit_isIso_kFlat`: tensor pullback along an isomorphism agrees with exact open restriction; apply counit naturality to a K-flat resolution. The existing derived-pullback computation and left-derived uniqueness prove the pinned counit's invertibility on K-flat complexes. K-flatness of the prescribed source complex is proved from the existing pullback-preservation theorem.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_coordinate_representatives` (node `lem-pc-affine-spectrum-coordinate-representatives`). Its proof contains no sorry.

Also proved the new `AlgebraicGeometry.SingleComplexBaseChange.isIso_counit_of_isIso` (node `lem-pc-isomorphism-pullback-counit`), including the shared proved theorem `counit_isIso_kFlat`. The duplicate private theorem
`spectrum_counit_isIso_of_isKFlat` has been removed; the original module now uses
`counit_isIso_kFlat` through its existing proof-only import.

One hole added and left: `AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_representative_map_eq` (node `lem-pc-affine-spectrum-representative-map`), in its own module `Sheaf.AlgebraicGeometry.AffineSpectrumRepresentativeMap`. This is only the compatibility equation for the explicit chain map and already specified canonical representative isomorphisms. It constructs neither coordinates nor representatives and asserts no K-flatness or counit invertibility.

Original holes closed: 1. New holes added: 1. This is a decomposition, with net hole count zero, rather than a complete axiom-free proof of the original theorem.

## No longer needed

No modules or imports were pruned. The duplicate proved private helper
`spectrum_counit_isIso_of_isKFlat` was pruned; the shared counit computation is
proved once in `IsomorphismPullbackCounit`. The old direct proof dependency
`lem-pc-module-pullback-adjunction` is no longer directly used by the original theorem:
its use moved into `lem-pc-isomorphism-pullback-counit`, so it remains transitively needed.
The derived-pullback computation and composition nodes
`def-pc-derived-pullback` and `lem-pc-ringed-spaces-derived-pullback-composition`
are now dependencies of the shared helper rather than direct proof dependencies
of the original theorem. They remain transitively needed. No unit statement or
realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing refusal: the original delivery duplicated the K-flat counit
computation in two modules. The existing helper is now public, its statement and
proof are unchanged, and the target invokes it rather than reproving it. This
changes only a newly added module, not any existing library interface.

The plan's declarations do not directly state the chain-level equation relating underived composition to the pinned derived-composition comparisons after the quotient/localization identifications. That equation is now a precise separate item, with its explicit chain map in the statement.

`tools/blueprint_refs.py ancestor lem-pc-affine-spectrum-coordinate-representatives` reports ancestor `None` because the parent was created with a module name in `created.item`. The new nodes retain the parent's recorded ancestor `lem-pc-rf-perfect-base-change`, adding the current node to its recorded `via` chain.

Edge cases checked: zero complexes, empty schemes, unbounded complexes, and arbitrary target representatives. No K-injectivity of the target is assumed or needed: the map is transported from the supplied chain map `c.t`, rather than lifted from an arbitrary derived morphism. Arbitrary representative isomorphisms are not permitted by the remaining lemma: its two inverse equations pin them to the counits. No definitions, interfaces, target statements, or other groups' modules changed.

## New nodes

`lem-pc-isomorphism-pullback-counit`, module `Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit`, is proved. Source: Stacks 0D5S and 0098; the Lean proof uses exact open restriction and a K-flat resolution.

`lem-pc-affine-spectrum-representative-map`, module `Sheaf.AlgebraicGeometry.AffineSpectrumRepresentativeMap`, is the remaining equation. Source: Stacks 0D5S, the composition calculation underlying 0DJ8's affine reduction. Its proof in words expands both left-derived factorization equations, uses counit and quotient-comparison naturality, substitutes the prescribed inverse equations, and applies `c.represents`.

For both nodes, LeanSearch was attempted and returned HTTP 500 (recorded as unavailable); LeanFinder returned no exact match. Source searches found the ingredients `quotientCompQhIso`, `tensorPullbackCompositionIso`, exact restriction, and abstract left-derived uniqueness, rather than either complete statement. Blueprint searches found no duplicate blueprint node. Change record: `coord/changes/affine-spectrum-representatives-local-elaboration.md`.


## Earlier second reading (a previous round; superseded)

1. Compared all three delivered modules with the repository. The two helper modules
   are new; the original theorem's signature and existing public imports are unchanged.
   Repaired the extra space before its proof delimiter so the signature is byte for byte
   identical. The module-local options/attributes have the declared change record and
   affect elaboration only. No definition, target statement, or other module was edited.
2. Compiled the complete set locally without errors or warnings. Exactly one named
   sorry remains, `affineSpectrum_representative_map_eq`; no forbidden declarations or
   hollow definitions occur. A scratch `#print axioms` check found only propext,
   Classical.choice and Quot.sound for `isIso_counit_of_isIso`; the original theorem and
   the compatibility lemma additionally use sorryAx. The scratch file was removed.
   The counit proof correctly uses exact restriction, a K-flat resolution, and naturality;
   the explicit complexes, isomorphisms, and map in the original proof are constructions,
   not arbitrary witnesses chosen from an unproved existence theorem.
3. Read the remaining compatibility statement and its complete docstring argument.
   It is strictly the represents equation for a specified termwise chain map, conditional
   on pinned inverse equations for e and eprime. It neither asserts existence of Coordinates
   nor supplies K-flatness or counit invertibility. Checking zero complexes, identity maps,
   empty schemes, and an arbitrary non-K-flat target gives no extra hypothesis or failure:
   exact inverse-spectrum pullback handles the target, and c.represents supplies its map.
   Expanded the actual definitions of both composition comparisons to verify their
   directions agree. Independent LeanFinder/Loogle/grep searches using left-derived
   transformation/factorization and localization terms found generic factorization and
   naturality ingredients, not this specialized equation. Local searches likewise found
   no existing public theorem to replace either new statement. The remaining diagram
   calculation was not closed during this reading; the delivery remains a decomposition.
4. Reviewed the route from the original theorem downward. All extra imports of that
   module are proof-only; all public imports of the new modules occur in their signatures.
   The original adjunction dependency remains transitively used by the new counit theorem;
   corrected No longer needed to state its removal from the direct dependency list.
   No module was pruned. The unit sk-thm-picard-semicon has realized statement=[] and
   steps=[[]] in the repository; this delivery does not modify or bypass a realized node.
5. Compared the original node's changed fields and both new nodes with the Lean code.
   Only proof, proof_deps and proof_origin changed on the old node. New nodes have their
   source, full statement, proof steps, searches, creation and blueprint provenance, unit,
   chapter and Lean records. Dependencies are the union of the recorded steps and match
   the construction and remaining equation. All records agree with the delivered code.

Changes in this reading: restored exact signature whitespace, clarified direct versus
transitive adjunction dependency in the report, and corrected the new counit docstring's
Tag 0098 description to “stalk formula for pullback, specialized to an isomorphism”.
Tag 0D5S supplies derived composition; Tag 0DJ8 supplies the motivating affine reduction.
Both cited pages and Tag 0098 were checked against the Stacks source.

## Second reading by P4

1. PASS. Independently diffed the original module against the repository and checked
   its entire theorem signature byte for byte. All existing public imports, signatures,
   definitions, and docstrings are unchanged. The two helper modules are new. The local
   elaboration commands are covered by the supplied change record; they do not alter
   exported declarations or target meanings. No other library module is adapted.
2. PASS as a decomposition. Compiled all three delivered modules in import order with
   lcompile.py: no errors or warnings. A scratch copy with #print axioms verified that
   isIso_counit_of_isIso and counit_isIso_kFlat use only propext, Classical.choice and
   Quot.sound. The coordinate theorem and affineSpectrum_representative_map_eq additionally
   use sorryAx, as reported. Removed the scratch copy after checking. There is exactly
   one delivered sorry, the named compatibility theorem; no forbidden commands and no
   hollow definitions. P0, N0, e, eprime and t are explicit constructions. The resolution
   witness is obtained from a proved resolution theorem, not an unproved existence hole.
3. PASS. Read the full remaining statement and its docstring proof, then expanded
   affineSpectrumDerivedPullbackIso, counit, and tensorPullbackCompositionIso in the
   repository. The derived comparison is pinned to the counit factorization; the
   underived comparison has the inverse orientation, as the chain map requires.
   The assumptions he and heprime pin the representative identifications and do not
   constrain the given coefficient map beyond c.represents. The equation follows by
   factorization and naturality, including transport along isoSpec naturality. For
   identity scheme maps these are the unit comparisons; for zero complexes and empty
   schemes the same diagram calculation applies. N need not be K-flat or K-injective:
   pullback along its spectrum isomorphism is exact. This is strictly a compatibility
   subproblem, not a restatement of existence of Coordinates.
   Fresh LeanFinder/Loogle/grep searches used left-derived factorization and composite
   natural transformation terminology. They found leftDerived_fac_app and
   leftDerivedNatTrans_fac, not the specialized equation. Repository searches found
   private K-flat counit helpers in SingleComplexBaseChangeStalkCondition,
   TensorCounitOneKFlatCoordinates and CounitStalkConditionFromLocalizedComparison;
   none is accessible for reuse. The new shared public helper avoids repeating this
   computation within this delivery. No short complete proof of the compatibility
   diagram was found. Rechecked Stacks 0D5S and 0098: they provide derived composition
   and the stalk pullback formula respectively; these are ingredients rather than a
   literal statement of the new specialized Lean equation.
4. PASS. Reviewed the route from the original theorem downward: actual termwise
   complexes, K-flat pullback preservation, exact isomorphism counits, the explicit
   chain map, and the remaining diagram equation. All added imports of the original
   module are proof-only. Public imports of the new compatibility module supply types
   or definitions appearing in its statement. The report accounts for all three old
   dependencies removed from the direct list (adjunction, derived-pullback definition,
   and derived composition); they remain transitively used. No module is pruned.
   The recorded unit has realized.statement=[] and realized.steps=[[]]; no recorded
   unit statement or realized step is bypassed or changed.
5. PASS. Compared the old node JSON: only proof, proof_deps and proof_origin differ.
   Checked the three Lean records against their verbatim signatures and checked that
   each proof_deps is the union of the recorded steps' uses. The new nodes have source,
   natural-language argument, searches, creation, blueprint provenance, chapter, unit
   and Lean records. Their dependencies match the actual reductions.

Changes in this reading: appended this independent review and clarified the search
finding that existing K-flat counit computations are private and cannot be imported.
No Lean proof or statement needed repair. Holes closed: the original
exists_affineSpectrum_coordinate_representatives; holes added:
affineSpectrum_representative_map_eq. Net zero, a decomposition. The two new counit
results are proved without sorryAx; the original result is not yet axiom-free.
