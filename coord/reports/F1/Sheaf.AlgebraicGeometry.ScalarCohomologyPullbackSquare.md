## What changed

Proved `AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_square` from the
single-path composition identity in the new proof-only import
`Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition`. The existing
signature, public import and definitions are unchanged. Four private, proved
helpers establish coefficient-map composition, identity, equality transport,
and cancellation for three general isomorphisms. Both modules compile cleanly
with lcompile.py --all (about two seconds each).

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_square`
(node `lem-sc-scalar-cohomology-pullback-square`). No sorry remains in the item.
Added one hole: `AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_comp`
(node `lem-sc-scalar-cohomology-pullback-composition`), in its own new module.
This is a decomposition, with net zero holes closed, not a complete proof of
composition. The remaining statement treats one composable pair, has no second
path or square equality, and is used twice. Equality transport and cancellation
are proved independently in the item, rather than restated as a new obligation.
The docstring spells out the normalized adjunction, scalar inverse-image unit,
Ext-composition and resolution-naturality steps still needed. Degree zero,
identity arrows, zero coefficients and empty schemes impose no missing hypotheses.

## No longer needed

No existing imports were removed. No module is claimed globally pruned.
The square's direct proof dependency on `lem-pc-module-pullback-identity-composition`
(`Sheaf.AlgebraicGeometry.TensorPullback`) moves to the new composition node;
it remains needed there. The square needs only the scalar operations and the new
composition law. No other planned dependency is bypassed. The unit
`sk-prop-av-cube` and its route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The original DAG describes the mathematical argument but gives no declaration
for its scalar composition/normalization step. The existing tensor-pullback
composition theorem supplies existence of an isomorphism, not compatibility of
the chosen normalized isomorphism with the Ext-defined scalar pullback.
The analogous etale cohomology theorem has a different site and coefficients.

Directly unfolding concrete adjunction comparisons during coefficient algebra
caused kernel deterministic timeouts. Proving the coefficient algebra for general
isomorphisms and specializing the resulting theorem avoids expanding those
comparisons; no definition, limit or compiler setting was changed to evade this.
The referenced Stacks TeX files are not present locally. Read official Tags
0097, 01F7 and 01FD online; 01FD concerns Cech-to-derived compatibility, while
01F7 is the direct source for the resolution-defined cohomology map.

## New nodes

`lem-sc-scalar-cohomology-pullback-composition`: the one-path composition step
of the original square proof, stated as `scalarCohomologyPullback_comp` in
`Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition`. It has a complete
proof in words, source attribution and LeanSearch/LeanFinder/Loogle/grep searches.
LeanSearch returned Internal Server Error; no match claim is based on it.
No change record is needed because no existing signature or definition changes.

## Second reading by F1

1. Compared the delivered square module with the repository using diff. Its only
   existing declaration is scalarCohomologyPullback_square. Restored two spaces
   of indentation in its conclusion, then extracted and compared the complete
   signature byte for byte: identical. Its docstring, public import, visibility,
   universe and all hypotheses remain unchanged. There are no changed definitions
   and no forced adaptations. The composition module is new.
2. Compiled both modules in import order with lcompile.py --all: no errors or
   warnings. Read all four private proofs: map_comp and map_id are derived from
   the cohomology functor; equality transport eliminates the arrow equality;
   three-iso cancellation uses inv_hom_id in the correct order. The final proof
   instantiates the three factors of scalarPullbackSquareIso exactly. There is
   precisely one sorry, the named public scalarCohomologyPullback_comp, and no
   axiom, unsafe, opaque, implemented_by, extern or hollow definition in either
   delivered module. Scratch #print axioms checks show only propext,
   Classical.choice, Quot.sound and sorryAx (the new obligation and existing
   upstream open proofs); this is not an axiom-closed proof of the target.
3. Read the definitions scalarPullbackCoefficient, scalarInverseUnitIso,
   scalarCohomologyExtEquiv, scalarCohomologyPullback, scalarPullbackCompIso and
   scalarCohomologyMap. The inverse comparison in the composition conclusion has
   the correct direction. Checked the composition obligation against Stacks
   https://stacks.math.columbia.edu/tag/0097 and the resolution construction at
   https://stacks.math.columbia.edu/tag/01F7, especially
   cohomology-equation-functorial and Remark 20.14.2. Its three schemes, arbitrary
   coefficient sheaf, degree and class require no flatness, quasi-coherence or
   compactness. For degree zero it is the unit/section composition identity;
   identity arrows reduce to the normalized unit comparisons; zero coefficients
   and empty schemes give zero groups. The docstring supplies the coefficient,
   constant-unit, Ext and resolution-comparison argument. It is a one-path
   statement used twice, with the square equality and cancellation proved
   separately, not a renaming of the square. Independent LeanFinder query
   "Functoriality of derived global sections for successive coefficient maps of ringed spaces"
   found section-map composition results only; Loogle query
   `"mapExactFunctor", "comp"` found three generic Ext algebra lemmas, and
   msearch grep `cohomology.*comp|comp.*cohomology` in AlgebraicGeometry found
   only ElladicCohomology comments. Local rg in both Lean roots and the upstream
   checkout found no scalar composition theorem. Read
   ExtExactFunctorCompositionComparison, MayerVietorisExtFunctorSquare and
   EtaleCohomologyPullbackFunctorial: these do not supply the needed normalized
   coefficient/unit and resolution comparisons. This hole cannot be closed by
   a short specialization of them.
4. The target is reduced from the top to two applications of the one-path law,
   equality elimination and coefficient functoriality. No unnecessary import
   remains: the original public import supplies the signature, and the new plain
   import supplies only the proof. The new module's public import supplies its
   signature. The old direct proof dependency
   lem-pc-module-pullback-identity-composition is fully accounted for under
   No longer needed and remains on the composition node. No module is globally
   pruned. Read dag/units/sk-prop-av-cube.json; its realized fields are unchanged
   (statement [] and steps [[]]); this reduction changes no unit route.
5. Compared both node records with the Lean. The square's proof and proof_deps
   describe exactly the two applications and algebra helpers. The composition
   node matches the new signature verbatim, contains its source, proof in words,
   search records, provenance and chapter/unit. Existing node changes are only
   in proof, proof_deps and proof_origin. The new obligation is counted openly:
   one upper hole closed, one lower hole added, net zero.

Second reading changed: restored the existing signature's exact whitespace and
corrected the new module's source attribution and both proof_origin records to
Tag 01F7 for the resolution-defined cohomology map. Tag 01FD was read and concerns
Cech-to-derived compatibility; it is not the direct source for that construction.
No proof term, statement meaning, definition or import was changed.
