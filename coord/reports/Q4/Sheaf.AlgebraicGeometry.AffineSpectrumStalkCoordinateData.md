## What changed

Proved `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_stalk_coordinate_data`
in `Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData`, with its original signature
byte-for-byte unchanged. All helpers are private and fully proved. The four ring equivalences
are actual inverse-isoSpec stalk maps composed with point equality isomorphisms. Both base
algebra equations include the actual point congruences from the two cartesian squares.
The pure-tensor equation follows from the two restrictions of `tensorMap` and multiplication.

For the complex isomorphism, use the existing `exists_tensorPullback_stalk_iso`, followed by
restriction of scalars and the invertible extension/restriction adjunction unit. This constructs
a natural linear comparison before mapping to complexes; no new semilinearity theorem is
needed. The only choice in this proof selects the already specified natural stalk isomorphism
from its germ-compatible universal description; no definition chooses arbitrary data from
an unproved existence theorem. The resulting complex witness is unpacked only in a theorem.

Replaced the public import of `IsoPullbackStalkCohomology` by the lower statement dependency
`SingleComplexBaseChangeStalkCondition`. Added proof-only imports of
`StalkComparisonSourceTransport` (its existing stalk-additivity instance) and Mathlib's
`CategoryTheory.Adjunction.FullyFaithful`. No public declaration was added or changed.
The only direct importer, `AffineSpectrumTensorCoordinateData`, already explicitly publicly
imports `IsoPullbackStalkCohomology`; no forced adaptation is required.
Updated the existing node's proof, proof dependencies and proof origin to this route.
Change record: `coord/changes/affine-spectrum-stalk-coordinate-import-pruning.md` records
the removed public import and local commands, with all downstream modules and their
unchanged interfaces. No forced adaptation was made.
A declaration-local unused-variable linter option preserves the original existential binder
`q`, which is necessarily absent from the ring-only compatibility clauses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_stalk_coordinate_data`
(node `lem-pc-affine-spectrum-stalk-coordinate-data`).
No `sorry` remains in the item; no hole or module was added. This is a proof from existing
library declarations, not a decomposition. Imported declarations may retain transitive holes;
this delivery does not claim the whole targets' closure is axiom-free.
The zero complex requires no exception, and an empty spectrum supplies no point `z0`.
No flatness, boundedness, nonzero-ring, or additional affine hypothesis was introduced.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology`.
Removed proof dependency: `lem-pc-iso-pullback-stalk-cohomology`.
Neither the additive stalk-cohomology comparison nor `tensorPullbackRestrictIso` nor
`restrictStalkNatIso` is needed by this proof. The source-transport module remains needed
only for its existing `comparisonStalkAdditive` instance. The tensor-pullback-stalk module
is already a public dependency of the stalk-condition module, so no extra import is needed.
No claim is made that the removed module disappears from every target's import closure:
the direct caller independently imports it. No other imports, nodes or modules are pruned.
The unit `sk-thm-picard-semicon` has empty realized statement and proof-step arrays;
this change bypasses no realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned module-germ semilinearity argument is unnecessary:
the existing tensor-pullback-stalk natural isomorphism is already linear, and the unit of
the extension/restriction adjunction is invertible because the stalk ring map is invertible.
The node and declaration docstring now record this shorter route. The original statement's
unused existential name `q` produces a linter warning once a complete proof is supplied;
a scoped linter option preserves the fixed signature without that warning.

Searches: launcher LeanFinder for stalk ring isomorphisms and pullback module stalks,
Loogle for `"stalkMap"`, launcher grep for `isoSpec_inv_naturality|restrictStalkNatIso`,
and direct `rg` of both library roots and Mathlib found the existing tensor-stalk theorem
and the adjunction equivalence API used here. No new nodes were necessary.

## Second reading by Q4

1. Interface: PASS. Compared the delivered module against the repository with `diff` and
   independently compared the complete existing theorem signature: byte-for-byte identical.
   All added declarations are private. No existing definition, visibility, hypothesis or
   conclusion changes. The public import replacement has its change record; the sole direct
   caller independently publicly imports the removed module.
2. Proof: PASS. The delivered file compiled without errors or warnings using `lcompile.py`.
   A scratch copy with `#print axioms` for
   `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_stalk_coordinate_data`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There is no `sorry`, forbidden declaration, or hollow definition in the delivery.
   `spectrumStalkEquiv` explicitly composes equality and inverse-isoSpec stalk isomorphisms.
   The tensor-map choice is fixed by its two restrictions; the stalk natural isomorphism is
   fixed on generating germs, and is used locally within a theorem, not as arbitrary data
   in a new definition. The unchanged direct caller `AffineSpectrumTensorCoordinateData`
   compiled against the delivered module in a scratch sandbox overlay.
3. Split statements: PASS; none added. Reviewed all private helpers: ring transport by
   equality induction, inverse-isoSpec naturality, the extension/restriction unit, and the
   two tensor-map restriction equations give exactly the claimed conclusions. Zero modules
   and zero complexes obey the same maps; empty spectra offer no point; the hypotheses
   require no extra flatness or nontriviality. No restatement of the item was split off.
4. Route and pruning: PASS. Read the existing tensor-pullback stalk theorem, stalk-condition
   declarations, and source-transport additivity instance; searched the library and Mathlib
   for stalk isomorphisms, scalar restriction, and complex-composition comparisons. The
   existing linear stalk isomorphism and scalar adjunction provide the direct route.
   `No longer needed` lists the only removed old proof dependency and import. The unit's
   realized statement and step arrays are empty, so no realized route is bypassed.
   Tested removing the source-transport import and stalk-additivity witnesses in scratch:
   `mapHomologicalComplexCompIso` requires additivity, so that proof import is necessary.
5. Nodes: PASS. Only `proof`, `proof_deps`, and `proof_origin` differ in the existing node.
   The dependencies equal the union of step uses and record the actual tensor-stalk,
   stalk-additivity, and ring-coordinate route. No new nodes or holes need registration.

Changes by the second reader: added this review record only. No Lean, node, or change-record
repair was needed. One original hole closed, zero holes added; this is a proof, not a
one-for-one decomposition.
