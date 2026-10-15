## What changed

Replaced the sole hole in AlgebraicGeometry.tensorResolutionCoordinateSections_naturality
by composing the affine tensor-homology square, the common K-flat comparison square,
and the proved tensorResolutionSection_naturality. The complete original signature,
including the conclusion after the pipeline operator, is byte-for-byte unchanged.

Added QCohTensorResolutionChartHomologyNaturality and
QCohTensorResolutionChartComparisonNaturality, each with one strictly smaller obligation.
Added the proved defining formula AlgebraicGeometry.tensorResolutionCoordinateSheafIso_factors
in its own new module QCohTensorResolutionCoordinateFactorization, imported only for the proof.
The first worker had added this formula to QCohTensorResolutionCoordinateSections; the second
reading moved it into the new module. The existing coordinate definition and its module are
unchanged. The helpers import the modules their signatures actually use, with named local
instances to avoid collisions with the existing coordinate module.

Repair of reviewer X-c7ef6, C5: removed the duplicate proposed coordinate-sections
node and updated the existing node
new-g2-existing-qcoh-tensor-resolution-coordinate-naturality instead. Only its proof,
proof_deps and proof_origin fields were replaced with the delivered proof fields;
all other fields, including the complete lean.statement, are preserved. The theorem
docstring now references that existing node. No proof or signature changed in this repair.

## Proved and sorry left

Closed: AlgebraicGeometry.tensorResolutionCoordinateSections_naturality (1 of 1 original holes).
Also proved: AlgebraicGeometry.tensorResolutionCoordinateSheafIso_factors, by reflexivity.
This is a decomposition: one original hole closed and two new holes added, a net increase of
one hole in this delivery, not a net proof gain or an axiom-free proof of the original theorem.

Added holes:
- AlgebraicGeometry.tensorResolutionChartHomologyIso_naturality,
  node new-t3-qcoh-tensor-resolution-chart-homology-naturality. This is the affine
  tensor-homology square using hb and hk, independent of augmentation and K-flat comparison.
- AlgebraicGeometry.tensorResolutionChartComparisonIso_naturality,
  node new-t3-qcoh-tensor-resolution-chart-comparison-naturality. This is the four-leg
  K-flat comparison square using ha, independent of b, k and the presentations NA and sN.

Each hole is exactly a public theorem with proof `by sorry`, source, complete proof in words,
and matching node. Neither is a restatement of the original section equation.
No definition or arbitrary witness chosen from an unproved existence theorem was added.

## No longer needed

Removed direct imports from the original item:
- Sheaf.AlgebraicGeometry.AffineChartTotalTensor;
- Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison;
- Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison;
- Sheaf.AlgebraicGeometry.QCohTensorResolutionCanonicalComparison (originally public).

The first three were unused proof-plan imports. The last supplies existence of comparison
maps, whereas this theorem takes a, b and k as arguments. Its declarations occur neither in
the signature nor the proof. The direct importer QCohOrdinaryTensorResolutionCoordinates
uses only the naturality theorem from this module. The new proof imports are plain imports.
The remaining public import QCohTensorResolutionCoordinateSections supplies the coordinates
in the statement.

No module is claimed pruned from the targets' closure. The existing attachment
new-g2-existing-qcoh-tensor-resolution-coordinate-naturality now lists exactly the two
square nodes, the defining formula, and the affine sections interfaces used in the proof.
Its proof_deps no longer includes lem-pc-affine-chart-total-tensor,
new-affine-derived-tilde-homology-comparison, or
lem-pc-open-kflat-tensor-homology-comparison.
The new square plans do not use lem-pc-affine-chart-total-tensor,
new-affine-derived-tilde-homology-comparison, or
lem-pc-open-kflat-tensor-homology-comparison as substitutes for naturality of specified maps:
those nodes provide isomorphisms without the required identifications.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery incorrectly claimed that the assigned module had no attached DAG node.
G2 had already attached new-g2-existing-qcoh-tensor-resolution-coordinate-naturality.
The duplicate proposed node was removed from the sandbox, and the existing node now records
the two-square reduction while preserving its full statement and attachment metadata.
The original docstring referred to
nonexistent tensorResolutionChartTensorIso_naturality and
tensorResolutionCoordinateSheafIso_naturality_of_squares. The new interfaces state their
separate mathematical content precisely.

The first worker's report omitted the three removed proof imports and put a new statement
in an existing module. The second reading corrected both, removed the unused public canonical
comparison import, and replaced plan citations to existential comparison theorems with the
canonical pure-tensor and four-leg zigzag arguments. Blueprint provenance now reaches the
original lem-sc-finite-duality ancestor through the coordinate-witness chain.

The earlier duplicate attachment used a parsed signature prefix after the signature parser
stopped at the original `|>` operator in `let e`. That duplicate attachment is removed.
The existing G2 node retains its complete lean.statement, including the section equation;
none of its lean fields were changed. The full original Lean signature remains unchanged.

## New nodes

new-t3-qcoh-tensor-resolution-chart-homology-naturality is the affine tensor-homology square,
without M, q, K, F, s or an augmentation hypothesis. Its plan uses the canonical tilde tensor
formula, section adjunction and naturality of the chosen homology comparisons.

new-t3-qcoh-tensor-resolution-chart-comparison-naturality is the augmented K-flat comparison
square, without NA, sN, b or k. Its plan uses the supplied common resolution, four chain
squares, invertibility from K-flatness, and normalized restriction homology naturality.

new-t3-qcoh-tensor-resolution-coordinate-factorization records the reflexive defining formula
in the new module QCohTensorResolutionCoordinateFactorization.

Change record: coord/changes/t3-qcoh-coordinate-factorization-api.md.

## Earlier second reading (a previous round; superseded)

1. Compared the item with the repository version by diff and independently compared the entire
   theorem signature as literal bytes through the final section equation. Verdict: unchanged.
   The coordinate definition is untouched. No other existing declaration is changed. The
   factorization statement now has its own module rather than extending an unclaimed module.
2. Read the actual proof: hf and hg compose by functoriality and associativity, edA and edB
   identify their composite with the specified coordinates, and the final application is the
   proved affine sections naturality theorem. Only the two listed public theorems contain
   sorry. No forbidden declarations or hollow definitions occur. Local compilation and axiom
   checks cover all four delivered modules; sorryAx remains allowed for the two open squares
   and the original theorem. The factorization theorem has only propext, Classical.choice
   and Quot.sound; the other three print exactly those axioms plus sorryAx. The unchanged
   direct caller QCohOrdinaryTensorResolutionCoordinates also compiles against the revised set.
   No axiom-free completion of the original theorem is claimed.
3. Read each split signature against the defining chart isomorphisms and the stated proof.
   Verdict: the squares have the correct orientations and are strictly separate parts of the
   argument. In degree zero, ha is precisely the augmentation square, and hb and hk give the
   coefficient tensor square. Positive degrees of the extended chain complex vanish. Empty
   affine charts/zero rings and zero coefficient modules give zero tensor homology. Unbounded
   K and F cause no problem: the four comparison legs use K-flatness, without truncation or
   quasi-coherence of N in the comparison square. Restriction of scalars is exact for every
   ring map; no extra flatness assumption is needed there. Fresh LeanFinder, Loogle and grep
   searches (recorded in searches.jsonl) found generic ShortComplex.mapHomologyIso naturality,
   not either complete chart square. Also searched the project and upstream Lean declarations.
   The existing generic homology API is already used in the plans; neither remaining square
   closes by a short application of a matching theorem.
4. Checked the route from the top: the item has a real composition proof, followed by the
   already proved sections theorem, rather than an application of a renamed copy of itself.
   The factorization is reflexive. Imports now distinguish statement and proof use, and the
   removed imports are fully listed above. Read dag/units/sk-thm-picard-duality.json: its
   realized statement and step arrays are empty, and no realized unit node is bypassed or
   changed. The affine coordinate-witness route and chapter remain intact.
5. Read all four nodes and their source places. The main proof_deps is the union of the
   statements its steps use. The factorization plan is reflexivity. Corrected the square
   plans so that existential isomorphism statements are not treated as identifying the
   canonical maps, and retained complete natural-language arguments with their actual API
   names. Checked the cited Stacks pages: [08DX(2)](https://stacks.math.columbia.edu/tag/08DX)
   for the affine derived tensor calculation, [08DV](https://stacks.math.columbia.edu/tag/08DV)
   for sheafified K-flatness, [06YT](https://stacks.math.columbia.edu/tag/06YT) for tensor
   invariance, and [01I9](https://stacks.math.columbia.edu/tag/01I9) for functorial affine
   pullback/restriction of scalars. The displayed naturality formulas are consequences of
   these constructions, not quotations of a source asserting exactly the Lean signatures.

Second-reading changes: relocated factorization to its own module; narrowed the new public
imports to signature dependencies; removed the unused public canonical-comparison import;
restored the original signature's exact whitespace; gave the new local instances unique names;
corrected node proof plans and blueprint provenance; completed the pruning and decomposition
accounting and this independent review. The substantive composition proof was retained.

## Second reading by T3

Independent reading of the repaired delivery, including return X-c7ef6/C5:

1. Compared the delivered item with the repository by diff and compared the complete
   theorem signature as literal bytes, through the section equation after `|>`.
   Verdict: identical. The other three modules are new; no existing definition or
   additional existing module is changed. All new public imports supply names used
   in signatures; the item's new proof imports are plain imports.
2. Read the composition proof and the defining coordinate composite. The `hf` and
   `hg` squares compose by associativity, the factorization is reflexive, and the
   final sections theorem has exactly the needed square. All four delivered files
   compile locally without warnings. Only the two reported public theorems contain
   `sorry`; no forbidden declaration, hollow definition, or arbitrary witness
   construction occurs. The unchanged direct caller
   QCohOrdinaryTensorResolutionCoordinates compiles against the delivered overlay.
   Explicit `#print axioms` in a scratch copy reports only propext,
   Classical.choice and Quot.sound for the factorization; the original theorem
   and the two open square theorems additionally report sorryAx, as expected.
3. Checked the split statements against ChartModel, ChartComparisonIso and
   HomologyCoherence. Verdict: true, correctly oriented and strictly smaller than
   the item. At n = 0 the augmentation square is exactly `ha`; the coefficient
   square is `hb`, and `hk` determines the tensor map on generators. The total
   tensor with the coefficient in degree zero introduces no extra sign. Positive
   degrees of the extended first complex vanish. Zero coefficients, empty charts,
   identity inclusions and unbounded K introduce no extra hypothesis. Exact
   restriction of scalars requires no flatness hypothesis. Fresh Loogle,
   LeanFinder and grep searches, with different queries recorded in searches.jsonl,
   found generic exact-functor and extension homology naturality, not a complete
   chart square. Local searches also checked the tensor zigzag and coordinate
   square interfaces. Neither remaining obligation is a short application of one
   of these results: the chain squares and canonical-map identifications remain.
4. Checked the reduction from the original hole downward. It uses two separate
   mathematical squares and a proved sections result, rather than a renamed copy
   of the original assertion. All four removed imports and all three removed old
   proof dependencies are listed under No longer needed. No module is claimed
   pruned from the target closure. The unit sk-thm-picard-duality has no populated
   realized statement or step nodes; its route and provenance are retained.
5. Compared every node's verbatim Lean statement with the delivered source and
   checked that proof_deps is the union of its proof steps' uses. Verdict: match.
   The duplicate attachment is absent. The existing G2 node differs from the
   repository only in proof, proof_deps and proof_origin: its full lean record,
   statement, creation and review metadata are preserved. The three new nodes
   have their required source, proof, searches, creation and blueprint records.
   Rechecked the cited Stacks constructions, which justify the reduction rather
   than asserting these exact Lean formulas: [08DX(2)](https://stacks.math.columbia.edu/tag/08DX),
   [08DV](https://stacks.math.columbia.edu/tag/08DV),
   [06YT](https://stacks.math.columbia.edu/tag/06YT), and
   [01I9](https://stacks.math.columbia.edu/tag/01I9).

Changes in this reading: added this independent review and fresh search records.
The repaired Lean proof and DAG were retained. This remains a decomposition:
one original hole closed, two holes added; net minus one hole closed.
