## What changed

`AlgebraicGeometry.supported_perfect_detector_affine` keeps its original signature and now
has a complete Lean proof from the affine Koszul construction/open-unit comparison.
The proof establishes `IsAffine X` directly from the cardinality and cover hypotheses,
including the empty-cover case. It then takes the complement open, uses the comparison
unit, proves its target zero through the adjunction Hom equivalence, and transports zero
across that invertible unit.

Added two separate modules: `SupportedPerfectDetectorAffineConstruction` states the
remaining construction/comparison argument; `SupportedDerivedRestrictionZero` proves
vanishing of exact derived restriction away from cohomological support directly from
Mathlib. The latter does not require affineness, quasi-coherence, closedness of the
support, compactness, or quasi-separatedness. Its private underived helper is also proved.

Updated the original DAG node's proof route and added a node for each new public theorem.
No existing definition or statement changed. No data definition, choice construction, or
axiom was added.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.supported_perfect_detector_affine`
(`lem-pc-supported-perfect-detector-affine`). It is a decomposition, not a proof free of
all remaining holes: its new construction lemma remains unproved.

Proved `AlgebraicGeometry.supported_derived_restriction_zero`
(`lem-pc-supported-derived-restriction-zero`) and its private helper `module_restriction_zero`.
`#print axioms AlgebraicGeometry.supported_derived_restriction_zero` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The only added and remaining hole is
`AlgebraicGeometry.supported_perfect_detector_affine_construction`
(`lem-pc-supported-perfect-detector-affine-construction`). It supplies a perfect supported
Koszul object and invertibility of the open-restriction unit for arbitrary quasi-coherent
objects orthogonal to its shifts. It does not assume support on those objects and does not
conclude that they are zero. The cover reduction, supported restriction vanishing, and
right-adjoint preservation of zero are independently proved in this delivery.

One original hole closed and one new hole added: net hole change zero. All three modules
compile in import order without warnings. Edge cases checked: empty X and empty cover,
zero ring, singleton cover, T empty, T equal to X, empty open, and unbounded complexes.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality` from the
item; it is retained in the construction module, together with the existing derived
adjunction input. Its node `lem-pc-perfect-generation-koszul-orthogonal` remains needed
below the construction node. No node or module is claimed globally pruned.

The target node's original direct proof dependency on that Koszul comparison is replaced
by the construction node and the proved restriction-vanishing node. The unit route stays
unchanged; `dag/units/sk-thm-picard-duality.json` has no realized binding for this node.

## Where the brief, the DAG or earlier work was wrong

The existing Koszul comparison is formulated on `Spec A` with an explicit sheafified
Koszul complex and a specified derived adjunction. Applying it on an arbitrary affine
scheme still requires construction of the finite tuple and perfect object, existence of
the right adjoint, and transport along the affine presentation. That remaining argument
is now isolated explicitly, rather than treating it as a one-line application.

The local mirror lacks `literature/stacks-project/perfect.tex`; the source paragraphs were
read directly at [Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A) and
[Tag 09IR](https://stacks.math.columbia.edu/tag/09IR). The source's route is preserved.
LeanSearch returned Internal Server Error. LeanFinder and Loogle were tried, and Mathlib,
both library roots, and the DAG were searched with `rg`. No exact statement was found;
Mathlib's section-germ extensionality and exact homology comparison close the restriction
argument. The new construction is sourced to the existing affine paragraph and Koszul
comparison, not to an unsupported alternate route.

## New nodes

`lem-pc-supported-perfect-detector-affine-construction` is in
`lean/Sheaf/AlgebraicGeometry/SupportedPerfectDetectorAffineConstruction.lean`. It is the
remaining named hole: construction of the finite supported perfect object on an affine
scheme and its open-unit comparison. The natural-language proof specifies the actual
Koszul construction and its edge cases.

`lem-pc-supported-derived-restriction-zero` is in
`lean/Sheaf/AlgebraicGeometry/SupportedDerivedRestrictionZero.lean` and is proved.
It uses stalkwise zero sections, a complex representative, exact restriction's homology
comparison, and the derived homology criterion for invertibility. It adds no hole.

## Second reading by V1

1. Compared every delivered module with the repository version. The existing target
   declaration has the same signature byte for byte; the two additional modules and the
   two new DAG nodes are explicitly recorded above. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`; there are no errors or warnings.
   The only remaining `sorry` is the named construction theorem, and no definition,
   axiom, unsafe declaration, or forbidden kernel escape was added. Verdict: pass.
3. Checked the split statements against the source route and searched Mathlib and the
   library for existing equivalents. The restriction-vanishing statement is strictly
   below the target, and the construction statement isolates the genuinely missing
   affine Koszul argument. Both are true and exactly as strong as used. Verdict: pass.
4. The target proof uses the affine construction and restriction-vanishing nodes, while
   the construction retains the Koszul orthogonality and derived-adjunction inputs.
   The direct target import of KoszulOpenOrthogonality was removed and is reported under
   `## No longer needed`; no further unused imports or proof dependencies remain.
   Verdict: pass.
5. Checked the DAG `proof`, `proof_deps`, `proof_origin`, Lean records, and unit field
   against the proofs and declarations. The unit remains `sk-thm-picard-duality`; its
   route is preserved. Verdict: pass.

Changed only the target proof and its proof route, added the two documented split-node
   modules, and recorded the corresponding DAG nodes. No existing statement or
   definition was changed.
