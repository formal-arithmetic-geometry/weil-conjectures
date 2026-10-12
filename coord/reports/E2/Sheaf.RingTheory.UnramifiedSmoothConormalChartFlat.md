## What changed

Replaced the whole-chart smoothness sorry with a real differential argument in `Sheaf.RingTheory.UnramifiedSmoothConormalChartFlat`. The existing declaration `Algebra.flat_of_unramified_smooth_conormal_chart` keeps its signature byte for byte. Added `Sheaf.RingTheory.SmoothConormalChartDifferentialBasis`, whose theorem constructs the rank-n differential basis by splitting the conormal sequence, adjoining c variables, and localizing. This theorem is proved too, from Mathlib and the already proved `KaehlerDifferential.exists_polynomial_extension_equiv`.

The target uses unramifiedness to make the differential map surjective, equal finite bases to make it injective, and the two proved Mathlib Jacobi-Zariski exactness lemmas to kill relative H1. Finite presentation then gives smoothness, and `Algebra.Smooth.flat` gives flatness. Added proof imports are plain imports. Removed the proposed public RingHom.Etale import, which was only for a proof. Updated the target node's proof route, dependencies and origin. The redundant public PDeriv import is removed with an import change record; its public transitive path remains intact.

## Proved and sorry left

Holes closed: `Algebra.flat_of_unramified_smooth_conormal_chart` (node `lem-weil-pbc-unramified-smooth-conormal-chart-flat`), one of the one original holes.

Holes added: none. Holes left in delivered modules: none. Removed the first worker's unproved `Algebra.smooth_of_unramified_smooth_conormal_chart` and its proposed node, rather than moving the original problem under another name.

The new intermediate `KaehlerDifferential.nonempty_basis_smooth_conormal_chart` (node `lem-weil-pbc-smooth-conormal-chart-differential-basis`) is fully proved. This is a proof, not a decomposition: net one original hole closed, zero added. The `#print axioms` scratch checks for both public declarations show only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, including through the imported polynomial-extension theorem.

## No longer needed

Removed direct imports relative to the current repository snapshot:

- `Mathlib.Algebra.MvPolynomial.PDeriv`
- `Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`
- `Sheaf.RingTheory.ClosedPointDimensionLocalRing`
- `Sheaf.RingTheory.FlatOfFlatClosedFiber`
- `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`
- `Sheaf.RingTheory.MiracleFlatness`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension`
- `Sheaf.RingTheory.SmoothFibreRegularLocal`

`Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension` is still needed by the new basis module; its node is retained there. The public PDeriv declarations remain available through Smooth.Basic -> Smooth.Kaehler -> Extension.Cotangent.Basic -> Kaehler.Polynomial. The first worker's extra RingHom.Etale import is also removed. No claim is made that any removed module becomes globally unreachable: other target routes may still use it.

Every old target proof dependency not used by either the target proof or the proved basis calculation is:

- `lem-weil-pbc-closed-point-dimension-local-ring`
- `lem-weil-pbc-criterion-flatness-fibre`
- `lem-weil-pbc-fibre-ring-localization-quotient`
- `lem-weil-pbc-flat-local-ring-maps`
- `lem-weil-pbc-flat-map-local-criterion`
- `lem-weil-pbc-flat-over-localization`
- `lem-weil-pbc-flat-ring-map-comp`
- `lem-weil-pbc-kahler-differentials-base-change`
- `lem-weil-pbc-localization-flat`
- `lem-weil-pbc-miracle-flatness`
- `lem-weil-pbc-polynomial-scalar-extension`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `lem-weil-pbc-smooth-fibre-regular-local`
- `lem-weil-pbc-smooth-over-field-dimension-differentials`
- `lem-weil-pbc-unramified-algebra-over-field-product`
- `lem-weil-pbc-zariski-lemma`

The old split-conormal, polynomial-basis, polynomial-extension, differential-localization, smooth-composition, smooth-principal-localization, and smooth-flatness ingredients remain used. The unit `dag/units/sk-thm-p1.json` and its `realized` route are unchanged; this is a shortening below the unit level.

## Where the brief, the DAG or earlier work was wrong

The first worker's smoothness intermediate had exactly the same chart inputs and still carried the whole flatness argument; its docstring proved flatness rather than its stronger smoothness conclusion. Its node had no search records, a non-self-contained statement, an ellipsis in `lean.statement`, and no substantive proof dependencies. That proposed delivery was not an acceptable reduction. It was removed entirely.

The old fibrewise plan is valid but unnecessary for this node. The conormal splitting yields an actual free differential module after stabilization, so a surjective endomorphism and the Jacobi-Zariski sequence suffice. Mathlib's full smooth-to-flat theorem is shorter than the first worker's conversion through a RingHom étale criterion. The source statement is unchanged. Sources checked: Stacks [07CH](https://stacks.math.columbia.edu/tag/07CH), [00S2](https://stacks.math.columbia.edu/tag/00S2), and [031J](https://stacks.math.columbia.edu/tag/031J).

## New nodes

`lem-weil-pbc-smooth-conormal-chart-differential-basis`: a proved, strictly smaller calculation of Omega(D_g/R), independent of theta and unramifiedness. Its Lean statement is recorded verbatim, with source, complete natural-language proof, three kinds of searches, and proof dependencies matching the constructed splitting, scalar extension and localization. LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, and repository/Mathlib text searches found ingredients but no duplicate statement.

Change record: `coord/changes/UnramifiedSmoothConormalChartFlatImports.md`. This records only redundant-public-import removal, all 206 downstream users and their unchanged public dependency closure. No existing statement or definition is changed; no forced adaptation is needed.

## Second reading by E2

1. Compared each delivered module with the repository version using diff, and separately compared the existing theorem signature bytes. Verdict: the only existing declaration's signature is identical; no definition or hypothesis changed. The new basis module is genuinely new. The public import removal is declared in its change record and has an unchanged public transitive path.
2. Compiled both modules in import order through lcompile.py. Verdict: no errors or warnings, no local sorry, and no forbidden axiom/unsafe/opaque/implemented_by/extern declaration. Scratch copies with #print axioms for both declarations show exactly the three permitted axioms. No data definition or arbitrary unproved witness is introduced.
3. Checked the new calculation at n=0, c=0, g=0, and zero coefficient rings: all tensor, basis, and split exactness arguments still apply; localization at zero simply yields the zero module. Verdict: true and exactly sufficient. It is proved, not a split-off hole. Searched using stabilization, polynomial differential bases, submersive presentations, and conormal freeness; the existing polynomial-extension theorem is used rather than duplicated.
4. Read the proof from the target downward. Verdict: a shorter route from Mathlib and one proved chart calculation closes everything; all imported Sheaf declarations used are proved. Unused direct geometric proof imports and all obsolete old proof-dependency nodes are listed above. Checked sk-thm-p1: its unit-level route is unchanged.
5. Read both delivered node records against the Lean. Verdict: the target's proof, proof_deps and proof_origin describe the actual differential argument, and the new node has the required provenance, searches and verbatim Lean signature. Dependencies account for the existing polynomial-extension declaration and the Mathlib fragments used; the stronger Sheaf Jacobi-Zariski module need not be imported for fragments already proved by Mathlib.

Changes by the second reader: removed the whole-problem smoothness sorry and deficient node; proved the differential-basis intermediate and target; repaired proof-only import visibility, pruned unused imports/dependencies, synchronized the DAG and natural-language proof, and replaced the misleading original progress report with the actual one-hole net closure.
