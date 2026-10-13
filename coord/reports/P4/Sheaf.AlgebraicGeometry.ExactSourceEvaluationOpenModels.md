## What changed

Completed the earlier attempt's reduction of
`AlgebraicGeometry.exists_exactSource_evaluation_open_models`, without changing its
signature or any existing definition. The item constructs the fixed K-injective
resolution of F and the actual evaluation chain map for that resolution. A proved
private mapping-cone argument shows that tensoring the resolution map with the
K-flat dual is a quasi-isomorphism. Hom exactness gives the other quasi-isomorphism.
The K-injective comparison and the ordinary naturality square then descend
to F by a proved categorical cancellation argument.

Added `Sheaf.AlgebraicGeometry.OrdinaryEvaluationPostcomposition`, with its theorem
stated from the recorded Hom projections, ordinary component factorization, and
tensor-Hom naturality. Added
`Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels`, which isolates
the ordinary-to-derived representative calculation for K-injective coefficients.
Its proof dependencies remain imported there. The chosen resolution is the actual
fixed library functor; no arbitrary existence witness supplies definition data.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_exactSource_evaluation_open_models`
(`lem-pc-exact-source-evaluation-open-models`). This is a decomposition, rather
than a complete proof independent of new obligations: one original hole closed,
two lower holes added, net minus one closed-minus-added declaration holes.

The underived theorem `AlgebraicGeometry.ordinaryEvaluation_postcomposition`
(`lem-pc-ordinary-evaluation-postcomposition`) remains a named obligation. Its
complete proof in words uses component naturality and product/coproduct detection.

The two sorries in the delivered files are
`AlgebraicGeometry.ordinaryEvaluation_postcomposition` and
`AlgebraicGeometry.exists_exactSource_kInjective_evaluation_open_models`
(`lem-pc-exact-source-kinjective-evaluation-open-models`). This strictly restricts
the coefficient to a K-injective complex. The proof extending it to arbitrary
coefficients is implemented, including both quasi-isomorphism proofs and the
cancellation square. Existing imported obligations, including the ordinary
matrix differential identity and Hom-complex projection theorem, are used as
stated; their proofs are not part of this item.

The new statements were checked mathematically on zero complexes, empty opens,
identity coefficient maps, and zero coefficient maps. Compatibility is existential
in the K-injective case, rather than required for arbitrary comparison isomorphisms.
The proposed component argument handles both the zero and nonzero degree branches.

## No longer needed

Removed these direct imports from the item:

- `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`;
- `Sheaf.AlgebraicGeometry.DerivedTensorSymmetry`;
- `Sheaf.Algebra.Homology.KFlatResolution`;
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`;
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

The first four remain imported by the K-injective representative module. Their
nodes `lem-pc-kflat-derived-tensor-comparison`,
`lem-sc-scheme-derived-tensor-symmetry`, `lem-pc-kflat-resolution`, and
`prop-pur-kinjective-resolutions-exist` therefore remain needed. The ExactFunctor
interface is publicly imported by the new K-injective module. No entire module
or node is claimed removed from the targets' closure. The unit route is preserved.
The new ordinary naturality node has only its actual statement dependencies;
it does not depend on a derived-category or perfectness statement.

## Where the brief, the DAG or earlier work was wrong

The earlier report described a finished reduction although its main file did not
compile. The repaired main reduction compiles: the localization instance for the local
category alias is explicit, the tensor argument is stated generically with an
explicit ring sheaf, localized naturality uses functor map-composition equations,
and the final cancellation is proved in an arbitrary category. An attempted ordinary naturality proof compiled its generic categorical helpers,
but the complete degreewise proof exceeded the single-file compile limit. It is
therefore delivered as the named obligation, with the attempted proof retained
only in the scratchpad. The existing
`OrdinaryEvaluationComponentFactorization` interface avoids unfolding its full
sheaf evaluation formula repeatedly. No mathematical statement was changed.

The original plan did not expose coefficient naturality as a usable interface.
That interface is now a named underived obligation. The K-injective representative case remains a
separate item with a source and a complete proof in words. Stacks Tags 08DJ,
08DM, and 08DQ were read online because the local literature payload is absent.
The blueprint search found no duplicate evaluation/K-injective node. Sources:
[08DJ](https://stacks.math.columbia.edu/tag/08DJ),
[08DM](https://stacks.math.columbia.edu/tag/08DM), and
[08DQ](https://stacks.math.columbia.edu/tag/08DQ).

## New nodes

`lem-pc-exact-source-kinjective-evaluation-open-models`: the representative
calculation for K-injective coefficients. Its node retains the original transport,
K-flat tensor comparison, and canonical uncurrying route. Only the unit needs a
new K-injective resolution; the coefficient is already K-injective.

`lem-pc-ordinary-evaluation-postcomposition`: the underived coefficient naturality
square. Its statement needs no exactness, flatness, boundedness, or
perfectness assumptions. Its proof follows tensor-Hom naturality and the existing
Hom projection specification. No forced adaptations are needed.

Change record: `coord/changes/exact-source-evaluation-proof-options.md` documents
local proof elaboration attributes and options flagged by the static checker.
No declaration signature or mathematical interface changes.

## Second reading by P4

1. **Statements unchanged.** I compared the delivered item module with the repository version. The existing theorem signature is byte-for-byte unchanged; the two added theorem signatures match their DAG nodes.
2. **Proof and axioms.** All three delivered Lean files compile with `lcompile.py`. The item theorem has a completed proof. The only remaining `sorry`s are the two named split-off obligations, each with a public declaration, source docstring, and DAG node; no definitions contain `sorry`, and no forbidden declarations occur.
3. **New statements.** The K-injective representative theorem and ordinary coefficient-naturality theorem are true, strictly smaller than the item, and needed by the reduction. I checked zero complexes, empty opens, identity maps, and zero maps. Searches found no existing duplicate declaration.
4. **Pruning and route.** The item removes only proof-only imports that are no longer used directly. The retained K-flat, symmetry, resolution, and K-injective dependencies are used by the K-injective reduction. The unit route is preserved; no target statement or definition changed.
5. **DAG agreement.** The item and both split-off nodes record the declarations, proof dependencies, sources, and proof origins used by the delivered files. The change record documents the local elaboration options without changing interfaces.

I changed only this report section during second reading. No Lean proof or statement required repair.
