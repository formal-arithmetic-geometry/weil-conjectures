## What changed

Proved `AlgebraicGeometry.ProEtale.sp_tower_injective_components`, the remaining hole in
`Sheaf.Paper.SmoothPurityTowerInjectiveComponents`. Existing signatures, definition bodies,
visibility, docstrings and public imports are unchanged. The other eight original holes were
already closed by X8; those arguments are retained.

Split the embedding supplied by `sp_tower_evaluation_adjoint`. System evaluation preserves
products because `systemLevelLeftExtensionTheory` supplies its ordinary left adjoint.
The equivalence counit and finite-support product isomorphism then give the stated retract of
a finite product of scalar-restricted injectives, including the one-factor case at index zero.

For section acyclicity, transport module sheaves to the common-universe AsSmall site. Apply
injective-module abelian acyclicity and the object-cohomology/derived-section comparison there.
Scalar restriction preserves the underlying abelian sheaf. Exact-composition comparisons and
faithful forgetful functors transfer the vanishing to module sections and back to the original
site. Finite products and retracts preserve this vanishing. The existing dimension-shifting
criterion proves direct-image acyclicity using sectionwise surjectivity.

Fully proved private generic naturality, limit-preservation and isomorphism-uniqueness helpers,
explicit universes and separately elaborated evaluation components avoid expensive unfolding
of the concrete coefficient construction. The duplicate injective-section transport was
replaced by the existing generic acyclicity of injectives. The small-site and level-pushforward additive
helpers have local instance attributes. The elaborator options are local to the module.
The evaluated-product argument is also factored through a proved generic helper, and the
concrete level-pushforward additive instance is cached locally. The whole module compiled
cleanly in 21.2 seconds under the unchanged limit
(`scratchpad/CompactRetract.log`); no temporary profiling or heartbeat options remain.

Updated the existing node's proof and dependencies. Added proof imports for object cohomology,
exact-composition comparisons and product preservation. The proof-context record is
`coord/changes/T4-tower-injective-components-proof-context.md`.

## Proved and sorry left

Closed 1 of 1 assigned holes: `AlgebraicGeometry.ProEtale.sp_tower_injective_components`
(node `det-sp-tower-injective-components`). Added 0 holes and split off 0 statements.
No `sorry` remains in any delivered Lean file. X8's eight earlier closures are not counted.
Existing named dependency statements are used as this stage permits; their proofs are not
claimed here.

## No longer needed

Removed `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison` and dependency
`lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`, including its obsolete
top-level tool-use entry. Its precoverage API requires extra structure unavailable for the
arbitrary induced AsSmall topology. Existing object-cohomology and exact-composition comparisons
supply the needed vanishing directly. The unit's coefficient-change argument is retained.

Removed redundant proof imports `Sheaf.CategoryTheory.RingedSiteModules` and
`Sheaf.Paper.SmoothPurityCoefficientTowers`, already supplied by the public abelian-tower import.
The unused experimental import `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero` is absent.
The existing ordinary evaluation adjunction also removes the need for a private construction
of pointwise small limits; no new module or node for that construction is needed.

No other module or node is claimed pruned. Evaluation adjoints, Grothendieck categories,
injective-module abelian acyclicity and D+ computation remain dependencies. No module is
withdrawn; removal of a direct dependency does not assert global unreachability.

## Where the brief, the DAG or earlier work was wrong

The current baseline has one hole, rather than the original nine, because X8 closed eight.
The declared module/abelian comparison does not directly apply to an arbitrary induced topology;
the more general existing ingredients above do. The direct-image argument uses the library's
dimension-shifting criterion. All blueprint unit steps and original statements are preserved.
No statement or definition repair was necessary, and no consumer adaptation is needed.

Previous delivery attempts were externally killed before completion; no push had occurred.
The initial dry run on resumption hit the compile limit. Diagnostic compiles isolated expensive
concrete coefficient comparisons. The shorter adjunction route and proof refactorings above
compile successfully without modifying launcher scripts or increasing the limit.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
