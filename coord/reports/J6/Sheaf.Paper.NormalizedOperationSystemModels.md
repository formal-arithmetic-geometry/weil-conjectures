## What changed

Replaced the proof hole in `WeilConjectures.NormalizedOperations.normalizedOperationSystemModels` with a conjunction assembled from explicit tensor, unit, model, ordinary scalar-association and geometric-pullback proofs. The theorem signature is unchanged. The law structures retain exactly their original field propositions by definitional equality.

Tensor normalization uses the supplied reduction formula and cancellation of invertible factors. The pure-section adjoint is obtained from the actual horizontal transition, scalar transposition and tensor linearity. Simultaneous resolutions and tensor/quotient closure use the existing K-flat and flat-term results. The regular whole-system unit is proved flat, and its degree-zero single complex is K-flat by the existing bounded-above flat-complex criterion; its ordinary reduction is invertible by an explicit Hom-equivalence argument, and its normalized derived reduction follows from the recorded K-flat counit comparison.

The ordinary geometric scalar comparison is constructed as a mate. Its further level-adjunction mate is invertible because the normalized underlying-sheaf equations identify it with the direct-image identification. Naturality and ordinaryPullTransition then prove the actual transition formula. Pulled systems have flat terms because flatness can be checked at every level: the proof lifts a local finite-relation factorization to a covering sieve of the sequence site and transports its witnesses along horizontal maps. The node explicitly records both existing directions of the local finite-relation criterion used in this argument.

Added `Sheaf.Paper.GeometricScalarAssociationCocycle`, with a complete proof. The ordinary restriction square is checked under faithful underlying sheaves, then localized using the existing exact-square composition theorem. A proved general adjunction calculation transposes that cocycle to the required scalar-association cocycle. There is no inference from faithfulness of derived evaluation.

Added `Sheaf.Paper.CanonicalCoefficientSystemGeometry` for the separate geometric coefficient-realization construction described below. This construction supplies literal equality with the specified target tower and the prescribed constant-section transpose; the operation laws are proved independently for that realization.

Changed only the presentation of `operationScalarFunctor`, `operationScalarComplex`, `operationScalarCounit`, `operationUnitComplex` and `operationUnit` from `abbrev` to `def`, retaining their bodies and types verbatim. The two unit definitions are locally irreducible during declaration of the law structures and restored before the proofs. The scalar functor and complex wrappers retain ordinary reducibility throughout. These changes avoid repeated expansion of the scalar functor, complex wrappers and regular single-complex model. The sheaf monoidal instance is also kept locally irreducible while declaring the law structures, following the ordinary tensor source, and restored before the proofs; its mathematical value is unchanged. During these declarations the generic sheafification instance is disabled in favor of the existing coefficient-sized instance, then restored for the concrete schemes. The full module had exceeded the fixed compile limit. See `coord/changes/normalized-operation-unit-unfolding-J6.md`. The shared source and downstream scans find no other Lean consumers of these names. There are no forced adaptations and no source-library edits.

The pure-section, cochain and quotient field propositions now have explicit names, `operationTensorPureFormula`, `operationTensorCochainFormula` and `operationModelQuotientFormula`. Their bodies are verbatim the former field formulas, and the structure fields refer to them. This keeps repeated kernel checks of structure projections compact; the declaration-only diagnostic fell from 39.7 to 9.6 seconds. All three are real definitions with no proof hole. No downstream Lean module uses either affected structure. See `coord/changes/normalized-operation-law-formulas-J6.md`.

The complete three-module sandbox compiled successfully with `lcompile.py --all`: the coefficient geometry and scalar cocycle modules each took 0.2 seconds, and the complete item module took 55.2 seconds, with no errors or warnings. Unit K-flatness applies `SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite` at bound zero after the flat-term proof; it avoids unfolding the total-complex tensor unitor. The unused direct tensor-colimit import was removed; that theorem's own dependencies remain unchanged. A separate three-module scratch check verified that disabling an imported instance and restoring it locally leaves the original instance available to later importers. The scratch diagnostics are not part of the delivery.

## Proved and sorry left

Closed the original literal hole in `WeilConjectures.NormalizedOperations.normalizedOperationSystemModels` (node `lem-pur-normalized-operation-system-models`), with its statement unchanged. The item module contains zero literal `sorry`s.

Added one literal hole: `WeilConjectures.NormalizedOperations.canonicalCoefficientSystemGeometry`, node `lem-pur-canonical-coefficient-system-geometry`. It isolates construction of a geometric realization on the literal canonical coefficient tower, including its specified ring transpose and pull-transition formula. It does not assert any of the tensor, unit, model, ordinary scalar-association or scalar-cocycle laws that the main module proves. Its docstring and node give the complete transport argument, including empty schemes, zero rings and equal quotient indices. The proof must construct the target tower and transport all the ordinary and derived data through the ring-tower isomorphism; no definition chooses arbitrary data from this theorem.

Proved `WeilConjectures.SemilinearSections.geometricScalarAssociationCocycle`, node `lem-pur-geometric-scalar-association-cocycle`, with zero new holes. All private helpers in both proved modules have complete proofs.

Hole accounting: one original hole closed, one new hole added, net zero. This is a decomposition of the original construction/operation theorem, not a net hole reduction. The unit definitions contain no holes.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.SystemEvaluationKFlat`: the supplied tensor-evaluation model already gives K-flat evaluation; the proved evaluation-flatness theorem supplies flat terms. This also avoids importing its alternative localization instance.
- `Sheaf.Paper.NormalizedDVRTower`: its separate tower construction is not used by these operations on the supplied semilinear calculus.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: the supplied geometric representative models give the required K-flat computations directly.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: the scalar data already includes the normalized ordinary adjunction and its representative counit.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`: its finite coefficient presentation is not applied in the operation-law proof; the separate literal coefficient-realization lemma describes the constant-sheaf adjunction construction required here.

The written proof does not directly use the former proof dependencies `lem-pur-system-evaluation-kflat`, `def-coef-normalized-dvr-tower`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-pur-sheaf-ring-derived-coefficient-adjunction`, `prop-weil-pbc-proetale-constant-ring-map`, or the cochain scalar-association construction of `lem-pur-cochain-pullback-tensor-coherence`. Its chain tensor formula is supplied by the existing system reduction theorem; the scalar cocycle instead uses normalized adjunction transposes. The node's statement dependencies and all existing public imports stay unchanged. No module is withdrawn, and these removals do not claim that a module is globally unreachable through other consumers or public imports. No source declaration or proof is removed.

Removed obsolete top-level tool approvals for `lem-pur-system-evaluation-kflat`, `lem-weil-pbc-ringed-pullback-preserves-kflat`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-pur-sheaf-ring-derived-coefficient-adjunction`, and `prop-weil-pbc-proetale-constant-ring-map`. Retained the original approvals needed by the remaining proof or unchanged statement dependencies.

`Sheaf.Paper.KFlatRingedToposPullback` remains a private import for its proved conversion from AlgebraicInverseImage to the independent-universe interface. Its K-flat preservation theorem is not used in place of the supplied model fields.

## Where the brief, the DAG or earlier work was wrong

Taking `A.geometric` alone does not satisfy `CoefficientsIdentified`: that interface supplies an inverse-image coefficient presentation and underlying isomorphisms, whereas the conclusion requires literal equality with the fixed constant-presheaf sheafifications and a specified transpose equation. A ring isomorphism does not give equality of sheaf objects. The missing step is transport of the full geometric calculus through the canonical tower isomorphism, retaining the actual ordinary transitions. This is now a separate, sourced construction obligation rather than an implicit identification.

The three-index scalar cocycle also needs the normalization fields of Geometry. Arbitrary isomorphisms between the displayed functors would not suffice. The new proved cocycle uses precisely those fields.

No statement is disputed or weakened, and the purity-convention unit's route is unchanged (its unit record has no realized proof steps to bypass). New dependencies are either the two extracted parts of this node or existing proved tools/definitions.

## New nodes

`lem-pur-geometric-scalar-association-cocycle`: proved; ordinary underlying restriction coherence, localization of the ordinary square, and a general scalar-adjunction transpose calculation. It is a separate coherence result of the source's composition argument and has no added hole.

`lem-pur-canonical-coefficient-system-geometry`: one construction hole; literal target coefficient realization with the prescribed constant-section transpose and actual pulled-transition equation. It is strictly the coefficient-construction part of original steps 4–5 and leaves the operation-law proofs in the item module.

Both inherit chapter `sec-smooth-purity`, unit `sk-def-purity-conv`, and the parent blueprint ancestry. Mathlib searches through LeanSearch, LeanFinder, Loogle and source grep, together with the blueprint duplicate search, found no matching result for either actual interface. Definition-presentation record: `coord/changes/normalized-operation-unit-unfolding-J6.md`.

Additional definition-presentation record: `coord/changes/normalized-operation-law-formulas-J6.md`.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
