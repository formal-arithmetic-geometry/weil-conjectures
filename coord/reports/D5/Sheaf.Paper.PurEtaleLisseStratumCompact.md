## What changed

Proved `AlgebraicGeometry.Etale.isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf` with its existing signature and docstring unchanged. Private generic helpers prove that an additive left adjoint carries compact objects to compact objects when its right adjoint preserves coproducts, and that dualizable objects are compact when the tensor unit is compact.

The unit is compact by the constant-sheaf/derived-global-sections adjunction and the existing rank-one compactness theorem. The lisse sheaf is dualizable by the source library's lisse-duality and bounded-complex duality theorems. Open extension and closed direct image then transport compactness through their adjunctions; exactness and the single-functor comparison identify the resulting object with the one in the statement.

The two new auxiliary modules are both proved: `Sheaf.Paper.PurEtaleLisseDualizable` and `Sheaf.Paper.PurEtaleClosedRightAdjointCoproducts`. The latter explicitly constructs coproduct triangles using opposite product triangles and proves preservation by comparing distinguished triangles and reflecting through fully faithful closed direct image. No existing definition or statement changes, and no consumer adaptation is needed. The static gate requires a change record for added proof-elaboration commands: `coord/changes/pur-etale-lisse-stratum-proof-commands.md`.

Validation: all three delivered modules compiled through `lcompile.py --all` on resumption, with no errors or warnings. The main theorem signature matches the current source token for token, and each node’s proof dependencies equal the union of its proof steps’ uses. The corrected dry run passed compilation and preflight (commit `fa9d2f5bb9`); the proof-elaboration change record is included. Review class: CODEX. The theorem may depend on existing library obligations, as stage 3 requires.

## Proved and sorry left

Holes closed: 1 of the item's 1 original holes, namely `AlgebraicGeometry.Etale.isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf` (`lem-pur-etale-lisse-stratum-compact`).

New proved declarations: `AlgebraicGeometry.Etale.isDualizable_singleFunctor_lisseFlat` (`lem-pur-etale-lisse-dualizable`) and `AlgebraicGeometry.Etale.preservesCoproducts_closedRightAdjoint` (`lem-pur-etale-closed-right-adjoint-coproducts`). These are proved auxiliary theorems, not admitted split-offs.

Holes added: 0. Sorries left in all three delivered modules: 0. No sorry occurs in a definition.

## No longer needed

The following direct proof imports from the original item are removed. Modules needed by the closed-support auxiliary remain imported there; this list does not claim that other targets cease to use them.

- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`
- `Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension`

The following nodes are no longer proof dependencies of the delivered DAG route. Existing source-library theorems supply the needed instances and canonical constructions; their own underlying prerequisites may still occur elsewhere. The proof uses source-library duality and canonical derived adjunctions instead of the ringed-site internal-Hom/global-sections realization and strict-perfect coefficient package. None realizes this unit's own statement or a unit proof step: `sk-def-sf-operations.realized` is empty.

- `def-pur-derived-internal-hom`
- `def-weil-pbc-projective-module`
- `def-weil-pbc-strict-perfect-coefficient-package`
- `lem-cbc-open-closed-recollement`
- `lem-kun-grothendieck-derived-coproducts`
- `lem-pur-rhom-global-sections`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-ring-modules-grothendieck-abelian`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`
- `prop-weil-open-closed-recollement-adjunctions`
- `prop-weil-pbc-inverse-image-modules-exact`

Obsolete top-level `tool_uses` approvals are also removed from the item node: `lem-cbc-open-closed-recollement`, `lem-kun-grothendieck-derived-coproducts`, `lem-pur-rhom-global-sections`, `lem-weil-pbc-locally-noetherian-quasi-separated`, `lem-weil-pbc-module-sheaves-grothendieck-abelian`, `lem-weil-pbc-ring-modules-grothendieck-abelian`, `lem-weil-pbc-ringed-internal-hom-exact-restriction`, `lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`, `prop-weil-open-closed-recollement-adjunctions`, `prop-weil-pbc-inverse-image-modules-exact`. The approvals still used by the auxiliary arguments remain in their original order.

The retained attempt's `PurEtaleLisseInternalHomCoproducts` module and node were never delivered and are omitted. The proved dualizability statement replaces that intermediate route. No tracked library file is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The retained report claimed a compiling main theorem and one open closed-right-adjoint theorem. On resumption the actual closed-right-adjoint and lisse internal-Hom proofs were complete, but the main proof timed out during kernel checking. Compile cuts located the expansion at specializing the derived internal-Hom compactness step to a degree-zero sheaf; a generic derived object checked promptly. The implemented tensor-dual argument avoids that large closed-structure conversion and compiles within the normal limit. No timeout limit was raised, no definition was made hollow, and no proof or file was split to evade the limit.

The DAG now records the actual duality argument and the two proved auxiliary statements. The paper's prime, invertibility and prime-power coefficient hypotheses remain in the theorem's signature; finite coefficients suffice for the proof, so unused-variable linting is disabled only for that declaration.

## New nodes

`lem-pur-etale-lisse-dualizable` states that a finite locally constant sheaf with flat geometric stalks becomes dualizable in degree zero. Its proof converts stalkwise flatness to sheaf flatness, uses existing lisse duality, and applies bounded-complex duality to the single complex. Source: Bhatt--Scholze Section 6.4, Example 6.4.1 and Lemma 6.4.6. Edge cases: zero sheaf and empty scheme are covered by dualizability of zero; no finite-type hypothesis is needed. The module is `Sheaf.Paper.PurEtaleLisseDualizable`.

`lem-pur-etale-closed-right-adjoint-coproducts` states coproduct preservation for the derived closed-immersion right adjoint over a finite-type scheme over an algebraically closed field. The proof uses the open complement's finite cohomological dimension, compares coproducts of closed-support distinguished triangles, and reflects the first comparison through closed direct image. Source: Bhatt--Scholze Section 6.4 and the item's closed-support argument. Empty families and empty closed subschemes are included by the categorical proof. The module is `Sheaf.Paper.PurEtaleClosedRightAdjointCoproducts`.

The search records include LeanSearch, LeanFinder/Loogle and grep. The results did not supply either specialized statement; existing source-library declarations supply their geometric inputs. The proof-elaboration command change is documented in `coord/changes/pur-etale-lisse-stratum-proof-commands.md`; no existing signature changes.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
