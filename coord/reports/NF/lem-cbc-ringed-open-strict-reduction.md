## Worker report

The delivery states `lem-cbc-ringed-open-strict-reduction` in
`Sheaf.Paper.RingedOpenStrictReduction`. The primary declaration is
`AlgebraicGeometry.Scheme.cbcRingedOpenStrictReduction`; the node's
`lean.declarations` also records the strict construction and its augmentation,
coefficient-action, normalization and cocycle clauses. The node's mathematical
statement, proof and dependency lists are unchanged. No proof is completed.
All postponed proofs are named theorems with the source and the relevant full
natural-language argument in their docstrings. Definitions contain real data;
choices occur only for maps or isomorphisms uniquely characterized by their local
generator formulas. The coefficient identifications use `asIso` on existing maps.

Hypotheses and clauses, matched individually:

| Node text | Lean rendering |
| --- | --- |
| Schemes T and an open immersion e:W→T | `{T : Scheme.{u}} (W : T.ProEt) [IsOpenImmersion W.hom]`. Every open immersion supplies this pro-etale object; the source scheme is `W.left` and the immersion is `W.hom`. This uses the concrete site rather than choosing a different skeleton. |
| A,I and the completed coefficient datum | `{A : Type (u+1)} [CommRing A] (d : AdicCoefficientDatum A)`. The inherited fields give the Noetherian condition, finite generation, additive torsion of A/I and perfect positive quotients; `quotientFinite` gives their finiteness. |
| n≥1 | An index `n : ℕ` means exponent `n+1`, exactly as in the recorded datum. `a ≤ b` covers every b+1≥a+1≥1, including equality. |
| Completed coefficients, with their restrictions | `completedReductionCoefficient`, `reductionCoefficient`, and `completedReductionProjection` from the recorded datum. `cbcFiniteRestriction` and `cbcCompletedRestriction` are `asIso` of the existing `cbcFiniteSliceMap` and `cbcCompletedSliceMap`. Their defining normalizations are already fixed by the continuous-function presheaf units and the limit projections. `cbcQuotientSquare` and `cbcProjectionSquare` retain all the coefficient maps. |
| The specified e_! | `cbcCompletedExtension` is an abbreviation for the existing `cbcOpenShriek d W.hom ...`. This transports by `cbcModuleToSlice`, takes `extensionByZeroPresheaf`, and applies `PresheafOfModules.sheafification`. `cbcRingedOpenExtension` is its general coefficient-ring interface, needed at the quotient rings; it uses that same construction with the specified ringed slice comparison. |
| e_! on strict towers and complexes | `cbcCompletedTowerExtension` is actual postcomposition of ℕᵒᵖ diagrams. `mapHomologicalComplex (.up ℤ)` extends degreewise, and `mapDerivedCategory` is used only for the exact functors. `cbcCompletedTowerExtension_exact` states levelwise exactness. |
| Every K in D(Mod(A_W)); a canonical natural isomorphism into D(Tow_A(T)) | `cbcRingedOpenStrictReduction` asserts a unique natural isomorphism `ρ` between `(cbcCompletedExtension W d).mapDerivedCategory ⋙ completedReductionTower T d` and `completedReductionTower W.left d ⋙ (cbcCompletedTowerExtension W d).mapDerivedCategory`, with the specified representative normalization. Thus its components cover every K and its naturality includes every derived morphism. |
| A flat-term K-flat representative | The normalization quantifies over `P : CochainComplex (reductionModules W.left (completedReductionCoefficient W.left d)) ℤ`, with `CochainComplex.IsKFlatIndependentCoefficients` and `∀ p, SheafOfModules.IsFlatOnSite (J := ProEt.topology W.left) ... (P.X p)`. These assumptions concern the computing representative, not K. The endpoint computation maps are explicitly required to be isomorphisms. |
| The actual strict complex map | `cbcStrictReductionIso` is a natural isomorphism of ordinary module-to-strict-tower functors. `cbcStrictReductionComplexIso` applies it in every degree; it is an actual isomorphism of strict complexes. The equation in the main theorem identifies its localization with `ρ` using the published universal reduction counits and the exact-functor localization comparisons. |
| Formula [p]⊗b↦[p⊗b\|W] | `cbcOpenScalarIso_existsUnique` specifies this formula on every module, every ambient site object V, every arrow `a : V ⟶ W`, every quotient coefficient b, and every section x. `cbcOpenSection` is the direct-sum injection followed by the actual module-sheafification unit. Restriction of b is exactly `cB.hom.hom.app (op (Over.mk a)) b`. The existing tensor API writes b⊗x; the displayed rule is precisely the node's x⊗b with this conventional order. |
| Independence after localization | The main theorem's unique natural-isomorphism characterization uses all flat-term K-flat representatives simultaneously. The equation with `cbcLeftReductionComputation` and `cbcRightReductionComputation` specifies the localization on each, so choices of representatives give the same comparison. Its proof docstring explains descent and the inverted quasi-isomorphism case. |
| Every quotient transition | `cbcStrictReductionIso` takes values in the actual functor category ℕᵒᵖ ⥤ Mod(A_T). Its components are natural transformations of towers, so they commute with every arrow, including composites and identities. `cbcQuotientSquare` also retains the literal quotient coefficient maps. |
| Both quotient augmentations, before localization | `cbcStrictReduction_augmentation` is equality of actual module morphisms at every n, using the existing `completedReductionModuleUnit` on T and W and the actual open-extension functor. Apply it to every `P.X p`: equality in every n and p is equality of the augmented strict complex diagrams, not just their derived evaluations. |
| P_n-module comparison before scalar restriction | `cbcOpenScalarIso` has codomain `reductionModules T B`, where B is the finite quotient coefficient sheaf. `cbcOpenRestrictIso` is fixed by identity on extension summands. The defining equation of `cbcStrictReductionIso_existsUnique` says its n-th map is scalar restriction of the former comparison followed by the inverse of the latter. No quotient-ring action is replaced by an arbitrary A-linear map. |
| Successive quotient normalization | `cbcStrictReduction_normalization` is the commuting square using the datum's actual `reductionBalance` maps and the specified finite-ring comparisons. It is stated at every `p : ℤ`, hence is equality of chain maps over P_a before scalar restriction. The K-flat base-change results in the proof make these precisely the derived normalization maps. |
| Equal-index unit | All normalization hypotheses are non-strict `a ≤ b`, so b=a is included. The datum's identity quotient map and balancing formula then give `(x⊗r)⊗s ↦ x⊗rs`. No equality-index case is discarded. |
| Three-index cocycle | `cbcNormalizeLeftAt` and `cbcNormalizeRightAt` are the two actual parenthesizations of the datum's balancing chain maps in degree p. `cbcTripleScalarComparisonAt` applies the three prescribed coefficient comparisons. `cbcStrictReduction_cocycle` states compatibility of each parenthesization and equality of the two paths, both on T and W, for all c≥b≥a and every p. This expresses the actual strict chain equations; localization preserves them. |
| No completeness or quasi-compactness required | Neither the declarations nor any computing hypothesis assumes completeness of K or quasi-compactness of the immersion. The reused `cbcOpenShriek` and its exactness interfaces also have neither assumption. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.Paper.AdicCoefficientDatum` and its public
  `Sheaf.Paper.CompletedAdicCoefficientDatum` interface:
  `AdicCoefficientDatum`, `reductionCoefficient`, `completedReductionCoefficient`,
  their quotient/projection maps, `reductionModules`, `reductionTowerCategory`,
  `reductionChange`, `reductionRestrict`, `reductionTensorSection`,
  `completedReductionModuleTowerFunctor`, `completedReductionComplexTowerFunctor`,
  `completedReductionTower`, `completedReductionTowerComplexCounit`, and
  `reductionBalance` with its projection/quotient composition laws.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`, the concrete site
  equivalence behind the existing slice transport. The existing `cbcSliceFunctor`
  calls this declaration for weakly-etale cancellation.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`, including its direct-sum sections.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, through `reductionRestrict`.
- Reused helper declarations in `Sheaf.Paper.CompletedExtensionZeroComparison`:
  `cbcSliceFunctor`, `cbcFiniteSliceMap`, `cbcCompletedSliceMap`,
  `cbcModuleToSlice`, `cbcOpenShriek`, and its additive/finite-limit/finite-colimit
  theorems. The comparison maps are reused rather than redefined from existence.
- `Sheaf.Paper.CompletedTowerPullback`: `completedReductionModuleUnit`, the
  existing strict quotient augmentation, imported through the preceding module.

The stated proof dependencies are imported explicitly, including the independent-
coefficient K-flat resolution and descent interfaces, the ringed slice tensor
formula, the open-unit tensor normalization, derived change of rings, the
levelwise abelian diagram API, sheafification localization, and the localization
universal property. `lem-cbc-ringed-open-flat-resolution` has no recorded Lean
interface and is not imported; the proof docstring identifies its role. No new
statement needs a definition from that unstated proof dependency.

Import-cycle note: the reused helper module also contains the downstream parent
statement `lem-cbc-completed-extension-zero-comparison`. This delivery uses its
coefficient and extension definitions, never that downstream theorem. Under
stage 2 rule 7, a future proof import from that parent module back to this module
must be omitted because it would create an import cycle. There is no circular
use of theorem declarations in this delivery.

Edge cases checked before and during the statement design: W=T gives identity
slice transport and the identity tensor comparison; W=∅ gives the zero extension;
K=0 and arbitrary shifts are included by unbounded cochain complexes; I=A gives
zero quotient coefficients and zero completed coefficient ring; n=0 is the first
positive quotient; a=b is the tensor unit; c=b=a is included in the cocycle;
non-complete K, e.g. a torsion quotient, is allowed. The empty site object may
have its unique arrow to W even when W is empty; the actual direct-sum/sheafification
construction handles it, rather than incorrectly assigning zero merely from the
absence of topological points. No extra boundedness, separatedness or finiteness
hypothesis on schemes is imposed. Site object universe u+1 and morphism universe u
are retained, and no equality between these universes is imposed.

Searches performed:

- `msearch.py ... leanfinder "Extension by zero commutes with strict adic quotient reduction towers and augmentation"`: 8 results about ordinary adic completion, including `IsAdicComplete.StrictMono.factorPow_comp_extend` and `AdicCompletion.transitionMap_comp_reduceModIdeal`; none concerns ringed sheaf extension or strict derived towers.
- `msearch.py ... loogle "SheafOfModules.restrictScalars, Functor"`: 0 hits.
- `msearch.py ... grep "extensionByZero|strictReduction|openReduction" Mathlib/CategoryTheory`: 0 hits.
- `msearch.py ... leansearch "Extension by zero sheaf of modules tensor quotient ring strict inverse tower derived category"`: 8 hits, including `DerivedCategory.instHasZeroObject`, `SheafOfModules.unit`, `SheafOfModules`, tilde sheaves and generic Ext results; no matching statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for strict/ringed/open reduction, completedReduction, the item id, and candidate declaration names. No exact item declaration exists. The older `SfCbcExtensionZeroCompletion` uses constant coefficients and does not state this completed-ring result. `IntegralOpenReductionComparison` is a specialized integral/complete setup. The search also found the existing completed-ring slice maps and extension in `CompletedExtensionZeroComparison`, which are now reused. A candidate helper name `cbcOpenExtension` collided with a constant-coefficient helper in `OpenLocalizedCounitComparison`; the new general coefficient helper is named `cbcRingedOpenExtension` instead.

Sources checked: the complete six-step node proof; the blueprint proof's opening
reduction sentence; Stacks `sites-cohomology.tex`, `lemma-j-shriek-and-tensor`
(Tag 0GL1); and the dependency declaration signatures and docstrings. The example
`CompactObject.lean` is now withdrawn; the delivery follows the active statement
module conventions instead. No statement correction or disputed statement is needed.

Validation: all compilation is through the prescribed `scompile.py` server wrapper
with its unchanged 60-second per-file limit. Higher-order complex functor equations
initially elaborated too slowly; the normalization and cocycle equations now quantify
over every degree of the same actual chain maps. This changes no mathematical
clause. Final compile and delivery preflight results are recorded below.

## Second reading by NF

This is the single dispatched worker's self-review; the independent review is the
maintainer's, as the dispatch brief specifies. No other agent was started. I reread
the node and the complete Lean module together. The table above checks each
hypothesis and clause. The review corrected a helper-name collision, replaced newly
constructed coefficient identifications with the existing normalized maps, retained
the actual pre-scalar-restriction comparison, and made both cocycle paths explicit.
The main theorem's normalization uses the actual strict complex map and both
canonical endpoint computation maps, so a bare unrelated natural isomorphism cannot
satisfy the statement. All non-strict index cases and the absence of completeness
and quasi-compactness hypotheses were checked again.

Final validation: `scompile.py` passed both the sandbox and library-name compiles
without errors or warnings (34.4 s and 29.5 s). `deliver2.py --no-push` printed
`OK (dry run): ... passes the preflight and compiles; nothing pushed`.
The recorded primary signature matches the file verbatim; the node differs from
the read-only repository only in `lean`; all Lean lines are at most 100 characters.
