# AlgebraicGeometry.Scheme.exists_finite_fppf_affine_open_refinement

## Reason

The adopted source module already proves this exact declaration, with the same name, binders, universes and conclusion. Retire the duplicate holed Sheaf copy, preserve the DAG node by attaching it to the proved source declaration, and redirect all five current direct private proof imports. No source-library file changes. The replacement source proof follows the same affine-neighborhood, open-image and compactness argument as Tag 021P. The server reports only the three allowed axioms.

## Old

Defined in `Sheaf.AlgebraicGeometry.FppfAffineRefinement`:

```lean
theorem exists_finite_fppf_affine_open_refinement {U : Scheme.{u}} [IsAffine U]
    {I : Type v} (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ U)
    (hf : Presieve.ofArrows T f ∈ fppfPrecoverage U) :
    ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (T (i j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
        Presieve.ofArrows (fun j ↦ (V j).toScheme)
          (fun j ↦ (V j).ι ≫ f (i j)) ∈ fppfPrecoverage U := by
  sorry
```

## New

The identical signature is already proved in `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`:

```lean
theorem exists_finite_fppf_affine_open_refinement {U : Scheme.{u}} [IsAffine U]
    {I : Type v} (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ U)
    (hf : Presieve.ofArrows T f ∈ fppfPrecoverage U) :
    ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (T (i j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
        Presieve.ofArrows (fun j ↦ (V j).toScheme)
          (fun j ↦ (V j).ι ≫ f (i j)) ∈ fppfPrecoverage U
```

The duplicate module is withdrawn via `deleted.txt`; each direct consumer replaces `import Sheaf.AlgebraicGeometry.FppfAffineRefinement` with `import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. Parent DAG dependencies still name the same mathematical node, whose Lean attachment now points to the proved source declaration; no parent proof or dependency is removed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ActionGroupoidTorsorComparison | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.AffineStackStabilizerEtaleComparison | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfFiniteAffineRefinement | unclaimed | Replace only the private import; all declarations and signatures remain verbatim. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcQCSeparatedDescent | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceHigherDirectImageQuasiCoherent | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenGluing | unclaimed | Current source preserved verbatim; already omits the duplicate import. |
| Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood | J1 | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.CurveSmoothPolarizationCover | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.EtaleAffineQuotientRepresentable | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.EtaleRelationQuotient | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.FppfAffineRefinement | C7 | Withdraw duplicate; node reattached to identical proved source declaration. |
| Sheaf.AlgebraicGeometry.FppfAffineRefinementPullbackModel | unclaimed | Replace only the private import; all declarations and signatures remain verbatim. |
| Sheaf.AlgebraicGeometry.FppfAffineSheafificationRestriction | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.FppfAffineSiteToposEquivalence | unclaimed | Replace only the private import; all declarations and signatures remain verbatim. |
| Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction | unclaimed | Current source preserved verbatim; already omits the duplicate import. |
| Sheaf.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding | unclaimed | Current source preserved verbatim; already omits the duplicate import. |
| Sheaf.AlgebraicGeometry.FppfLocalOpenSubfunctorDescent | unclaimed | Current source preserved verbatim; already omits the duplicate import. |
| Sheaf.AlgebraicGeometry.FppfSchemeDataSheafGluing | unclaimed | Current source preserved verbatim; already omits the duplicate import. |
| Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData | F7 | Replace only the private import; all declarations and signatures remain verbatim. |
| Sheaf.AlgebraicGeometry.FppfSheafificationAffineContinuity | unclaimed | Replace only the private import; all declarations and signatures remain verbatim. |
| Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.ProperCurveAutomorphismScheme | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.ReducedSingletonFieldFactorization | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.RepresentableEtaleQuotientPresentation | unclaimed | Current source preserved verbatim; already omits the duplicate import. |
| Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SeparatedGroupSpaceGeometricScheme | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable | W8 | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SeparatedLqfAffineRelationCover | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.SpaceSquareZeroRingedRealization | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.Paper.NormalLatticeFiniteCoverPresentation | M6 | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.Paper.TameIntegralReductionFamily | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.SecPurity.NormalLocallyConstantFiniteSection | unclaimed | Transitive consumer; no declaration or signature changes, no edit required. |
| Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent | unclaimed | Current source preserved verbatim; already omits the duplicate import. |

## Return repair

The current return at `ff32e2d5042` names the newly proved
`AlgebraicSpaceOpenGluing` landed at `b3210a1419a`. Take its current source
verbatim, including every private helper and the complete proof. It no longer
imports the duplicate module, so no edit to that module is delivered.

Also refresh `FppfFamilyCoproductDescentEncoding` from the current source. Its
complete proof already omits the duplicate import, so no edit is needed.
The other previously repaired consumer proofs remain intact.

Two new current direct importers, `AlgebraicSpaceFppfFiniteAffineRefinement` and
`FppfSheafificationAffineContinuity`, require the same private import replacement.
There are five actual single-line import changes. No signatures, public imports,
proof bodies or declarations are changed. The active holder of
`FppfSheafRepresentabilityDescentData` is F7; its import replacement is necessary
for the duplicate's withdrawal under brief step 8b.

## Status

landed 20261024T184758-L-3179608 2026-10-24 (merge of deliver/C7/Sheaf.AlgebraicGeometry.FppfAffineRefinement)
