# profiniteTestProjection and existsUnique_condensedFieldContinuousMapIso

## Reason
The presentation-matrix statements need the continuous coefficient realization. Keeping
those declarations in the original item would create an import cycle when its proof
imports the corank and matrix lemmas. Move the existing realization and its private
proof helpers into `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`, and
publicly reexport it from the original item. Every existing public signature and the
projection definition remain the same. The uniquely characterized realization is also
provided for arbitrary totally disconnected normed fields, which the new proof APIs use.

## Old
In `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`:

```lean
noncomputable def profiniteTestProjection (X : Scheme.{u}) (S : Profinite.{u}) :
    C(((profiniteToProEtOf X).obj S).left, S)

theorem existsUnique_condensedFieldContinuousMapIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    ∃! e : Mon.mk (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) ≅
        Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousCoefficientRingSheaf X E)),
      ∀ (S : Profinite.{u}) (f : C(S, E)),
        (((pointUpperStarLowerStarAdjunction.comp
            (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv
              _ _ e.hom.hom).hom.app (Opposite.op S)) (ULift.up f) =
          ULift.up (f.comp (profiniteTestProjection X S))
```

## New
The exact two signatures above, with the same declaration names and universes, now live
in `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`. The original module
has `public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`.
`profiniteTestProjection` retains its original body. The private implementation helpers
move with it. No original public definition changes its mathematical value. The new
`condensedFieldContinuousMapIso` chooses from a proved *unique* characterization.

## Users
The original textual-user search found only the item. A later preflight, against the
newly fetched base, found the newly landed `Sheaf.Paper.IntegralScalarContractive`.
It also imports private helpers using `import all` and must follow their extraction.
The public users below see the same names by public reexport.

The original IntegralScalarContractive compiles against the published baseline but fails
against the delivered extraction with unknown identifiers `profiniteTestProjection_natural`
(lines 56 and 99), `pushforwardRingMonObj` (line 110), `canonicalComponentArrow` (line 170),
and `isIso_of_affine_weaklyContractible` (line 281). Its only adaptation replaces
`import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` by
`import all Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization` on line 11.
The adapted file compiles against the extraction. Every declaration, signature, proof,
attribute, and visibility is byte-for-byte unchanged. No other importer is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | F1 | public reexport and proof imports |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | not adapted | unchanged public API |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | not adapted | unchanged public API |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | not adapted | unchanged public API |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | forced one-line proof import; same private helper types and proofs |

## Status
landed 20261016T005128-L-4190704 2026-10-16 (merge of deliver/F1/Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality)
