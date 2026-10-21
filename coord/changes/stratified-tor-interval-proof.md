# Stratified Tor interval proof: private elaboration context

## Reason

Item: `Sheaf.Paper.StratifiedTorIntervalDevissage` (group S3).
Direct composition of specialized derived-bifunctor comparisons exceeded the
60-second file limit by repeatedly converting sheaf monoidal instances. Generic
transport of the existing normalized tensor comparison avoids this conversion.
The change record is required because the proof adds section commands and a local
instance attribute, although no public declaration signature changes.

## Old

The changed interface commands were absent before (no generic section variables
or local derived-tensor instance selection). The following public theorem signature
is retained verbatim in both versions:

```lean
theorem torAmplitudeIn_of_constructible_of_uniform_local_model
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (c d : ℤ) (_hcd : c ≤ d)
    (hlocal : ∀ (S : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S)),
      HasFiniteConstantLocalModel Λ.X S N →
        DerivedCategory.torAmplitudeIn _ c d ((DerivedCategory.singleFunctor _ 0).obj N))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))
    (hM : IsConstantModelConstructible Λ.X X M) :
    DerivedCategory.torAmplitudeIn _ c d ((DerivedCategory.singleFunctor _ 0).obj M)
```

The item theorem had this signature and one `sorry`. Its planned proof
imported sectionwise Tor local detection, pro-etale inverse image, Cartesian
coefficients and adjunction composition. It had no generic helper section or
local selection of the canonical derived monoidal instance.

## New

The theorem has exactly the original signature and a complete proof with no
`sorry`. All original public imports and the explicit Cartesian-coefficients
unit-route import remain. New proved declarations are private. The section
`GenericTensor` introduces two category universes and section variables, ending
at `end GenericTensor`; these add no binders to the public theorem. The open
command enables tensor notation. The local instance attribute on
`DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` selects the same
canonical derived tensor used by `DerivedCategory.torAmplitudeIn`; its priority
change is not exported. The transparency option matches the comparison API and
is only an elaboration setting.

The existing normalized derived tensor comparison is transported along
`supportPullbackIsoUpperStar`. Private proved helpers detect a fixed Tor interval
on an open-closed pair and reflect it along an isomorphism. The actual refinement
leaf factorizations, empty covering family and reverse-index induction finish the
proof. The DAG proof/proof_deps/proof_origin record this internal-module route.
No file or proof is split to evade the compile limit.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StratifiedTorIntervalDevissage | S3 | Complete proof; original public signature retained |

There are no current Lean importers of this item. Its public theorem signature,
visibility and original public imports remain identical; no consumer adaptation
is required. DAG parents continue to cite the original declaration. The existing
finite refinement and every unit proof step remain, including the explicit
Cartesian-coefficients import. No source-library module changes or withdrawals
are included. No exported attribute, definition, or instance body changes.

## Status

landed 20261021T203822-L-3877416 2026-10-21 (merge of deliver/S3/Sheaf.Paper.StratifiedTorIntervalDevissage)

Implemented in the sandbox. The complete zero-hole file compiled successfully
through `lcompile.py` in 35.1 seconds and, after removing profiling, in 37.0
seconds. Final compile/preflight are run by `deliver3.py`. The independent reader
checks the exact public signature, private helper scopes, canonical tensor
comparison, empty-cover case, reverse-index induction and root-isomorphism
descent. No new nodes or holes are added.
