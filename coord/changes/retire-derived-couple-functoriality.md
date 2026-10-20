# CategoryTheory.BigradedExactCouple: retire the duplicate functoriality module

## Reason

Complete the retirement listed in `coord/retire-items.tsv`. The upstream twin now
provides the identical public `CoupleMorphism` structure and
`derivedCoupleFunctoriality` theorem over the same upstream `BigradedExactCouple`.
Keeping their Sheaf copies causes duplicate declaration names when the two import
routes meet. Switch every live consumer to the twin, withdraw the copy, and point
`lem-sp-derived-couple-functoriality` at the upstream implementation.

The old copy additionally exposed `exactCoupleFiniteTransport` and
`factors_iff_image_le`. The upstream twin has the same proved helpers privately.
The only external user of either helper is `FiniteRangeComparison`, in proof
bodies. Its proof-only `import all` makes those upstream helpers available without
changing upstream visibility, copying proofs, or creating new declarations.
No definition, mathematical statement, proof body, target, or upstream file changes.

## Old

The withdrawn module publicly imported:

```lean
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
```

It declared the following public interfaces in
`CategoryTheory.BigradedExactCouple` (verbatim signatures):

```lean
structure CoupleMorphism {s : ℕ} (X Y : BigradedExactCouple C s) where
  tD : ∀ p q : ℤ, X.D p q ⟶ Y.D p q
  tE : ∀ p q : ℤ, X.E p q ⟶ Y.E p q
  alpha_comm : ∀ p q : ℤ,
    tD p q ≫ Y.alpha p q = X.alpha p q ≫ tD (p - 1) (q + 1)
  f_comm : ∀ p q : ℤ,
    tE p q ≫ Y.f p q = X.f p q ≫ tD (p + 2) (q - 1)
  g_comm : ∀ p q : ℤ,
    tD p q ≫ Y.g p q = X.g p q ≫ tE (p + s) (q - s)

theorem exactCoupleFiniteTransport {C : Type u} [Category.{v} C] [Abelian C]
    (X Y : BigradedExactCouple C 0)
    (t : ∀ p q : ℤ, X.E p q ⟶ Y.E p q)
    (e : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).E p q ⟶ (Y.pageCouple r).E p q)
    (hzero : ∀ p q, e 0 p q = t p q)
    (hd : ∀ r p q, e r p q ≫ (Y.pageCouple r).d p q =
      (X.pageCouple r).d p q ≫ e r (p + 2 + r) (q - 1 - r))
    (hnext : ∀ r p q,
      ∃ k : kernel ((X.pageCouple r).d p q) ⟶ kernel ((Y.pageCouple r).d p q),
        k ≫ kernel.ι ((Y.pageCouple r).d p q) =
          kernel.ι ((X.pageCouple r).d p q) ≫ e r p q ∧
        (X.pageCouple r).derivedEProjection p q ≫ e (r + 1) p q =
          k ≫ (Y.pageCouple r).derivedEProjection p q) :
    ∀ r p q,
      (Y.cycleBoundaryTower.Z r p q).Factors
        ((X.cycleBoundaryTower.Z r p q).arrow ≫ t p q) ∧
      (Y.cycleBoundaryTower.B r p q).Factors
        ((X.cycleBoundaryTower.B r p q).arrow ≫ t p q)

theorem factors_iff_image_le {A B : C} (P : Subobject B) (f : A ⟶ B) :
    P.Factors f ↔ imageSubobject f ≤ P

theorem derivedCoupleFunctoriality (X Y : BigradedExactCouple C 0)
    (T : CoupleMorphism X Y) :
    (∃ M : ∀ n : ℕ, CoupleMorphism (X.pageCouple n) (Y.pageCouple n),
      (∀ p q : ℤ, (M 0).tD p q = T.tD p q) ∧
      (∀ p q : ℤ, (M 0).tE p q = T.tE p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (M (n + 1)).tD p q ≫ (Y.pageCouple n).derivedDInclusion p q =
          (X.pageCouple n).derivedDInclusion p q ≫ (M n).tD p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        ∃ k : kernel ((X.pageCouple n).d p q) ⟶
          kernel ((Y.pageCouple n).d p q),
          k ≫ kernel.ι ((Y.pageCouple n).d p q) =
            kernel.ι ((X.pageCouple n).d p q) ≫ (M n).tE p q ∧
          (X.pageCouple n).derivedEProjection p q ≫ (M (n + 1)).tE p q =
            k ≫ (Y.pageCouple n).derivedEProjection p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (M n).tE p q ≫ (Y.pageCouple n).d p q =
          (X.pageCouple n).d p q ≫ (M n).tE (p + 2 + n) (q - 1 - n))) ∧
    (∀ (LX : LimitSubobjects X) (LY : LimitSubobjects Y),
      (∀ p q : ℤ,
        (LY.Z p q).Factors ((LX.Z p q).arrow ≫ T.tE p q) ∧
        (LY.B p q).Factors ((LX.B p q).arrow ≫ T.tE p q)) ∧
      (∀ p q : ℤ, ∃ (e : X.pageInfinity LX p q ⟶ Y.pageInfinity LY p q)
          (z : (LX.Z p q : C) ⟶ (LY.Z p q : C)),
        (LX.Z p q).arrow ≫ T.tE p q = z ≫ (LY.Z p q).arrow ∧
        z ≫ cokernel.π (Subobject.ofLE (LY.B p q) (LY.Z p q)
              (limitBoundary_le_cycle Y LY p q)) =
          cokernel.π (Subobject.ofLE (LX.B p q) (LX.Z p q)
              (limitBoundary_le_cycle X LX p q)) ≫ e)
    )
```

The five adapted modules imported `Sheaf.CategoryTheory.DerivedCoupleFunctoriality`.
`NaturalTruncationCouple` used a public import; the others used proof-only imports.

## New

The old module is withdrawn through `deleted.txt`. The two main public declarations
above are supplied verbatim by
`WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality`, which is unchanged.
The corresponding imports become:

```lean
public import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
```

in `NaturalTruncationCouple`, and:

```lean
import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
```

in `ExactCoupleMorphism`, `ExactCoupleDifferential`, and `TruncationExchangeAbutment`.
`FiniteRangeComparison` uses:

```lean
import all WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
```

Its existing helper applications and every other proof body are unchanged.
The upstream helpers have the exact finite transport and image-factorization
signatures above, with private visibility. Consumers of the main structure and
theorem see the same signatures from the upstream module. The DAG's Lean attachment
moves to the twin; its statement, proof plan, proof dependencies and unit stay intact.

## Users

`tools/downstream.py` reports 36 transitive consumers. Its `--uses` checks find
`CoupleMorphism` in `NaturalTruncationCouple` and `ExactCoupleDifferential`, the
main theorem in `ExactCoupleDifferential`, and both helper names only in
`FiniteRangeComparison` (besides the withdrawn module itself).
There are five current direct importers. The older retirement row also lists
`Sheaf.CategoryTheory.CoproductTruncationCouple`, which is already absent and has
no quarantine source importing the item; no file for it is added or deleted here.
All five adapted modules were unclaimed when copied. Every adapted consumer
compiles against the migration, without any signature or proof-body edit.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.BoundedAboveCoherentRHom | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Algebra.Homology.CompleteLocalCoherentDuality | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Algebra.Homology.PseudoCoherentTensorClosure | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Algebra.Homology.SemidualizingRHomConservative | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.ClosedPointSupportDetection | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRangeComparison | unclaimed | Proof-only import all of upstream; reuses its proved private finite transport and image helpers. |
| Sheaf.AlgebraicGeometry.HypercohomologyConvergenceStatement | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.HypercohomologyFiltrations | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleLeftComplete | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution | S3 | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.TruncationExchangeAbutment | unclaimed | Import switched to the upstream twin; declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCohomologyAcyclicBasis | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.CategoryTheory.ExactCoupleMorphism | unclaimed | Import switched to the upstream twin; declarations and proof bodies unchanged. |
| Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.CategoryTheory.NaturalTruncationCouple | unclaimed | Import switched to the upstream twin; declarations and proof bodies unchanged. |
| Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.CategoryTheory.SiteTruncationDerivedLimit | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.CategoryTheory.TruncationsAndHomotopyColimits | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.Paper.ExactCoupleDifferential | unclaimed | Import switched to the upstream twin; declarations and proof bodies unchanged. |
| Sheaf.SecTraceFormula.LocalDerivedTensorNonvanishing | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.SixFunctors.UnboundedClassicalTruncation | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.TraceFormula.AlgebraicShriekCalculus | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.TraceFormula.AlgebraicShriekRelativePerfect | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.TraceFormula.UpperShriekBoundedCoherent | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Transitive consumer; declarations and proof bodies unchanged. |

No target statement uses a changed definition: definitions do not change, so no
semantic target review is reopened. DAG parents retain the same node and theorem;
only the module that supplies it changes. No quarantined module imports the copy.

## Status

landed 20261020T211824-L-3506809 2026-10-20 (merge of deliver/S4/Sheaf.CategoryTheory.DerivedCoupleFunctoriality)
