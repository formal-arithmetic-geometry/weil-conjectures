# Quotient tensor resolution homotopy retirement

## Reason

The item is listed as `retire` in coord/queue.tsv and coord/retire-items.tsv.
Its quotient theorem is already proved upstream with the identical signature.
The Sheaf copy additionally exposes ModuleCat.augmented_lift_homotopy, which
ResolutionInflationComparison uses for representations in an arbitrary abelian
category. The upstream copy makes this helper private. Preserve the existing
proved public helper in its own Sheaf module and redirect the quotient caller
to the upstream theorem. No upstream file or target statement is changed.

## Old

Both public theorems were declared in
Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy:

```lean
theorem augmented_lift_homotopy
    {D : Type*} [Category D] [Abelian D] {M N : D}
    (P : ProjectiveResolution M) (K : ChainComplex D ℕ) (π : K.X 0 ⟶ N)
    (hz : K.d 1 0 ≫ π = 0)
    (hzero : (ShortComplex.mk (K.d 1 0) π hz).Exact)
    (hsucc : ∀ n : ℕ,
      (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
        (K.d_comp_d _ _ _)).Exact)
    (a a' : P.complex ⟶ K) (haug : a.f 0 ≫ π = a'.f 0 ≫ π) :
    Nonempty (Homotopy a a')

theorem quotient_tensor_resolution_lift_homotopy
    {A C : Type u} [CommRing A] [CommRing C]
    (I : Ideal A) (J : Ideal C) (φ : A →+* C)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (R : ProjectiveResolution (ModuleCat.of C (C ⧸ J))) :
    let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex (.down ℕ)
    ∀ (ψ : (A ⧸ I) →+* (C ⧸ J))
      (a a' : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj R.complex)
      (k k' : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj (TC.obj R.complex)),
      (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) →
      (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) →
      (∀ x : P.complex.X 0, R.π.f 0 (a'.f 0 x) = ψ (P.π.f 0 x)) →
      (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
        k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) →
      (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
        k'.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a'.f j x) ⊗ₜ[C] (ψ y)) →
      Nonempty (Homotopy k k')
```

## New

The signatures above remain identical. ModuleCat.augmented_lift_homotopy
and its complete proof move verbatim to
Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy. The quotient theorem
is supplied by WeilConjectures.Algebra.Homology.QuotientTensorResolutionLiftHomotopy,
whose existing complete proof and private helpers stay untouched.
The old Sheaf file is withdrawn through deleted.txt; the delivery tool leaves
an empty module with no declarations. Neither live consumer imports it.
The two existing DAG nodes point at these respective modules; no new node
or proof obligation is introduced. The quotient node's proof now describes
its upstream private induction, rather than a call to the relocated public helper.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SelfTorOrdinaryResolutionSections | unclaimed | Replace its proof import with the upstream twin; theorem signature and proof unchanged. |
| Sheaf.RepresentationTheory.ResolutionInflationComparison | unclaimed | Replace its proof import with AugmentedResolutionLiftHomotopy; all declarations unchanged. |
| Sheaf.AlgebraicGeometry.DerivedSelfTorAffineCoordinates | absent | Listed in the retirement inventory, but no live source file or import remains. Its upstream twin already imports the upstream homotopy module. |
| Sheaf.AlgebraicGeometry.SelfTorAmbientSectionCoordinates | absent | Listed in the inventory; no live source file. Its upstream twin already uses the upstream homotopy module. |
| Sheaf.AlgebraicGeometry.SelfTorNonpositiveFlatSections | absent | Listed in the inventory; no live source file. Its upstream twin already uses the upstream homotopy module. |

| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.GroupTheory.CyclicInflation | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | Indirect consumer only; no textual use of either homotopy theorem; public interfaces unchanged, no edit. |

Source-only downstream.py reports two live direct importers and 13 transitive
consumers. Its --uses scan finds the generic theorem only in the representation
caller and the quotient theorem only in the ordinary-resolution caller. The
other 11 transitive consumers do not mention either declaration; both callers'
public imports, signatures, visibility, and definition bodies are unchanged.
The stale comment in QCohOrdinaryTensorResolutionNaturality refers to the old
location historically; it is not an import or a declaration use.
No statement changes meaning, and no target needs a definition review.

## Status

landed 20261020T135406-L-1818602 2026-10-20 (merge of deliver/G1/Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy)
