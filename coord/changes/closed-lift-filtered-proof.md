# Algebra.ClosedLift.isFiltered_index

## Reason

The delivery fills the proof of an existing proposition-valued instance. The static interface
scanner compares instance bodies and therefore requires this record even though the elaborated
type, instance name, priority and visibility stay identical. It also records the new
`open scoped TensorProduct` command, which enables notation used inside this file's proofs.
No public definition, public theorem signature, statement hypothesis or conclusion changes.
All new helpers are private and all added imports are proof-only.

## Old

```lean
instance isFiltered_index : IsFiltered (Index A C) :=
  sorry
```

## New

```lean
instance isFiltered_index : IsFiltered (Index A C) := by
  exact {
    nonempty := by
      obtain ⟨X, _, _⟩ := exists_index A C A (Algebra.ofId A C)
      exact ⟨X⟩
    cocone_objs X Y := by
      let q : X.alg ⊗[A] Y.alg →ₐ[A] C :=
        Algebra.TensorProduct.productMap X.toC Y.toC
      have : Algebra.Etale A (X.alg ⊗[A] Y.alg) :=
        Algebra.Etale.comp A X.alg _
      obtain ⟨Z, e, he⟩ := exists_index A C _ q
      refine ⟨Z, ⟨e.symm.toAlgHom.comp Algebra.TensorProduct.includeLeft, ?_⟩,
        ⟨e.symm.toAlgHom.comp Algebra.TensorProduct.includeRight, ?_⟩, trivial⟩
      · ext x
        simp [he, q]
      · ext y
        simp [he, q]
    cocone_maps {X Y} f g := by
      let h : X.alg ⊗[A] X.alg →ₐ[A] Y.alg :=
        Algebra.TensorProduct.productMap f.hom g.hom
      let K := KaehlerDifferential.ideal A X.alg
      let J : Ideal Y.alg := K.map h.toRingHom
      have hK : IsIdempotentElem K :=
        (Ideal.cotangent_subsingleton_iff K).mp
          (inferInstanceAs (Subsingleton Ω[X.alg⁄A]))
      have hJ : IsIdempotentElem J := by
        change J * J = J
        rw [← Ideal.map_mul, hK]
      have hJfg : J.FG := (KaehlerDifferential.ideal_fg A X.alg).map _
      have : Algebra.FinitePresentation Y.alg (Y.alg ⧸ J) :=
        Algebra.FinitePresentation.quotient hJfg
      have : Algebra.FormallyEtale Y.alg (Y.alg ⧸ J) := by
        apply (Algebra.FormallyEtale.iff_of_surjective
          (Ideal.Quotient.mk_surjective (I := J))).mpr
        simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hJ
      have : Algebra.Etale Y.alg (Y.alg ⧸ J) := ⟨inferInstance, inferInstance⟩
      have : Algebra.Etale A (Y.alg ⧸ J) := Algebra.Etale.comp A Y.alg _
      have hcomp : Y.toC.comp h = X.toC.comp (Algebra.TensorProduct.lmul' A) := by
        apply Algebra.TensorProduct.ext
        · ext x
          simpa [h] using DFunLike.congr_fun f.comp_toC x
        · ext x
          simpa [h] using DFunLike.congr_fun g.comp_toC x
      have hker : J ≤ RingHom.ker Y.toC.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        change Y.toC (h x) = 0
        rw [← AlgHom.comp_apply, hcomp, AlgHom.comp_apply]
        change Algebra.TensorProduct.lmul' A x = 0 at hx
        rw [hx, map_zero]
      let q : (Y.alg ⧸ J) →ₐ[A] C := Ideal.Quotient.liftₐ J Y.toC hker
      obtain ⟨Z, e, he⟩ := exists_index A C _ q
      let a : Y ⟶ Z := ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A J), by
        ext y
        simp [he, q]⟩
      refine ⟨Z, a, ?_⟩
      apply Index.Hom.ext
      apply AlgHom.ext
      intro x
      change e.symm (Ideal.Quotient.mk J (f.hom x)) =
        e.symm (Ideal.Quotient.mk J (g.hom x))
      congr 1
      apply Ideal.Quotient.eq.mpr
      have hx : x ⊗ₜ[A] (1 : X.alg) - (1 : X.alg) ⊗ₜ[A] x ∈ K := by
        change Algebra.TensorProduct.lmul' A _ = 0
        simp
      have hm := Ideal.mem_map_of_mem h.toRingHom hx
      simpa [h, J] using hm
 }
```

The additional local notation command is `open scoped TensorProduct`.

## Users

`tools/downstream.py WeilConjectures.RingTheory.ProEtale.ClosedLift --uses
Algebra.ClosedLift.isFiltered_index` reports 28 downstream modules and no downstream textual
reference to this declaration name. Typeclass users receive the identical proposition-valued
instance; proof irrelevance makes the new proof interchangeable with the old proof. Listed
for completeness, including downstream importers whose statements do not mention the instance:

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation | D4 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | E1 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties | E1 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction | G1 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift | G1 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | D2 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | B4 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections | D2 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | D3 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.RingTheory.ProEtale.ClosedLiftAdjunction | E3 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.RingTheory.ProEtale.ClosedLiftMap | E3 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.RingTheory.ProEtale.ClosedLiftUnits | F2 | Same IsFiltered proposition and instance name; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Same IsFiltered proposition and instance name; no adaptation. |
| TargetsCheck | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| WeilConjectures | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| WeilConjectures.AlgebraicGeometry.ProEtale.ClosedCoverExtension | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| WeilConjectures.RingTheory.ProEtale.ClosedLift | E3 | Same IsFiltered proposition and instance name; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same IsFiltered proposition and instance name; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | Same IsFiltered proposition and instance name; no adaptation. |

No target statement or definition used by a target changes meaning; no target statement
review is reopened by this proof-only change.

## Status

landed 20261015T182203-L-785410 2026-10-15 (merge of deliver/E3/WeilConjectures.RingTheory.ProEtale.ClosedLift)
