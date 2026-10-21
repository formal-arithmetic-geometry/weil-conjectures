# completedAdicScalar_exists

## Reason

Restoring ResidueLissePerfectLift requires the missing finite-quotient induction.
That induction's existing compatibility proof uses completedAdicScalar_exists.
Complete this canonical scalar-map obligation from the coefficient limit and
sheafification universal properties. The module is unclaimed. This fills one
existing named proof hole; it changes no signature, definition or import, and
requires no consumer adaptation. It also offsets the archived successor hole
that the dependency restoration must retain.

## Old

```lean
theorem completedAdicScalar_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    ∃! α : adicConstantRing T A ⟶ completedAdicCommRing T d,
      ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (a : ULift.{t + 1} A),
        (completedAdicProjection T d n).hom.app U
          (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α).hom.app U
            ((koszulConstantUnit T A).app U a)) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down)) := by
  sorry
```

## New

```lean
theorem completedAdicScalar_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    ∃! α : adicConstantRing T A ⟶ completedAdicCommRing T d,
      ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (a : ULift.{t + 1} A),
        (completedAdicProjection T d n).hom.app U
          (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α).hom.app U
            ((koszulConstantUnit T A).app U a)) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down)) := by
  let J := ProEt.topology T
  let F := (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} A))
  let D := completedAdicRingSystem T d
  let E := sheafToPresheaf J RingCat.{t + 1}
  let q (n : ℕ) : ULift.{t + 1} A →+* completedAdicQuotient d n :=
    RingHom.ulift (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let σ (n : ℕ) : F ⟶ (completedAdicFiniteRing T d n).obj :=
    (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom (q n)) ≫
      ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)
  have hσ (n : ℕ) : σ (n + 1) ≫ (completedAdicFiniteStep T d n).hom = σ n := by
    ext U a
    have hs := congrArg
      (fun k ↦ (k.app U).hom
        ((ProEtale.finiteCoefficientConstants T
          (completedAdicQuotient d (n + 1))).app U (q (n + 1) a)))
      (toSheafify_naturality J (completedAdicFinitePresheafStep T d n))
    have hc : (completedAdicFinitePresheafStep T d n).app U
        ((ProEtale.finiteCoefficientConstants T
          (completedAdicQuotient d (n + 1))).app U (q (n + 1) a)) =
      (ProEtale.finiteCoefficientConstants T
        (completedAdicQuotient d n)).app U (q n a) := by
      apply ContinuousMap.ext
      intro x
      rfl
    simp only [NatTrans.comp_app, RingCat.comp_apply] at hs
    rw [hc] at hs
    exact hs.symm
  let c : Cone (D ⋙ E) :=
    { pt := F
      π := NatTrans.ofOpSequence σ (fun n ↦ by
        dsimp only [Functor.const_obj_map, Functor.comp_map, D, E,
          completedAdicRingSystem]
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        change 𝟙 F ≫ σ n = σ (n + 1) ≫ (completedAdicFiniteStep T d n).hom
        simpa only [Category.id_comp] using (hσ n).symm) }
  let L := isLimitOfPreserves E (limit.isLimit D)
  let β : F ⟶ (completedAdicRing T d).obj := L.lift c
  let F' := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} A))
  let β' : F' ⟶ (completedAdicCommRing T d).obj :=
    { app := fun U ↦
        letI := completedAdicCommRingStructure T d U
        CommRingCat.ofHom (β.app U).hom
      naturality := fun U V f ↦ (forget₂ CommRingCat RingCat).map_injective
        (β.naturality f) }
  let α : adicConstantRing T A ⟶ completedAdicCommRing T d :=
    ((sheafificationAdjunction J CommRingCat.{t + 1}).homEquiv F'
      (completedAdicCommRing T d)).symm β'
  have hα : toSheafify J F' ≫ α.hom = β' :=
    ((sheafificationAdjunction J CommRingCat.{t + 1}).homEquiv F'
      (completedAdicCommRing T d)).apply_symm_apply β'
  have hnorm (n : ℕ) (U : T.ProEtᵒᵖ) (a : ULift.{t + 1} A) :
      (completedAdicProjection T d n).hom.app U
        (((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α).hom.app U
          ((koszulConstantUnit T A).app U a)) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (q n a) := by
    have ha := congrArg (fun k : F' ⟶ (completedAdicCommRing T d).obj ↦
      (k.app U).hom a) hα
    change (α.hom.app U).hom ((toSheafify J F').app U a) = (β.app U).hom a at ha
    change (completedAdicProjection T d n).hom.app U
      ((α.hom.app U).hom ((toSheafify J F').app U a)) = _
    rw [ha]
    exact congrArg (fun k : F ⟶ (completedAdicFiniteRing T d n).obj ↦
      (k.app U).hom a) (L.fac c (op n))
  refine ⟨α, hnorm, ?_⟩
  intro ψ hψ
  have htest : toSheafify J F' ≫ ψ.hom = β' := by
    apply ((Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat RingCat).obj
      (forget₂ CommRingCat RingCat)).map_injective
    change Functor.whiskerRight (toSheafify J F' ≫ ψ.hom)
      (forget₂ CommRingCat RingCat) = β
    apply L.hom_ext
    intro j
    rw [L.fac c j]
    ext U a
    exact hψ j.unop U a
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicCommRing T d).property
  exact htest.trans hα.symm
```

The proof follows the declaration's original proof in words. Constant residue maps
commute with quotient transitions by sheafification naturality. They give a cone,
whose unique limit map promotes to commutative rings. Sheafification extends this
presheaf map. Equality is tested on constant sections and all limit projections.
No choices beyond the limit and sheafification universal properties are introduced.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedAdicIntrinsicCompletion | unclaimed | Complete the scalar-map existence and uniqueness proof; all signatures and definitions unchanged. |
| Sheaf.Paper.FinitePerfectQuotientModels | unclaimed | Uses the scalar-map normalization in its compatibility proof; no change forced by this proof replacement. |
| Sheaf.Paper.ResidueLissePerfectLift | D4 | Restored item depends on the canonical scalar map through the same unchanged interface. |

The downstream.py --uses scan lists the intrinsic-completion module and the
finite-quotient module as the two current source users. The restored item is
included as an adapted module. All eighteen transitive importers retain the same
public interfaces, with no source edits needed.

## Status

landed 20261021T001116-L-1371846 2026-10-21 (merge of deliver/D4/Sheaf.Paper.ResidueLissePerfectLift)
