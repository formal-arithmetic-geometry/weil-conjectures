# B7 reconstruction uniform tower stratification API restoration

## Reason

The assigned rework source is quarantined at
`quarantine/Sheaf/Paper/ReconstructionUniformTower.lean`. Its old
`LocallyClosedStratification` name was removed by the adopted source update.
The current `BoundedConstructibleTower` module uses `Scheme.Stratification`.
Restore the archived module and use that same existing type in its three signatures.
The new type retains the domains, immersions, finite partition and locally closedness,
and records constructibility of strata, as the current constructible-tower definition
requires. On the finite-type-over-a-field schemes of the reconstruction theorem,
locally closed strata are constructible by Noetherianity. No target statement is edited.

## Old

```lean
structure UniformAdicTowerData (M : AdicTower X d)
    (strata : LocallyClosedStratification X) where
  lower : ℤ
  upper : ℤ
  bounds : lower ≤ upper
  cover : ∀ α : Fin strata.n, Sieve (⊤_ (strata.domain α).ProEt)
  covering : ∀ α : Fin strata.n,
    cover α ∈ ProEt.topology (strata.domain α) (⊤_ (strata.domain α).ProEt)
  model : ∀ (α : Fin strata.n) (U : (strata.domain α).ProEt)
    (f : U ⟶ ⊤_ (strata.domain α).ProEt), cover α f →
      AdicTowerLocalModel d (U.hom ≫ strata.immersion α) M lower upper


abbrev UniformReconstructionFamily (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (S : LocallyClosedStratification X) :=
  ∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S)
    (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
    (hf : W.cover α f)
    (_E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf)),
    DerivedCategory.Q.obj (W.model α U f hf).complex ≅
      (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d)).obj
        (uniformReconstructionLimit d M)


theorem reconstructionUniformTower {k : Type u} [Field k] (X : Scheme.{u})
    (fX : X ⟶ Spec (.of k)) (_hX : LocallyOfFiniteType fX ∧ QuasiCompact fX)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (S : LocallyClosedStratification X) :
    ∃ φ : UniformReconstructionFamily X d S,
      (∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S)
        (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
        (hf : W.cover α f),
        Nonempty (UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf)) ∧
          ∀ E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf),
            ∀ n : ℕ,
              (φ M W α U f hf E).hom ≫
                  CategoryTheory.Functor.map
                    (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d))
                    (uniformTowerProjection X (pbcAdicCompletion X d) M.tower n) ≫
                  (uniformPullEvaluation (U.hom ≫ S.immersion α) d n).inv.app M.tower =
                uniformLocalUnit (U.hom ≫ S.immersion α) d (W.model α U f hf).complex n ≫
                  (pbcTowerEvaluation U.left
                    (uniformLocalRing (U.hom ≫ S.immersion α) d) n).map E.comparison.inv) ∧
      (∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S),
        (∀ (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
          (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
          (e : DerivedCategory.Q.obj C ≅ uniformReconstructionLimit d M),
          IsDerivedCompleteIntrinsic X d r a ha (uniformReconstructionLimit d M) C e) ∧
        (∀ n : ℕ, IsIso (uniformReconstructionCounit d M n)) ∧
        (∀ (b a : ℕ) (hab : a ≤ b),
          (pbcDerivedExtend (pbcAdicQuotient X d b a hab)).map
              (uniformReconstructionCounit d M b) ≫ (M.normalization b a hab).hom =
            (pbcReductionNormalization (pbcAdicProjection X d b)
              (pbcAdicQuotient X d b a hab) (pbcAdicProjection X d a)
              (pbcAdicProjection_comp X d b a hab)
              (uniformReconstructionLimit d M)).hom ≫ uniformReconstructionCounit d M a) ∧
        ∀ q : ℤ, q < W.lower ∨ W.upper < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj (uniformReconstructionLimit d M))) ∧
      (∀ (M N : AdicTower X d) (W : UniformAdicTowerData d M S)
        (V : UniformAdicTowerData d N S) (α : Fin S.n) (U : (S.domain α).ProEt)
        (f : U ⟶ ⊤_ (S.domain α).ProEt) (hf : W.cover α f) (hf' : V.cover α f)
        (E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf))
        (E' : UniformLocalEquipment (U.hom ≫ S.immersion α) d N (V.model α U f hf'))
        (v : M.tower ⟶ N.tower)
        (h : DerivedCategory.Q.obj (W.model α U f hf).complex ⟶
          DerivedCategory.Q.obj (V.model α U f hf').complex),
        (uniformTowerPull (U.hom ≫ S.immersion α) d).map v ≫ E'.comparison.hom =
          E.comparison.hom ≫
            (localReductionDerived U.left (uniformLocalRing (U.hom ≫ S.immersion α) d)
              (uniformLocalRings (U.hom ≫ S.immersion α) d)
              (uniformLocalProjections (U.hom ≫ S.immersion α) d)).map h →
        h ≫ (φ N V α U f hf' E').hom = (φ M W α U f hf E).hom ≫
          (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d)).map
            ((uniformTowerRlim X (pbcAdicCompletion X d)).map v))
```

## New

```lean
structure UniformAdicTowerData (M : AdicTower X d)
    (strata : Stratification X) where
  lower : ℤ
  upper : ℤ
  bounds : lower ≤ upper
  cover : ∀ α : Fin strata.n, Sieve (⊤_ (strata.domain α).ProEt)
  covering : ∀ α : Fin strata.n,
    cover α ∈ ProEt.topology (strata.domain α) (⊤_ (strata.domain α).ProEt)
  model : ∀ (α : Fin strata.n) (U : (strata.domain α).ProEt)
    (f : U ⟶ ⊤_ (strata.domain α).ProEt), cover α f →
      AdicTowerLocalModel d (U.hom ≫ strata.immersion α) M lower upper


abbrev UniformReconstructionFamily (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (S : Stratification X) :=
  ∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S)
    (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
    (hf : W.cover α f)
    (_E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf)),
    DerivedCategory.Q.obj (W.model α U f hf).complex ≅
      (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d)).obj
        (uniformReconstructionLimit d M)


theorem reconstructionUniformTower {k : Type u} [Field k] (X : Scheme.{u})
    (fX : X ⟶ Spec (.of k)) (_hX : LocallyOfFiniteType fX ∧ QuasiCompact fX)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (S : Stratification X) :
    ∃ φ : UniformReconstructionFamily X d S,
      (∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S)
        (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
        (hf : W.cover α f),
        Nonempty (UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf)) ∧
          ∀ E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf),
            ∀ n : ℕ,
              (φ M W α U f hf E).hom ≫
                  CategoryTheory.Functor.map
                    (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d))
                    (uniformTowerProjection X (pbcAdicCompletion X d) M.tower n) ≫
                  (uniformPullEvaluation (U.hom ≫ S.immersion α) d n).inv.app M.tower =
                uniformLocalUnit (U.hom ≫ S.immersion α) d (W.model α U f hf).complex n ≫
                  (pbcTowerEvaluation U.left
                    (uniformLocalRing (U.hom ≫ S.immersion α) d) n).map E.comparison.inv) ∧
      (∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S),
        (∀ (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
          (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
          (e : DerivedCategory.Q.obj C ≅ uniformReconstructionLimit d M),
          IsDerivedCompleteIntrinsic X d r a ha (uniformReconstructionLimit d M) C e) ∧
        (∀ n : ℕ, IsIso (uniformReconstructionCounit d M n)) ∧
        (∀ (b a : ℕ) (hab : a ≤ b),
          (pbcDerivedExtend (pbcAdicQuotient X d b a hab)).map
              (uniformReconstructionCounit d M b) ≫ (M.normalization b a hab).hom =
            (pbcReductionNormalization (pbcAdicProjection X d b)
              (pbcAdicQuotient X d b a hab) (pbcAdicProjection X d a)
              (pbcAdicProjection_comp X d b a hab)
              (uniformReconstructionLimit d M)).hom ≫ uniformReconstructionCounit d M a) ∧
        ∀ q : ℤ, q < W.lower ∨ W.upper < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj (uniformReconstructionLimit d M))) ∧
      (∀ (M N : AdicTower X d) (W : UniformAdicTowerData d M S)
        (V : UniformAdicTowerData d N S) (α : Fin S.n) (U : (S.domain α).ProEt)
        (f : U ⟶ ⊤_ (S.domain α).ProEt) (hf : W.cover α f) (hf' : V.cover α f)
        (E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf))
        (E' : UniformLocalEquipment (U.hom ≫ S.immersion α) d N (V.model α U f hf'))
        (v : M.tower ⟶ N.tower)
        (h : DerivedCategory.Q.obj (W.model α U f hf).complex ⟶
          DerivedCategory.Q.obj (V.model α U f hf').complex),
        (uniformTowerPull (U.hom ≫ S.immersion α) d).map v ≫ E'.comparison.hom =
          E.comparison.hom ≫
            (localReductionDerived U.left (uniformLocalRing (U.hom ≫ S.immersion α) d)
              (uniformLocalRings (U.hom ≫ S.immersion α) d)
              (uniformLocalProjections (U.hom ≫ S.immersion α) d)).map h →
        h ≫ (φ N V α U f hf' E').hom = (φ M W α U f hf E).hom ≫
          (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d)).map
            ((uniformTowerRlim X (pbcAdicCompletion X d)).map v))
```

The file also has proof-only imports and elaborator transparency settings supporting
its proved auxiliary lemmas. These settings guide elaboration without changing any
mathematical definition. All existing construction bodies are retained. No arbitrary
witness construction was added.

## Users

`tools/downstream.py Sheaf.Paper.ReconstructionUniformTower --uses UniformAdicTowerData`
reports `unknown module(s)` because the item is quarantined. A direct search of both
`lean/` and `quarantine/` finds no external Lean occurrence or importer of this module
or of either uniform-data family name. The rework queue also records zero quarantined
importers waiting. This is restoration, not withdrawal: the existing node attachment and
all its dependencies remain.

The DAG still has unfinished parents citing the reconstruction node. They retain it:
`thm-sf-pf-adic`, `rem-trf-classical-framework`,
`lem-pur-condensed-tate-integral-tower`, and
`thm-pod-adic-reconstruction-and-scalar-extension`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ReconstructionUniformTower | B7 | Restored; obsolete stratification name migrated. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | not adapted | DAG parent only; no Lean reference to the repaired signatures. |

## Status

landed 20261020T221053-L-4140591 2026-10-20 (merge of deliver/B7/Sheaf.Paper.ReconstructionUniformTower)
