# AlgebraicGeometry.Scheme.UniformAdicTowerData and reconstruction stratifications

## Reason

The current rework archive is
`quarantine/Sheaf/Paper/ReconstructionUniformTower.lean`, recorded in `coord/rework.tsv`.
Its reported error is `Unknown identifier LocallyClosedStratification`.
The working file initially read in this session already had the spelling repaired
and eight auxiliary holes closed. This delivery retains those proofs, proves the
adjacent ordinary reduction map and restores the full module.

The imported module `WeilConjectures.AlgebraicGeometry.LocallyClosedStratification`
provides `AlgebraicGeometry.Scheme.Stratification` via
`WeilConjectures.ConstructibleSheaf.Defs`. `BoundedConstructibleTower` already uses it.

## Old

The three declarations below are copied verbatim from the archive, with the proof
body omitted from the theorem signature. Their section variables are unchanged.

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

Only the three stratification parameter names change. Every data field and every
conclusion clause is preserved verbatim.

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

The current type additionally records constructibility of the strata. On the
finite-type-over-a-field schemes in the reconstruction theorem, the scheme is
Noetherian, so every locally closed subset is constructible
(`Stratification.ofNoetherianSpace`). Thus all intended finite locally closed
stratifications in that theorem are admitted. No conclusion is weakened.
The theorem is not a target of `Challenge.lean`.

The adjacent ordinary reduction map is proved using its normalized scalar adjunction
and pure-tensor extensionality. Eight auxiliary proofs from the initial working
source are restored. Two original named proof obligations remain.
All public imports and all other existing signatures and definition data are retained.
No adopted source-library declaration is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ReconstructionUniformTower | M4 | Restore the module and consistently use the imported Stratification type in its three declarations. |

No other current file under `lean/Sheaf` or `lean/WeilConjectures` imports this
quarantined module or names the repaired declarations. The same search under
`quarantine/Sheaf` and `quarantine/WeilConjectures` found only this module itself.
The read-only downstream check is
`python3 tools/downstream.py Sheaf.Paper.ReconstructionUniformTower --allow-missing --uses AlgebraicGeometry.Scheme.UniformAdicTowerData AlgebraicGeometry.Scheme.UniformReconstructionFamily AlgebraicGeometry.Scheme.reconstructionUniformTower`.
The check returned zero downstream modules and zero current users of each of the
three declarations. No other group's module is adapted. The DAG attachment is preserved and its recorded
Lean statement uses the current name. Both remaining obligations retain their full
statements and natural-language proof plans.

## Status

landed 20261021T001131-L-1375347 2026-10-21 (merge of deliver/M4/Sheaf.Paper.ReconstructionUniformTower)

Implemented in the sandbox and verified by the complete single-file `lcompile.py`
check (57.8 seconds). Submitted for independent review with this stage-3 delivery.
The listed restoration/identifier repair is complete. Mathematical reconstruction
still has the two named holes listed in report.md; no new holes are introduced.
