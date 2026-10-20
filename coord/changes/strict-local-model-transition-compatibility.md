# AlgebraicGeometry.Scheme.exists_strictLocal_algebraicResidue_models

## Reason

The item needs a diagram over Spec L. The model interface supplied each p_i separately,
without its transition equation. The existing construction uses L-subalgebra inclusions,
so the omitted equation follows by extensionality, with no new assumption or proof hole.
The adapted module was unclaimed when inspected. No target signature or definition changes.

## Old

```lean
theorem exists_strictLocal_algebraicResidue_models {K : Type u} [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) : ∃ U : Y.Opens, s (IsLocalRing.closedPoint Ω) ∈ U ∧ IsAffineOpen U ∧ ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsSepClosed L), Algebra.trdeg K L = @Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω))) _ _ (((Y ↘ Spec (.of K)).residueFieldAlgebraMap (s (IsLocalRing.closedPoint Ω))).toAlgebra) ∧ ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Over U.toScheme) (p : ∀ i : I, (D.obj i).left ⟶ Spec (.of L)) (c : Cone D) (e : strictHenselizationScheme s ≅ c.pt.left), Nonempty (IsLimit c) ∧ e.hom ≫ c.pt.hom ≫ U.ι = strictHenselizationStructuralMap s ∧ (∀ i : I, Nonempty (D.obj i).left ∧ IsAffine (D.obj i).left ∧ LocallyOfFiniteType (p i) ∧ QuasiCompact (p i) ∧ (D.obj i).hom ≫ U.ι ≫ (Y ↘ Spec (.of K)) = p i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ (∀ (i j : I) (a : i ⟶ j), IsAffineHom (D.map a).left) ∧ ∀ (i : I) (v : (D.obj i).left), @Algebra.IsAlgebraic (U.toScheme.residueField ((D.obj i).hom v)) ((D.obj i).left.residueField v) _ _ (((D.obj i).hom.residueFieldMap v).hom.toAlgebra)
```

## New

```lean
theorem exists_strictLocal_algebraicResidue_models {K : Type u} [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) : ∃ U : Y.Opens, s (IsLocalRing.closedPoint Ω) ∈ U ∧ IsAffineOpen U ∧ ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsSepClosed L), Algebra.trdeg K L = @Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω))) _ _ (((Y ↘ Spec (.of K)).residueFieldAlgebraMap (s (IsLocalRing.closedPoint Ω))).toAlgebra) ∧ ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Over U.toScheme) (p : ∀ i : I, (D.obj i).left ⟶ Spec (.of L)) (c : Cone D) (e : strictHenselizationScheme s ≅ c.pt.left), Nonempty (IsLimit c) ∧ e.hom ≫ c.pt.hom ≫ U.ι = strictHenselizationStructuralMap s ∧ (∀ i : I, Nonempty (D.obj i).left ∧ IsAffine (D.obj i).left ∧ LocallyOfFiniteType (p i) ∧ QuasiCompact (p i) ∧ (D.obj i).hom ≫ U.ι ≫ (Y ↘ Spec (.of K)) = p i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ (∀ (i j : I) (a : i ⟶ j), IsAffineHom (D.map a).left) ∧ (∀ (i : I) (v : (D.obj i).left), @Algebra.IsAlgebraic (U.toScheme.residueField ((D.obj i).hom v)) ((D.obj i).left.residueField v) _ _ (((D.obj i).hom.residueFieldMap v).hom.toAlgebra)) ∧ (∀ (i j : I) (a : i ⟶ j), (D.map a).left ≫ p j = p i)
```

The only extra public clause is `(∀ (i j : I) (a : i ⟶ j), (D.map a).left ≫ p j = p i)`.
The private `exists_models_of_subalgebras` exposes the same clause; spectrum functoriality
and extensionality prove it for the existing inclusions. The main proof forwards that clause.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels --uses
exists_strictLocal_algebraicResidue_models` found the ten downstream modules below and
no existing external call to the theorem. Only the new item proof consumes it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange | claimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | claimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | claimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | claimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | claimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationLimit | claimed | Consumes the added compatibility; proved in this delivery. |
| Sheaf.Paper.FiniteAffineDirectImageSupportBound | unclaimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.Targets.BaseChangeTowardsFields | claimed | No call to the changed theorem; imports remain compatible; statement unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels | unclaimed | Exposes and proves compatibility; private assembly helper gains the same clause. |

Both DAG citers retain their intended uses: `lem-kun-0f0u` builds its L-diagram;
`lem-kun-affine-direct-image-support-bound` retains its coefficient-model argument.
The target's statement and the unit's route stay unchanged. The zero-transcendence-degree
case of the model theorem still works: every inclusion fixes each scalar, also for b=0.

## Status

landed 20261020T122128-L-482397 2026-10-20 (merge of deliver/R2/Sheaf.AlgebraicGeometry.StrictHenselizationLimit)
