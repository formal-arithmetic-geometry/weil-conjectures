# AlgebraicGeometry.Scheme.ProEtaleCoefficientSliceComparison.Normalized

## Reason

The ordinary monoidal and closed portions must be stated in separate modules without importing their consuming theorem. Move the existing data definitions to a publicly reexported data module. Keep their names and types; factor the original conjunction through TensorNormalized with a proposition tail, so its expansion is definitionally the original conjunction. TensorData carries the six ordinary/monoidal fields only. No object is chosen from an existence theorem in a definition.

## Old

```lean
def Normalized (d : Data U O B c delta S SR SB T TR TB) : Prop :=
  -- scalar_equivalence
  ((e U O B c delta).IsEquivalence) ∧
  -- scalar_derived_equivalence
  ((e U O B c delta).mapDerivedCategory.IsEquivalence) ∧
  -- ordinary_section
  (∀ (N : proEtaleRingModules X O) (V : U.left.ProEt)
    (m : N.val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
    (d.ordinary.hom.app N).val.app (op V) (proEtaleSlicePullbackSection U O B c N V m) = m) ∧
  -- restriction_chain
  (∀ (P Q : CochainComplex (proEtaleRingModules X O) ℤ)
    (p q n : ℤ) (h : p + q = n) (V : U.left.ProEt)
    (x : (P.X p).val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V)))
    (y : (Q.X q).val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
    ((d.restrictionTensor.chain P Q).hom.f n).val.app (op V)
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) O
        P Q p q n h (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V)) x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left)
        (proEtaleSliceRing U O) ((proEtaleComparisonComplex (r U O)).obj P)
        ((proEtaleComparisonComplex (r U O)).obj Q) p q n h (op V) x y) ∧
  -- scalar_chain
  (∀ (P Q : CochainComplex (proEtaleRingModules U.left
    (proEtaleSliceRing U O)) ℤ) (p q n : ℤ) (h : p + q = n) (V : U.left.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((d.scalarTensor.chain P Q).hom.f n).val.app V
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left)
        (proEtaleSliceRing U O) P Q p q n h V x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left) B
        ((proEtaleComparisonComplex (e U O B c delta)).obj P)
        ((proEtaleComparisonComplex (e U O B c delta)).obj Q) p q n h V x y) ∧
  -- restriction_unit_section
  (∀ (V : U.left.ProEtᵒᵖ)
    (a : (proEtaleSliceRing U O).obj.obj V), d.restrictionUnit.hom.val.app V a = a) ∧
  -- scalar_unit_section
  (∀ (V : U.left.ProEtᵒᵖ)
    (a : (proEtaleSliceRing U O).obj.obj V),
    d.scalarUnit.hom.val.app V a = (b U O B c delta).hom.hom.app V a) ∧
  -- pullback_unit_section
  (∀ (V : U.left.ProEt)
    (a : (proEtaleSliceRing U O).obj.obj (op V)),
    d.pullbackUnit.hom.val.app (op V)
      (proEtaleSlicePullbackSection U O B c (proEtaleCoefficientUnit X O) V a) =
        (b U O B c delta).hom.hom.app (op V) a) ∧
  -- tensor_compatibility
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    (rho U O B c S SB T TB).hom.app (L, M) ≫
        SB.tensor.map (Prod.mkHom
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app L)
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app M)) =
      (proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
          (S.tensor.obj (L, M)) ≫
        (e U O B c delta).mapDerivedCategory.map (d.restrictionTensor.rho.hom.app (L, M)) ≫
        d.scalarTensor.rho.hom.app
          ((r U O).mapDerivedCategory.obj L, (r U O).mapDerivedCategory.obj M)) ∧
  -- unit_compatibility
  ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (proEtaleCoefficientUnit X O)) ≫
      (e U O B c delta).mapDerivedCategory.map
        (proEtaleDerivedCoefficientUnit (r U O) d.restrictionUnit).hom ≫
      (proEtaleDerivedCoefficientUnit (e U O B c delta) d.scalarUnit).hom =
    (proEtaleDerivedCoefficientUnit (f U O B c) d.pullbackUnit).hom) ∧
  -- restriction_hom_normalization
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.restrictionHom.hom.app (op L, M) = coefficientClosedPullbackMap S SR
      (r U O).mapDerivedCategory d.restrictionTensor.rho L M) ∧
  -- scalar_hom_normalization
  (∀ L M : DerivedCategory
    (proEtaleRingModules U.left (proEtaleSliceRing U O)),
    d.scalarHom.hom.app (op L, M) = coefficientClosedPullbackMap SR SB
      (e U O B c delta).mapDerivedCategory d.scalarTensor.rho L M) ∧
  -- hom_normalization
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.homComparison.hom.app (op L, M) = coefficientClosedPullbackMap S SB
      (f U O B c).mapDerivedCategory (rho U O B c S SB T TB) L M) ∧
  -- hom_transport
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.homComparison.hom.app (op L, M) =
      (proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
          ((proEtaleCoefficientHom X O).obj (op L, M)) ≫
        (e U O B c delta).mapDerivedCategory.map (d.restrictionHom.hom.app (op L, M)) ≫
        d.scalarHom.hom.app
          (op ((r U O).mapDerivedCategory.obj L), (r U O).mapDerivedCategory.obj M) ≫
        (proEtaleCoefficientHom U.left B).map (Prod.mkHom
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app L).op
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).inv.app M)))

```

## New

```lean
def TensorNormalized (d : TensorData U O B c delta S SR SB T TR TB)
    (tail : Prop := True) : Prop :=
  -- ordinary_section
  (∀ (N : proEtaleRingModules X O) (V : U.left.ProEt)
    (m : N.val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
    (d.ordinary.hom.app N).val.app (op V) (proEtaleSlicePullbackSection U O B c N V m) = m) ∧
  -- restriction_chain
  (∀ (P Q : CochainComplex (proEtaleRingModules X O) ℤ)
    (p q n : ℤ) (h : p + q = n) (V : U.left.ProEt)
    (x : (P.X p).val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V)))
    (y : (Q.X q).val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
    ((d.restrictionTensor.chain P Q).hom.f n).val.app (op V)
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) O
        P Q p q n h (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V)) x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left)
        (proEtaleSliceRing U O) ((proEtaleComparisonComplex (r U O)).obj P)
        ((proEtaleComparisonComplex (r U O)).obj Q) p q n h (op V) x y) ∧
  -- scalar_chain
  (∀ (P Q : CochainComplex (proEtaleRingModules U.left
    (proEtaleSliceRing U O)) ℤ) (p q n : ℤ) (h : p + q = n) (V : U.left.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((d.scalarTensor.chain P Q).hom.f n).val.app V
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left)
        (proEtaleSliceRing U O) P Q p q n h V x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left) B
        ((proEtaleComparisonComplex (e U O B c delta)).obj P)
        ((proEtaleComparisonComplex (e U O B c delta)).obj Q) p q n h V x y) ∧
  -- restriction_unit_section
  (∀ (V : U.left.ProEtᵒᵖ)
    (a : (proEtaleSliceRing U O).obj.obj V), d.restrictionUnit.hom.val.app V a = a) ∧
  -- scalar_unit_section
  (∀ (V : U.left.ProEtᵒᵖ)
    (a : (proEtaleSliceRing U O).obj.obj V),
    d.scalarUnit.hom.val.app V a = (b U O B c delta).hom.hom.app V a) ∧
  -- pullback_unit_section
  (∀ (V : U.left.ProEt)
    (a : (proEtaleSliceRing U O).obj.obj (op V)),
    d.pullbackUnit.hom.val.app (op V)
      (proEtaleSlicePullbackSection U O B c (proEtaleCoefficientUnit X O) V a) =
        (b U O B c delta).hom.hom.app (op V) a) ∧
  -- tensor_compatibility
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    (rho U O B c S SB T TB).hom.app (L, M) ≫
        SB.tensor.map (Prod.mkHom
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app L)
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app M)) =
      (proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
          (S.tensor.obj (L, M)) ≫
        (e U O B c delta).mapDerivedCategory.map (d.restrictionTensor.rho.hom.app (L, M)) ≫
        d.scalarTensor.rho.hom.app
          ((r U O).mapDerivedCategory.obj L, (r U O).mapDerivedCategory.obj M)) ∧
  -- unit_compatibility
  ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (proEtaleCoefficientUnit X O)) ≫
      (e U O B c delta).mapDerivedCategory.map
        (proEtaleDerivedCoefficientUnit (r U O) d.restrictionUnit).hom ≫
      (proEtaleDerivedCoefficientUnit (e U O B c delta) d.scalarUnit).hom =
    (proEtaleDerivedCoefficientUnit (f U O B c) d.pullbackUnit).hom) ∧ tail

/-- The section, tensor, unit and closed normalizations of the comparison data.
These are the equations in the node, factored out of the data record so Lean does
not expand them in every generated projection and constructor.
Source: Hemo--Richarz--Scholbach Lemma 4.5; Stacks 03CE, 07A4, 08J9 and 08JB
(blueprint: lem-zl-proetale-coefficient-slice-closed-comparison). -/
def Normalized (d : Data U O B c delta S SR SB T TR TB) : Prop :=
  -- scalar_equivalence
  ((e U O B c delta).IsEquivalence) ∧
  -- scalar_derived_equivalence
  ((e U O B c delta).mapDerivedCategory.IsEquivalence) ∧
  TensorNormalized U O B c delta S SR SB T TR TB d.tensorData (
  -- restriction_hom_normalization
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.restrictionHom.hom.app (op L, M) = coefficientClosedPullbackMap S SR
      (r U O).mapDerivedCategory d.restrictionTensor.rho L M) ∧
  -- scalar_hom_normalization
  (∀ L M : DerivedCategory
    (proEtaleRingModules U.left (proEtaleSliceRing U O)),
    d.scalarHom.hom.app (op L, M) = coefficientClosedPullbackMap SR SB
      (e U O B c delta).mapDerivedCategory d.scalarTensor.rho L M) ∧
  -- hom_normalization
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.homComparison.hom.app (op L, M) = coefficientClosedPullbackMap S SB
      (f U O B c).mapDerivedCategory (rho U O B c S SB T TB) L M) ∧
  -- hom_transport
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.homComparison.hom.app (op L, M) =
      (proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
          ((proEtaleCoefficientHom X O).obj (op L, M)) ≫
        (e U O B c delta).mapDerivedCategory.map (d.restrictionHom.hom.app (op L, M)) ≫
        d.scalarHom.hom.app
          (op ((r U O).mapDerivedCategory.obj L), (r U O).mapDerivedCategory.obj M) ≫
        (proEtaleCoefficientHom U.left B).map (Prod.mkHom
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app L).op
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).inv.app M))))

```

All other moved definitions retain their original bodies and public visibility. The exactness proof now applies the existing public proEtaleSliceModules_exact from a proof-only import of Sheaf.AlgebraicGeometry.ProEtaleScalarExtensionSliceComparison. Its functor is definitionally the displayed restriction functor, so the signature is unchanged. The duplicate private exact_moduleRestriction is removed, repairing the return on ad094857678. No other module needs an adaptation for this proof change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientSliceClosedComparison | R6 | Publicly reexports moved definitions; same theorem signature and expanded normalization. |

The downstream query reports no current Lean importers. DAG parents, including lem-zl-condensed-lisse-proetale-locality, retain the unchanged theorem. The definition conveys the same mathematical statement, so no target changes meaning. New modules ProEtaleSliceOrdinaryComparison, ProEtaleSliceMonoidalDescent and ProEtaleSliceClosedMates import the factored data interface.

## Status

landed 20261024T190843-L-114045 2026-10-24 (merge of deliver/R6/Sheaf.AlgebraicGeometry.ProEtaleCoefficientSliceClosedComparison)
