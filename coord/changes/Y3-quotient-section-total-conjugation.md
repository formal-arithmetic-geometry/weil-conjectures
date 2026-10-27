# AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_normalized_total

## Reason

The old helper required a fixed counit normalization for an arbitrary tensor isomorphism barB. Changing barB by its negative over coefficients where 1 differs from -1 leaves all old hypotheses unchanged but changes the required equation on a nonzero flat regular degree-zero pair. The helper must use the section conjugate of b. This repairs an intermediate statement; no target signature or definition is changed.

The new proved `section_tensor_conjugate_exists` constructs the required barB by fully faithful precomposition. Its unique preimage is actual categorical data, not a witness selected from an unproved existence theorem. The sole caller chooses this barB and retains its signature.

## Old

```lean
theorem section_tensor_transport_normalized_total (T : Scheme.{u}) (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c) (b : TensorIso a T) (hb : TensorNormalized a T b) (barB : tensor Λ T ⋙ c.model.T ≅ (c.model.T.prod c.model.T) ⋙ tensor Λ' T) (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶ (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj (curriedTensor (modules Λ' T))) (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) (s : (ring Λ' T).obj.obj W), (((e.app M).app N).val.app W) (sectionScalarElement a T c (M ⊗ N) W (sectionPureTensor Λ T M N W m n) s) = sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W (sectionScalarElement a T c M W m 1) (sectionScalarElement a T c N W n s)) : ∀ P Q : CochainComplex (modules Λ T) ℤ, CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) P → CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) Q → (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T) (R := ring Λ T) (P.X i)) → (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T) (R := ring Λ T) (Q.X i)) → ∃ g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj ((totalTensor Λ T).obj (P, Q)) ⟶ (totalTensor Λ' T).obj ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P, (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q), (∀ (i j k : ℤ) (h : i + j = k), c.model.E.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (modules Λ T)) i j k h) ≫ g.f k = (e.app (P.X i)).app (Q.X j) ≫ CochainComplex.ιMapBifunctor ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P) ((c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor (modules Λ' T)) i j k h) ∧ barB.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫ (tensor Λ' T).map (Prod.mkHom (c.model.ε.app P) (c.model.ε.app Q)) ≫ (qTensor Λ' T).app ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P, (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) = c.model.T.map ((qTensor Λ T).app (P, Q)) ≫ c.model.ε.app ((totalTensor Λ T).obj (P, Q)) ≫ DerivedCategory.Q.map g
```

## New

```lean
theorem section_tensor_transport_normalized_total (T : Scheme.{u}) (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c) (b : TensorIso a T) (hb : TensorNormalized a T b) (barB : tensor Λ T ⋙ c.model.T ≅ (c.model.T.prod c.model.T) ⋙ tensor Λ' T) (hbarB : TensorSectionCondition a T c b barB) (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶ (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj (curriedTensor (modules Λ' T))) (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) (s : (ring Λ' T).obj.obj W), (((e.app M).app N).val.app W) (sectionScalarElement a T c (M ⊗ N) W (sectionPureTensor Λ T M N W m n) s) = sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W (sectionScalarElement a T c M W m 1) (sectionScalarElement a T c N W n s)) : ∀ P Q : CochainComplex (modules Λ T) ℤ, CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) P → CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) Q → (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T) (R := ring Λ T) (P.X i)) → (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T) (R := ring Λ T) (Q.X i)) → ∃ g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj ((totalTensor Λ T).obj (P, Q)) ⟶ (totalTensor Λ' T).obj ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P, (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q), (∀ (i j k : ℤ) (h : i + j = k), c.model.E.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (modules Λ T)) i j k h) ≫ g.f k = (e.app (P.X i)).app (Q.X j) ≫ CochainComplex.ιMapBifunctor ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P) ((c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor (modules Λ' T)) i j k h) ∧ barB.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫ (tensor Λ' T).map (Prod.mkHom (c.model.ε.app P) (c.model.ε.app Q)) ≫ (qTensor Λ' T).app ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P, (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) = c.model.T.map ((qTensor Λ T).app (P, Q)) ≫ c.model.ε.app ((totalTensor Λ T).obj (P, Q)) ≫ DerivedCategory.Q.map g
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientSectionTensorTransportNormalizedTotal | Y3 | Own helper requires the compatibility square and is proved from two separate internal path evaluations. |
| Sheaf.Paper.QuotientSectionTensorTransportNormalized | unclaimed | Replace the arbitrary BarB existence import with the proved conjugation constructor and supply hbarB. Signature and public imports stay identical. |

`tools/downstream.py --uses section_tensor_transport_normalized_total` finds only these two modules; a full text search and direct import search agree. No other existing module is edited. The five new modules carry their own nodes. The two evaluation holes are explicit public theorem statements, not data holes.

## Status

landed 20261027T210317-L-1687664 2026-10-27 (merge of deliver/Y3/Sheaf.Paper.QuotientSectionTensorTransportNormalizedTotal)
