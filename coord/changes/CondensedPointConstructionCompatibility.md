# AlgebraicGeometry.ProEtale.condensed_point_realization_exists

## Reason

STATEMENT-DISPUTED: the old component split quantified over independent choices which
must be constructed compatibly. Negating a tensor isomorphism preserves invertibility
but negates its required nonzero unit-basis entry. Rescaling all modelIso maps by c
preserves chain-map descent but scales the tensor-descent sides by c and c squared.
A coefficient-field automorphism gives an exact strong symmetric monoidal realization
whose unit scalar a has trace sigma(a), contradicting the old arbitrary-R matrix and
trace formulas for the independently fixed injective epsilon.

Choose the realization, scalars, based models, their identifications and normalized
tensor comparisons in one existential telescope. The false matrix and tensor-law
helpers and the redundant separate tensor-model helper are withdrawn. The scalar
existence theorem is proved by copying fields, which do not use rho. The duality
existence theorem takes the missing compatible-matrix hypothesis, supplied by the
joint construction. The parent condensed_point_supertrace statement is unchanged.
There remain three explicitly named admitted construction theorems; the removed false
obligations are not claimed as proofs.

The matrix class gains a proved frame-membership default. Named differential-matrix,
chain-map-matrix and transported-trace propositions expand to the exact former field
types. This compacts generated recursors without changing any condition. No hollow
object is defined. No data are selected in a definition from an admitted theorem.

## Old

```lean
theorem condensed_point_realization_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    Nonempty (CondensedPointRealizationData k l E)

theorem condensed_point_matrix_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] :
    Nonempty (CondensedPointMatrixData k l E)

theorem condensed_point_tensor_model_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    [M : CondensedPointMatrixData k l E] :
    Nonempty (CondensedPointTensorModelData k l E)

theorem condensed_point_tensor_compatibility
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    [M : CondensedPointMatrixData k l E]
    [T : CondensedPointTensorModelData k l E] :
    pointSupertraceTensorMatrix k l E ∧ pointSupertraceTensorDescent k l E

theorem condensed_point_duality_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] :
    Nonempty (CondensedPointDualityData k l E)

class CondensedPointMatrixData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] where
  frame_mem : ∀ F : PointSupertraceFrame E.val,
    DerivedCategory.pointFiniteDimensional E.val (DerivedCategory.Q.obj F.complex)
  model : PointSupertraceFrame E.val → CochainComplex (PointCondensedModules k l) ℤ
  termIso : ∀ (F : PointSupertraceFrame E.val) (i : ℤ),
    (model F).X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l))
  differential_matrix : ∀ (F : PointSupertraceFrame E.val) (i j : ℤ)
    (a : Fin (F.rank i)) (b : Fin (F.rank j)),
    biproduct.ι (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l)) a ≫
      (termIso F i).inv ≫ (model F).d i j ≫ (termIso F j).hom ≫
      biproduct.π (fun _ : Fin (F.rank j) ↦ 𝟙_ (PointCondensedModules k l)) b =
        S.scalar ((F.basis j).repr ((F.complex.d i j).hom (F.basis i a)) b).val
  modelIso : ∀ F : PointSupertraceFrame E.val,
    (R.rho.obj ⟨DerivedCategory.Q.obj F.complex, frame_mem F⟩).obj ≅
      DerivedCategory.Q.obj (model F)
  modelMap : ∀ (F G : PointSupertraceFrame E.val),
    (F.complex ⟶ G.complex) → (model F ⟶ model G)
  chain_map_matrix : ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex)
    (i : ℤ) (a : Fin (F.rank i)) (b : Fin (G.rank i)),
    biproduct.ι (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l)) a ≫
      (termIso F i).inv ≫ (modelMap F G f).f i ≫ (termIso G i).hom ≫
      biproduct.π (fun _ : Fin (G.rank i) ↦ 𝟙_ (PointCondensedModules k l)) b =
        S.scalar ((G.basis i).repr ((f.f i).hom (F.basis i a)) b).val
  chain_map_descent : ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex),
    (R.rho.map (ObjectProperty.homMk (DerivedCategory.Q.map f))).hom ≫ (modelIso G).hom =
      (modelIso F).hom ≫ DerivedCategory.Q.map (modelMap F G f)
  quasi_iso : ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex),
    QuasiIso f → IsIso (DerivedCategory.Q.map (modelMap F G f))

class CondensedPointDualityData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] where
  dual_mem : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    DerivedCategory.pointFiniteDimensional E.val
      ((ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))))
  pairing : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    ExactPairing (R.rho.obj C)
      (R.rho.obj ⟨(ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))), dual_mem C⟩)
  pairing_evaluation : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    (pairing C).evaluation' =
      Functor.LaxMonoidal.μ R.rho _ C ≫ R.rho.map (ObjectProperty.homMk
        ((β_ ((ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val)))) C.obj).hom ≫
          (ihom.ev C.obj).app (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))))) ≫
        (Functor.Monoidal.εIso R.rho).inv
  conjugate_trace :
    ∀ (C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory)
      (P : PointCondensedCategory k l) (w : P ≅ R.rho.obj C),
    ∃ ep : ExactPairing P
      (R.rho.obj ⟨(ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))), dual_mem C⟩),
      ep.evaluation' = (𝟙 _ ⊗ₘ w.hom) ≫ (pairing C).evaluation' ∧
      ep.coevaluation' = (pairing C).coevaluation' ≫ (w.inv ⊗ₘ 𝟙 _) ∧
      ∀ (v : P ⟶ P) (f : C ⟶ C), v ≫ w.hom = w.hom ≫ R.rho.map f →
        @trace _ _ _ _ P { rightDual := _, exact := ep } v =
          S.epsilon (∑ᶠ i : ℤ, i.negOnePow • LinearMap.trace E.val
            ((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).obj C.obj)
            (((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).map f.hom).hom))
  unit_trace : ∃ h : HasRightDual (𝟙_ (PointCondensedCategory k l)),
    @trace _ _ _ _ _ h (𝟙 _) = S.epsilon 1

noncomputable instance pointSupertraceModuleColimits
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :
    HasColimitsOfSize.{0, 0} (PointCondensedModules k l) :=
  InternalAbelianSheafModule.comparison_internalColimits
    (Scheme.ProEt.topology (Spec (.of k))) (padicAlgClRingObj (Spec (.of k)) l)

noncomputable instance pointSupertraceTotalExists
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (K L : CochainComplex (PointCondensedModules k l) ℤ) :
    K.HasMapBifunctor L (curriedTensor (PointCondensedModules k l)) :=
  InternalAbelianSheafModule.comparison_internalTotalExists
    (Scheme.ProEt.topology (Spec (.of k))) (padicAlgClRingObj (Spec (.of k)) l) K L

noncomputable instance pointSupertraceSourceBraiding
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :
    BraidedCategory (DerivedCategory (ModuleCat.{0} E.val)) :=
  DerivedCategory.perfectTraceCanonicalBraiding (ModuleCat.{0} E.val)

noncomputable instance pointSupertraceTargetBraiding
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :
    BraidedCategory (DerivedCategory (PointCondensedModules k l)) :=
  DerivedCategory.perfectTraceCanonicalBraiding (PointCondensedModules k l)
```

## New

```lean
theorem condensed_point_realization_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    ∃ (R : CondensedPointRealizationData k l E)
      (S : @CondensedPointScalarData k _ l _ E R)
      (M : @CondensedPointMatrixData k _ l _ E R S)
      (T : @CondensedPointTensorModelData k _ l _ E R S M),
      @pointSupertraceTensorMatrix k _ l _ E R S M T ∧
        @pointSupertraceTensorDescent k _ l _ E R S M T

theorem condensed_point_duality_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    [M : CondensedPointMatrixData k l E] :
    Nonempty (CondensedPointDualityData k l E)

class CondensedPointMatrixData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] where
  frame_mem : ∀ F : PointSupertraceFrame E.val,
    DerivedCategory.pointFiniteDimensional E.val (DerivedCategory.Q.obj F.complex) :=
      pointSupertraceFrame_mem E.val
  model : PointSupertraceFrame E.val → CochainComplex (PointCondensedModules k l) ℤ
  termIso : ∀ (F : PointSupertraceFrame E.val) (i : ℤ),
    (model F).X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l))
  differential_matrix : pointSupertraceDifferentialMatrix k l E model termIso
  modelIso : ∀ F : PointSupertraceFrame E.val,
    (R.rho.obj ⟨DerivedCategory.Q.obj F.complex, frame_mem F⟩).obj ≅
      DerivedCategory.Q.obj (model F)
  modelMap : ∀ (F G : PointSupertraceFrame E.val),
    (F.complex ⟶ G.complex) → (model F ⟶ model G)
  chain_map_matrix : pointSupertraceChainMapMatrix k l E model termIso modelMap
  chain_map_descent : ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex),
    (R.rho.map (ObjectProperty.homMk (DerivedCategory.Q.map f))).hom ≫ (modelIso G).hom =
      (modelIso F).hom ≫ DerivedCategory.Q.map (modelMap F G f)
  quasi_iso : ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex),
    QuasiIso f → IsIso (DerivedCategory.Q.map (modelMap F G f))

class CondensedPointDualityData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] where
  dual_mem : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    DerivedCategory.pointFiniteDimensional E.val
      ((ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))))
  pairing : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    ExactPairing (R.rho.obj C)
      (R.rho.obj ⟨(ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))), dual_mem C⟩)
  pairing_evaluation : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    (pairing C).evaluation' =
      Functor.LaxMonoidal.μ R.rho _ C ≫ R.rho.map (ObjectProperty.homMk
        ((β_ ((ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val)))) C.obj).hom ≫
          (ihom.ev C.obj).app (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))))) ≫
        (Functor.Monoidal.εIso R.rho).inv
  conjugate_trace : pointSupertraceConjugateTrace k l E dual_mem pairing
  unit_trace : ∃ h : HasRightDual (𝟙_ (PointCondensedCategory k l)),
    @trace _ _ _ _ _ h (𝟙 _) = S.epsilon 1

instance pointSupertraceSiteSmall (k : Type u) [Field k] :
    EssentiallySmall.{u + 1} (Spec (.of k)).ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

noncomputable instance pointSupertraceModuleColimits
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :
    HasColimitsOfSize.{0, 0} (PointCondensedModules k l) := by
  exact Adjunction.has_colimits_of_equivalence
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology (Spec (.of k))) (padicAlgClRingObj (Spec (.of k)) l)).functor

noncomputable instance pointSupertraceTotalExists
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (K L : CochainComplex (PointCondensedModules k l) ℤ) :
    K.HasMapBifunctor L (curriedTensor (PointCondensedModules k l)) := by
  intro n
  exact (pointSupertraceModuleColimits k l).has_colimits_of_shape _ |>.has_colimit _

noncomputable instance pointSupertraceFieldBraiding (E : Type) [Field E] :
    BraidedCategory (DerivedCategory (ModuleCat.{0} E)) :=
  DerivedCategory.braidedCategory' (ModuleCat.{0} E)

@[instance_reducible]
noncomputable def pointSupertraceSourceBraiding
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :
    BraidedCategory (DerivedCategory (ModuleCat.{0} E.val)) :=
  DerivedCategory.braidedCategory' (ModuleCat.{0} E.val)

noncomputable instance (priority := 100) pointSupertraceTargetBraiding
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :
    BraidedCategory (DerivedCategory (PointCondensedModules k l)) :=
  DerivedCategory.braidedCategory' (PointCondensedModules k l)

def pointSupertraceDifferentialMatrix
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    (model : PointSupertraceFrame E.val → CochainComplex (PointCondensedModules k l) ℤ)
    (termIso : ∀ (F : PointSupertraceFrame E.val) (i : ℤ),
      (model F).X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l))) : Prop :=
  ∀ (F : PointSupertraceFrame E.val) (i j : ℤ)
  (a : Fin (F.rank i)) (b : Fin (F.rank j)),
  biproduct.ι (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l)) a ≫
    (termIso F i).inv ≫ (model F).d i j ≫ (termIso F j).hom ≫
    biproduct.π (fun _ : Fin (F.rank j) ↦ 𝟙_ (PointCondensedModules k l)) b =
      S.scalar ((F.basis j).repr ((F.complex.d i j).hom (F.basis i a)) b).val

def pointSupertraceChainMapMatrix
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    (model : PointSupertraceFrame E.val → CochainComplex (PointCondensedModules k l) ℤ)
    (termIso : ∀ (F : PointSupertraceFrame E.val) (i : ℤ),
      (model F).X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l)))
    (modelMap : ∀ (F G : PointSupertraceFrame E.val),
      (F.complex ⟶ G.complex) → (model F ⟶ model G)) : Prop :=
  ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex)
  (i : ℤ) (a : Fin (F.rank i)) (b : Fin (G.rank i)),
  biproduct.ι (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l)) a ≫
    (termIso F i).inv ≫ (modelMap F G f).f i ≫ (termIso G i).hom ≫
    biproduct.π (fun _ : Fin (G.rank i) ↦ 𝟙_ (PointCondensedModules k l)) b =
      S.scalar ((G.basis i).repr ((f.f i).hom (F.basis i a)) b).val

def pointSupertraceConjugateTrace
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    (dual_mem : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
      DerivedCategory.pointFiniteDimensional E.val
        ((ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val)))))
    (pairing : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
      ExactPairing (R.rho.obj C)
        (R.rho.obj ⟨(ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))),
          dual_mem C⟩)) : Prop :=
  ∀ (C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory)
    (P : PointCondensedCategory k l) (w : P ≅ R.rho.obj C),
  ∃ ep : ExactPairing P
    (R.rho.obj ⟨(ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))), dual_mem C⟩),
    ep.evaluation' = (𝟙 _ ⊗ₘ w.hom) ≫ (pairing C).evaluation' ∧
    ep.coevaluation' = (pairing C).coevaluation' ≫ (w.inv ⊗ₘ 𝟙 _) ∧
    ∀ (v : P ⟶ P) (f : C ⟶ C), v ≫ w.hom = w.hom ≫ R.rho.map f →
      @trace _ _ _ _ P { rightDual := _, exact := ep } v =
        S.epsilon (∑ᶠ i : ℤ, i.negOnePow • LinearMap.trace E.val
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).obj C.obj)
          (((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).map f.hom).hom))

theorem pointSupertraceFrame_mem (E : Type) [Field E] :
    ∀ F : PointSupertraceFrame E,
      DerivedCategory.pointFiniteDimensional E (DerivedCategory.Q.obj F.complex) := by
  intro F
  classical
  obtain ⟨s, hs⟩ := F.bounded
  apply DerivedCategory.pointFiniteDimensional_Q_of_finite_terms E F.complex s
  · intro i hi
    have hr : F.rank i = 0 := hs i hi
    haveI : Subsingleton (Fin (F.rank i) → E) := by rw [hr]; infer_instance
    haveI : Subsingleton (F.complex.X i) :=
      (F.basis i).equivFun.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · intro i
    exact (F.basis i).finiteDimensional_of_finite
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedPointSupertrace | N4 | Unpack compatible choices in the parent, copy scalar fields, and pass matrix data to duality; use the compact proposition names. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed, quarantined | Uses the parent package and projections, whose expanded field types are preserved; its archive is unchanged. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed, quarantined | Uses the parent package; coefficient and constructibility imports are already direct; its archive is unchanged. |

Downstream checks for realization_exists, tensor_compatibility, duality_exists and
CondensedPointScalarData find only this item. Repository/quarantine searches find
no other use of changed helper theorem names or generated SizeOf/injectivity lemmas.
Neither archived parent uses the perfect-trace API formerly re-exported by the item.
No external module requires adaptation. No Challenge declaration is modified and
no target mathematical condition is weakened.

The existing definitions now have their own DAG attachment
(def-zl-condensed-point-supertrace-data). Component statement dependencies refer to
that interface instead of the entire parent existence assertion. Comparison of the
whole overlaid graph with the repository introduces no new cyclic component.

The broad public imports of PerfectCategoricalTrace, CoefficientExtensionFinite,
ProEtaleBoundedConstructible and InternalSectionTensorComparison are replaced by the
needed definition APIs or removed. In particular DerivedCategory.braidedCategory'
and perfectTraceCanonicalBraiding have the identical DerivedMonoidal.braidedCategory'
body. The source-library definitions, attributes and public imports are untouched.
The target specialization has instance priority 100; the source specialization is
retained as an instance-reducible named definition, with a direct field-indexed
canonical source instance. The original scalar-data interface is preserved. Existing
sheaf monoidal structures are registered locally, not changed.

Unused SizeOf/injectivity generation is disabled, and the existing false settings
for backward.isDefEq.respectTransparency and its types option are used, as in the
quarantined parent modules. The complete item compiled without warnings in 36.6 s,
with its new proved dependency compiling as well. This repairs the earlier repeated
60-second elaboration timeouts without splitting the module or raising the limit.

## Status

landed 20261021T013349-L-2291023 2026-10-21 (merge of deliver/N4/Sheaf.Paper.CondensedPointSupertrace)
