# FiniteCoefficientTotalComparison.ChainIso and finiteHomNuChainTensor

## Reason

The normalized chain witness type expanded the inverse-image functor and signed
totalization whenever a uniqueness witness was chosen or passed to the naturality
proof. Share precisely that isomorphism type as `ChainIso`, name its uniquely
normalized source comparison before coefficient specialization, and specialize that
same named comparison at finite level. The normalization equations are retained
verbatim. The new comparison definition chooses from the existing **unique**
normalization theorem; it chooses no arbitrary object from mere existence.

The inferred finite-level return type is definitionally the original displayed
isomorphism type. No hypothesis, equation or conclusion is changed. Definition-meaning
review is reopened for all targets using these definitions. No target statement changes.

## Old

There was no named `ChainIso` or `finiteCoefficientIntrinsicChainTensor`.
The normalization declarations and finite-level definition were:

```lean
def normalizedTensorEquation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (e : tensor C ⋙ G ≅ G.prod G ⋙ tensor D)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)) : Prop :=
      ∀ (p q k : ℤ) (h : p + q = k),
        G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫ a.hom.f k =
          (e.app (P.X p, Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h
```

```lean
def Normalization
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (N : (tensor C ⋙ G ≅ G.prod G ⋙ tensor D) → Prop)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
      HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)) : Prop :=
  ∃ e, N e ∧ normalizedTensorEquation G e P Q a
```

```lean
def finiteHomNuChainTensor (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    (finiteHomNuComplex l E X n).obj (HomologicalComplex.tensorObj P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
        ((finiteHomNuComplex l E X n).obj P, (finiteHomNuComplex l E X n).obj Q) :=
  (finiteHomNuChainTensor_existsUnique l E X n P Q).choose
```

## New

```lean
def ChainIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)] : Type _ :=
  (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
    HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)
```

```lean
def normalizedTensorEquation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q) : Prop :=
      ∀ (p q k : ℤ) (h : p + q = k),
        G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫ a.hom.f k =
          (e.app (P.X p, Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h
```

```lean
def Normalization
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (N : (FiniteCoefficientTotalComparison.Ordinary G) → Prop)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q) : Prop :=
  ∃ e, N e ∧ normalizedTensorEquation G e P Q a
```

```lean
def finiteCoefficientIntrinsicChainTensor
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    FiniteCoefficientTotalComparison.ChainIso (finiteCoefficientIntrinsicComparison X A) P Q :=
  (finiteCoefficientIntrinsicChainTensor_existsUnique X A P Q).choose
```

```lean
def finiteHomNuChainTensor (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  ProEtale.finiteCoefficientIntrinsicChainTensor X
    (Padic.coefficientExtensionRing l E (n + 1)) P Q
```

The private lifted isomorphism and total-equation helper use the same `ChainIso`
alias for their old native isomorphism types. Their constructions and equations are retained. The existence-and-uniqueness
argument is assembled by a fully proved private generic lemma: choose the uniquely
normalized ordinary comparison, lift it to total complexes, and use ordinary
uniqueness followed by total-summand extensionality. `Ordinary` sharing is recorded separately
in `finite-ordinary-tensor-comparison-sharing.md`.

## Server compile repair

The returned packet's full chain-comparison module exceeded the 60-second compile
limit when choosing its normalized comparison. Profiling showed that the proof
through the uniqueness theorem compiled, while the final data definition triggered
repeated expansion of the totalization instances. Name those existing instances
before forming the normalization and choosing its uniquely specified witness:

```lean
/-- The source totalization instance, shared before using its normalized comparison.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
instance finiteCoefficientIntrinsicSourceHasTensor
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    HomologicalComplex.HasTensor P Q := by infer_instance

/-- The target totalization instance, shared before using its normalized comparison.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
instance finiteCoefficientIntrinsicTargetHasTensor
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    HomologicalComplex.HasMapBifunctor
      (((finiteCoefficientIntrinsicComparison X A).mapHomologicalComplex (.up ℤ)).obj P)
      (((finiteCoefficientIntrinsicComparison X A).mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)))
      (.up ℤ) := by infer_instance
```

Both instances are proved by the existing instances; they add no hypothesis or
choice of data. `HasTensor` and `HasMapBifunctor` are propositions, so replacing
inferred instance proofs with these named proofs preserves the total objects by
proof irrelevance. The uniqueness theorem and chosen definition explicitly use
`ChainIso` for their isomorphism type. This is definitionally their previous type.
The entire module compiled on the server in 31.9 seconds after this change.

## Users

The source-import closure and whole-name searches give the following consumers.
Every unchanged consumer retains its statement because the changed types and
constructors unfold to the original ones. Rows also retain adapted and new modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.FiniteCoefficientIntrinsicChainTensor | unclaimed | Shares the identical type and names the unique normalized comparison. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Specializes that same comparison; its inferred type is the original type. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.FiniteCoefficientSiteTensorNaturality | new, Y7 | Uses the shared type and named comparison in the naturality proof. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Unchanged; the shared type or constructor is definitionally identical where used. |
| WeilConjectures | unclaimed | Aggregate import names contain the textual token Normalization; this is not a use of the changed normalization predicate. The aggregate source and its public imports remain unchanged. |
| Sheaf.Paper.FiniteCoefficientKFlatReflection | new, Y7 | Uses the specified finite-level chain isomorphism to reflect tensor acyclicity; its proof compiles unchanged with the same comparison. |

## Status

landed 20261022T114256-L-598666 2026-10-22 (merge of deliver/Y7/Sheaf.Paper.FiniteCoefficientSiteHomArrow)
