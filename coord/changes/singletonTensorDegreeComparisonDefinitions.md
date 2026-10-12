# singletonTensorCech, singletonTensorAmitsur, singletonTensorCechCosimplicial, singletonTensorForget, IsSingletonTensorDegreeComparison

## Reason

Move the five existing definitions, without changing their signatures or bodies, into
Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization. The item publicly
imports that module, so the same names remain available to every existing importer.
The new homomorphism and inverse statements then live in their own modules without
an import cycle or expanding the tensor-pullback constructions inside their signatures.
The new normalization predicate is the existing isomorphism normalization with its
homomorphism supplied directly. No definition acquires data from an unproved existence claim.

## Old

In Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeComparison:

```lean
/-- The singleton tensor-section Čech complex, before identifying its terms. -/
abbrev singletonTensorCech (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) :=
  (cechComplexFunctor fun _ : Fin 1 ↦ Over.mk g).obj
    ((Over.forget U).op ⋙
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf F)).obj)

/-- Forget scalars and lift the affine Amitsur complex. -/
abbrev singletonTensorAmitsur (X : Scheme.{u}) (F : X.Modules)
    (U W : X.Etale) (g : W ⟶ U) :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  (((forget₂ (ModuleCat.{u} Γ(U.left, ⊤)) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
      (Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) Γ(W.left, ⊤)
        Γ((Modules.tensorPullback U.hom).obj F, ⊤))

/-- The cosimplicial object underlying the singleton tensor-section Čech complex. -/
abbrev singletonTensorCechCosimplicial (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) :=
  (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ (fun _ : Fin 1 ↦ Over.mk g)).cech).obj
      ((Over.forget U).op ⋙
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F)).obj)

/-- The coefficient-forgetting and universe-lifting functor used by the comparison. -/
abbrev singletonTensorForget (U : Scheme.{u}) :=
  (forget₂ (ModuleCat.{u} Γ(U, ⊤)) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The pure-tensor equation fixes the degree comparison uniquely: evaluate the singleton
product, multiply the pulled-back functions, and pull back the coefficient section.
This predicate mentions no differential or coface. -/
def IsSingletonTensorDegreeComparison (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (e : (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n) : Prop :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)),
    ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1} Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)))
      (fun _ ↦ 0))
        (e.hom (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
      (∏ k : Fin (n + 1), (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop
        (b k)) • Modules.etaleTensorSectionsRestriction F P.hom m
```

## New

In Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization:

```lean
/-- The singleton tensor-section Čech complex, before identifying its terms. -/
abbrev singletonTensorCech (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) :=
  (cechComplexFunctor fun _ : Fin 1 ↦ Over.mk g).obj
    ((Over.forget U).op ⋙
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf F)).obj)

/-- Forget scalars and lift the affine Amitsur complex. -/
abbrev singletonTensorAmitsur (X : Scheme.{u}) (F : X.Modules)
    (U W : X.Etale) (g : W ⟶ U) :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  (((forget₂ (ModuleCat.{u} Γ(U.left, ⊤)) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
      (Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) Γ(W.left, ⊤)
        Γ((Modules.tensorPullback U.hom).obj F, ⊤))

/-- The cosimplicial object underlying the singleton tensor-section Čech complex. -/
abbrev singletonTensorCechCosimplicial (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) :=
  (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ (fun _ : Fin 1 ↦ Over.mk g)).cech).obj
      ((Over.forget U).op ⋙
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F)).obj)

/-- The coefficient-forgetting and universe-lifting functor used by the comparison. -/
abbrev singletonTensorForget (U : Scheme.{u}) :=
  (forget₂ (ModuleCat.{u} Γ(U, ⊤)) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The pure-tensor equation fixes the degree comparison uniquely: evaluate the singleton
product, multiply the pulled-back functions, and pull back the coefficient section.
This predicate mentions no differential or coface. -/
def IsSingletonTensorDegreeComparison (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (e : (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n) : Prop :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)),
    ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1} Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)))
      (fun _ ↦ 0))
        (e.hom (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
      (∏ k : Fin (n + 1), (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop
        (b k)) • Modules.etaleTensorSectionsRestriction F P.hom m

/-- The pure-tensor normalization for a comparison homomorphism.
Source: Stacks Project, Tag 03P2, affine tensor calculation.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom-normalization)
-/
def IsSingletonTensorDegreeComparisonHom (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n) : Prop :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)),
    ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1} Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)))
      (fun _ ↦ 0))
        (f (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
      (∏ k : Fin (n + 1), (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop
        (b k)) • Modules.etaleTensorSectionsRestriction F P.hom m
```

The five existing definitions have the exact old signatures and bodies. The only added
definition is the homomorphism normalization predicate. The original module now re-exports
them through:

```lean
public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
```

No mathematical definition or statement changes; no downstream adaptation is required.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeComparison | A3 | Definitions re-exported unchanged; fixed-degree proof assembled from hom and inverse. |
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorAmitsur | unclaimed | Same declarations, types and bodies via the public import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorCofaces | unclaimed | Same declarations, types and bodies via the public import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorPureCofaces | K3 | Same declarations, types and bodies via the public import; no adaptation. |

The source-only downstream scan finds these three external modules mentioning the relocated
names, among 147 transitive importers. All transitive importers retain the same public
imports through the new shared module. No target changes its meaning and no downstream
statement becomes weaker or stronger.

## Status

landed 20261012T202229-L-700338 2026-10-12 (merge of deliver/A3/Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeComparison)
