# affineRealizationComparison and the affine-realization comparison interface

## Reason

The geometric compatibility results must refer to the canonical comparison and restriction
before the realization theorem imports them. Move the four existing definitions to a public
interface module, avoiding an import cycle. This is an interface extraction, not a change of
mathematical data. The bundled raw and ordinary groups and their fixed comparison provide evaluation
and naturality APIs for the derived-Hom and Ext constructions. The scalar calculation
uses coefficient naturality and the affine specialization formula instead of unfolding
the chosen comparison. Private named section wrappers in the item provide structural
section types during natural-isomorphism construction; their canonical inverse maps
recover the original presheaves and all original normalization formulas.

## Old

The following declarations lived in AffineCohomologyEtaleModuleRealization:

```lean
/-- The common-lift simultaneous comparison, selected by its unique normalization.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization). -/
def affineRealizationComparison (Y : Scheme.{u}) [CompactSpace Y] [Y.IsSeparated]
    (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Sheaf.H (liftedCoherentEtaleSheaf M) q ≃+
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj M :=
  (Classical.choose (exists_unique_qcoherentNormalizedComparison Y) M q).symm

attribute [local irreducible] affineRealizationComparison

/-- Pullback with the canonical tensor-composition coefficient identification.
Source: Stacks Project, Tags 03Q8 and 01FD
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization). -/
def affineRealizationRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V)) ⟶
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V'.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V')) := by
  let B : S.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
  let b : B.obj V' ⟶ B.obj V := B.map h
  let adj : tensorPullback b.left ⊣ pushforward b.left :=
    Classical.choose (exists_tensorPullbackAdjunction b.left)
  let ψ : (tensorPullback b.left).obj (affineRealizationCoefficient f G V) ⟶
      affineRealizationCoefficient f G V' :=
    (tensorSectionsComp b.left (Limits.pullback.snd V.hom f)).hom.app G ≫
      eqToHom (congrArg (fun j ↦ (tensorPullback j).obj G) b.w)
  exact moduleCohomologyFMap b.left (adj.homEquiv _ _ ψ) q

attribute [local irreducible] affineRealizationRestriction

/-- The affine specialization of the canonical simultaneous comparison.
Quasi-compactness is stable under base change; separatedness over an affine scheme
implies absolute separatedness. Neither property is imposed on S.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization). -/
def affineRealizationAffineComparison {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V : S.Etale) [IsAffine V.left] :
    Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q ≃+
      (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V) := by
  letI : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  letI : CompactSpace ((𝟭 Scheme).obj V.left) :=
    Scheme.compactSpace_of_isAffine V.left
  exact @affineRealizationComparison (Limits.pullback V.hom f)
    (QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst V.hom f))
    ((HasAffineProperty.iff_of_isAffine (P := @IsSeparated)
      (Q := fun Y _ _ _ ↦ Scheme.IsSeparated Y)
      (f := Limits.pullback.fst V.hom f)).mp inferInstance)
    (affineRealizationCoefficient f G V) inferInstance q

attribute [local irreducible] affineRealizationAffineComparison

/-- Evaluate a sectionwise module action without introducing a file-local instance.
Source: Stacks Project, Modules on Sites, definition of a sheaf of modules
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization). -/
def affineRealizationSmul {R : Type v} {A : Type w} [Semiring R] [AddCommMonoid A]
    (m : Module R A) (a : R) (x : A) : A :=
  @SMul.smul R A m.toDistribMulAction.toMulAction.toSemigroupAction.toSMul a x

```

## New

The exact same signatures and bodies live in
`Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData`, publicly imported by the original
module. The four names and their meanings are unchanged. The unused public import of
QcoherentCohomologyComparisonPullback is omitted; normalized comparison and the
restriction bridge supply the actual proof. No existing Lean consumer imports the item. The new definition node owns their
Lean attachment. The existing theorem keeps its signature and all five conclusions.

The complete extracted module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
public import Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso
public import Sheaf.AlgebraicGeometry.EtaleCohomologyPresentation
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
public import Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Data for affine coherent cohomology realization

The canonical comparisons and restrictions are separated from their realization theorem
so that their geometric compatibility lemmas can be imported by that theorem.
Source: Stacks Project, Tags 03P2, 03FD and 03Q8.
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] Etale.sheafHDerivedEquiv Etale.sheafHToDerived
  CategoryTheory.derivedExtEvaluation coherentEtaleRestrictionIso
  moduleAbelianCohomologyLarge coherentEtaleMap
  moduleCohomologyFMap IsNormalizedCoherentEtaleComparison
  tensorPullback tensorPullbackObj tensorSectionsComp tensorSectionsUnit
  etaleTensorSectionsRestriction
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The common-lift simultaneous comparison, selected by its unique normalization.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-weil-pbc-affine-cohomology-comparison-data). -/
def affineRealizationComparison (Y : Scheme.{u}) [CompactSpace Y] [Y.IsSeparated]
    (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Sheaf.H (liftedCoherentEtaleSheaf M) q ≃+
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj M :=
  (Classical.choose (exists_unique_qcoherentNormalizedComparison Y) M q).symm

attribute [local irreducible] affineRealizationComparison

/-- Pullback with the canonical tensor-composition coefficient identification.
Source: Stacks Project, Tags 03Q8 and 01FD
(blueprint: def-weil-pbc-affine-cohomology-comparison-data). -/
def affineRealizationRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V)) ⟶
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V'.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V')) := by
  let B : S.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
  let b : B.obj V' ⟶ B.obj V := B.map h
  let adj : tensorPullback b.left ⊣ pushforward b.left :=
    Classical.choose (exists_tensorPullbackAdjunction b.left)
  let ψ : (tensorPullback b.left).obj (affineRealizationCoefficient f G V) ⟶
      affineRealizationCoefficient f G V' :=
    (tensorSectionsComp b.left (Limits.pullback.snd V.hom f)).hom.app G ≫
      eqToHom (congrArg (fun j ↦ (tensorPullback j).obj G) b.w)
  exact moduleCohomologyFMap b.left (adj.homEquiv _ _ ψ) q

attribute [local irreducible] affineRealizationRestriction

/-- The affine specialization of the canonical simultaneous comparison.
Quasi-compactness is stable under base change; separatedness over an affine scheme
implies absolute separatedness. Neither property is imposed on S.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: def-weil-pbc-affine-cohomology-comparison-data). -/
def affineRealizationAffineComparison {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V : S.Etale) [IsAffine V.left] :
    Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q ≃+
      (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V) := by
  letI : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  letI : CompactSpace ((𝟭 Scheme).obj V.left) :=
    Scheme.compactSpace_of_isAffine V.left
  exact @affineRealizationComparison (Limits.pullback V.hom f)
    (QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst V.hom f))
    ((HasAffineProperty.iff_of_isAffine (P := @IsSeparated)
      (Q := fun Y _ _ _ ↦ Scheme.IsSeparated Y)
      (f := Limits.pullback.fst V.hom f)).mp inferInstance)
    (affineRealizationCoefficient f G V) inferInstance q

attribute [local irreducible] affineRealizationAffineComparison

/-- Evaluate a sectionwise module action without introducing a file-local instance.
Source: Stacks Project, Modules on Sites, definition of a sheaf of modules
(blueprint: def-weil-pbc-affine-cohomology-comparison-data). -/
def affineRealizationSmul {R : Type v} {A : Type w} [Semiring R] [AddCommMonoid A]
    (m : Module R A) (a : R) (x : A) : A :=
  @SMul.smul R A m.toDistribMulAction.toMulAction.toSemigroupAction.toSMul a x

/-- The fixed bundled group of raw classes. Keeping the group bundled prevents
repeated unfolding of the derived-Hom presentation.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-affine-cohomology-comparison-data). -/
def affineRealizationRawGroup {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    [G.IsQuasicoherent] (q : ℕ) (V : S.Etale) : AddCommGrpCat.{u + 1} :=
  (Etale.abelianHigherDirectImageRawPresheaf f q (liftedCoherentEtaleSheaf G)).obj (op V)

/-- The bundled ordinary cohomology group of a chart.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-affine-cohomology-comparison-data). -/
def affineRealizationOrdinaryGroup {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    (q : ℕ) (V : S.Etale) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of ((RingedSpace.moduleCohomology
    (Limits.pullback V.hom f).toRingedSpace q).obj (affineRealizationCoefficient f G V))

/-- The raw restriction, retaining its specified bundled source and target.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-affine-cohomology-comparison-data). -/
def affineRealizationRawRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    affineRealizationRawGroup f G q V ⟶ affineRealizationRawGroup f G q V' :=
  (Etale.abelianHigherDirectImageRawPresheaf f q (liftedCoherentEtaleSheaf G)).map h.op

/-- The fixed composite of raw evaluation and the affine coherent comparison.
This records the existing construction, without making another choice.
Source: Stacks Project, Tags 03Q8 and 03P2
(blueprint: def-weil-pbc-affine-cohomology-comparison-data). -/
def affineRealizationRawCoherentEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V : S.Etale) [IsAffine V.left] :
    affineRealizationRawGroup f G q V ≃+ affineRealizationOrdinaryGroup f G q V :=
  (affineRealizationRawEquiv f G q V).trans (affineRealizationAffineComparison f G q V)

attribute [local irreducible] affineRealizationRawCoherentEquiv

/-- Evaluation formula for the fixed bundled comparison.
Source: Stacks Project, Tags 03Q8 and 03P2
(blueprint: def-weil-pbc-affine-cohomology-comparison-data).
Proof: the raw evaluation is the forward map of its constructed additive equivalence. -/
theorem affineRealizationRawCoherentEquiv_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V : S.Etale) [IsAffine V.left]
    (z : affineRealizationRawGroup f G q V) :
    affineRealizationRawCoherentEquiv f G q V z =
      affineRealizationAffineComparison f G q V
        (affineRealizationRawEvaluation f G q V z) := by
  unfold affineRealizationRawCoherentEquiv affineRealizationRawEvaluation
  rfl

/-- The inverse normalized comparison is natural in every coefficient morphism.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-weil-pbc-affine-cohomology-comparison-data).
Proof: apply the forward comparison, use its coefficient naturality, and cancel
both inverse pairs. -/
theorem affineRealizationComparison_natural (Y : Scheme.{u})
    [CompactSpace Y] [Y.IsSeparated] (M N : Y.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (q : ℕ)
    (x : Sheaf.H (liftedCoherentEtaleSheaf M) q) :
    affineRealizationComparison Y N q (Sheaf.H.map (coherentEtaleMap M N φ) q x) =
      ((RingedSpace.moduleCohomology Y.toRingedSpace q).map φ).hom
        (affineRealizationComparison Y M q x) := by
  unfold affineRealizationComparison
  let c := Classical.choose (exists_unique_qcoherentNormalizedComparison Y)
  apply (c N q).injective
  rw [AddEquiv.apply_symm_apply]
  have h : c N q (((RingedSpace.moduleCohomology Y.toRingedSpace q).map φ).hom
      ((c M q).symm x)) = Sheaf.H.map (coherentEtaleMap M N φ) q
        (c M q ((c M q).symm x)) :=
    (Classical.choose_spec (exists_unique_qcoherentNormalizedComparison Y)).1.2.2
      M N φ q ((c M q).symm x)
  simpa only [AddEquiv.apply_symm_apply] using h.symm

/-- The affine specialization is the same comparison for any proofs of the
required compactness and separatedness properties.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: def-weil-pbc-affine-cohomology-comparison-data).
Proof: unfold the specialization; proof irrelevance identifies its property witnesses. -/
theorem affineRealizationAffineComparison_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V : S.Etale) [IsAffine V.left]
    [CompactSpace (Limits.pullback V.hom f : Scheme.{u})]
    [Scheme.IsSeparated (Limits.pullback V.hom f : Scheme.{u})] :
    affineRealizationAffineComparison f G q V =
      affineRealizationComparison (Limits.pullback V.hom f)
        (affineRealizationCoefficient f G V) q := by
  unfold affineRealizationAffineComparison
  rfl

end
end AlgebraicGeometry.Scheme.Modules
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization | V1 | Publicly imports the extracted interface. |
| Sheaf.AlgebraicGeometry.AffineCohomologyRawRestriction | new, V1 | Uses canonical comparison and restriction. |
| Sheaf.AlgebraicGeometry.CoherentHigherImageModuleAction | new, V1 | Uses explicit action evaluation. |

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization` reports
zero current Lean downstream modules. Its DAG parents remain attached and need no change:
all names are re-exported, and no statement meaning changes. No source-library file changes.

## Status

landed 20261022T044031-L-1213921 2026-10-22 (merge of deliver/V1/Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization)
