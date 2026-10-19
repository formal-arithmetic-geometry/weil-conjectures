/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import all Sheaf.AlgebraicGeometry.EllAdicFiniteIndHeartWeakSerre
import all Sheaf.Paper.IntegralConstantModelHeartClosure
import Sheaf.Paper.IntegralProperDirectSums
import Sheaf.Paper.IntegralLfpConstantModelComparison
import WeilConjectures.NumberTheory.Padics.Extension
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Proper upper bound on the ind-constructible heart

This isolates the class-relative upper-amplitude argument from the truncation-window
corollary. Source: blueprint `sk-lem-proper-unbounded-window` and
`det-prop-int-compactness-direct-sums` (1)-(2).
(blueprint: new-lem-sfb-integral-constructible-heart-bound)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSeparated Z.hom] in
private theorem canonical_integral_constructible_eq
    (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ F) Z.left) =
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ F) Z.left := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := {}
  obtain ⟨e⟩ := integralCoefficientIso.{u} ℓ F
  let a := e.hom.hom
  have : IsMonHom a := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso a := inferInstanceAs (IsIso e.hom.hom)
  funext M
  apply propext
  have hp := integralLfpConstantModelComparison ℓ (ULift.{u} F) Z.left
    ((Mod.comap (coefficientMap a Z.left)).obj M)
  exact (constructible_comapIso_iff (coefficientMap a Z.left) M).symm.trans
    (hp.trans (constantModel_comap_iff a Z.left M))

private theorem canonical_integral_heart_bound
    (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ c : ℕ, ∀ M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F) Z.left),
      ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ F) Z.left)) M →
      ∀ j : ℤ, (c : ℤ) < j →
        IsZero ((DerivedCategory.homologyFunctor _ j).obj
          ((R((g.left)_*⟦Profinite.padicIntegersRingObj ℓ F⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let : Z.left.Over (Spec (.of k)) := ⟨Z.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  have : LocallyOfFiniteType (Z.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : QuasiCompact (Z.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Z.hom)
  have : IsSeparated (Z.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Z.hom)
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  have : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  have : g.left.IsOver (Spec (.of k)) := ⟨g.w⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le Z.hom
  have hdim (y : Y.left) : topologicalKrullDim
      (pullback g.left (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.left.residueField y) (AlgebraicClosure (Y.left.residueField y)))) ≫
          Y.left.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞) :=
    (topologicalKrullDim_pullback_le g.left _).trans hd
  have h := (integralProperDirectSums ℓ F k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ)
    Z.left Y.left g.left d hdim).2.1
  refine ⟨2 * d + 1, ?_⟩
  intro M hM j hj
  rw [canonical_integral_constructible_eq ℓ (Z := Z) F] at hM
  have : ((R((g.left)_*⟦Profinite.padicIntegersRingObj ℓ F⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE (2 * (d : ℤ) + 1) :=
    (h M hM).2.2
  exact DerivedCategory.isZero_of_isLE _ (2 * (d : ℤ) + 1) j (by omega)

include ℓ k in
/-- Proper pushforward has a uniform upper bound on constructible integral sheaves.

Source: blueprint `det-prop-int-compactness-direct-sums`, proof steps 1--5.
(blueprint: new-lem-sfb-integral-constructible-heart-bound)

Proof: choose a natural number d bounding the geometric fibre dimensions of g.
Finite locally presented integral modules have finite constant scalar models on a finite
stratification. Their derived torsion reductions are represented by the two-term complex
[M -- pi^n --> M], in degrees [-1,0], including torsion M. The adic criterion makes these
reductions classical. The proper torsion cohomological bound puts their direct images
in degrees at most 2d. Derived completeness reconstructs M from this countable tower;
proper direct image preserves products. The Roos triangle and exact countable products
give the Milnor sequence, which loses at most one degree. Thus c = 2d+1 works uniformly
in M. Transport between any embedded finite E and its image in the fixed algebraic closure
preserves the integral coefficient ring, finite presentations and the direct image.
The argument includes zero modules, empty schemes and empty geometric fibres. -/
theorem ellAdic_integral_constructible_heart_upper_bound
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ c : ℕ, ∀ M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z.left),
      IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z.left) M →
      ∀ j : ℤ, (c : ℤ) < j →
        IsZero ((DerivedCategory.homologyFunctor _ j).obj
          ((R((g.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let emb : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)
  let ef := emb.equivFieldRange
  have : FiniteDimensional ℚ_[ℓ] emb.fieldRange := ef.toLinearEquiv.finiteDimensional
  let F : PadicAlgCl.FiniteIntermediateField ℓ := ⟨emb.fieldRange, inferInstance⟩
  let e : PadicAlgCl.integers ℓ E ≃+* PadicAlgCl.integers ℓ F :=
    { toFun := fun x ↦ ⟨ef x, by exact x.property⟩
      invFun := fun y ↦ ⟨ef.symm y, by
        change ‖algebraMap E (PadicAlgCl ℓ) (ef.symm y)‖₊ ≤ 1
        have he : algebraMap E (PadicAlgCl ℓ) (ef.symm y) = (y : F).val :=
          congrArg Subtype.val (ef.apply_symm_apply y)
        rw [he]
        exact y.property⟩
      left_inv := fun x ↦ Subtype.ext (ef.symm_apply_apply x)
      right_inv := fun y ↦ Subtype.ext (ef.apply_symm_apply y)
      map_mul' := fun x y ↦ Subtype.ext (map_mul ef (x : E) (y : E))
      map_add' := fun x y ↦ Subtype.ext (map_add ef (x : E) (y : E)) }
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F
  have he : Isometry e := AddMonoidHomClass.isometry_of_norm e (fun _ ↦ rfl)
  let ei : PadicAlgCl.integers ℓ E ≃ᵢ PadicAlgCl.integers ℓ F := ⟨e.toEquiv, he⟩
  let eR : Profinite.padicIntegersCondensedRing.{u} ℓ E ≅
      Profinite.padicIntegersCondensedRing ℓ F :=
    { hom := Profinite.continuousMapRingSheafMap e.toRingHom ei.continuous
      inv := Profinite.continuousMapRingSheafMap e.symm.toRingHom ei.symm.continuous
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro y
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro y
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  obtain ⟨c, hc⟩ := canonical_integral_heart_bound ℓ g F
  refine ⟨c, fun M hM j hj ↦ ?_⟩
  exact proper_heart_bound_of_coefficient_iso eAb.inv g.left c hc M
    (ObjectProperty.le_ind _ _ hM) j hj

end AlgebraicGeometry.ProEtale.CondensedRing
