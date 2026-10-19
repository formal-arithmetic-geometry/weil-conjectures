/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Sheaf.AlgebraicGeometry.LocallyFreeConstantModelComparison
import Sheaf.AlgebraicGeometry.EllAdicIntegralIndHeartWeakSerre
import Sheaf.Paper.ProperHeartBound
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.IndHeartKernelsCokernels
import Sheaf.Paper.IndConstructibleExtensions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
/-! # Finite coefficient transport and weak Serre closure

Source: blueprint `sk-prop-ind-heart`. The private helpers transport finite presentations,
ambient ind closures and derived proper bounds along actual coefficient isomorphisms.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

private theorem constructible_comapIso
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (h : IsConstructibleModuleObject S M) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj M) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun i ↦ ?_⟩
  exact lfp_of_iso (lfp_comap ((upperStar Ab.{u + 1} (T.immersion i)).map φ) (hT i))
    (((upperStar Ab.{u + 1} (T.immersion i)).mapModComapIso φ).app M).symm

private theorem constructible_comapIso_iff
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj M) ↔
      IsConstructibleModuleObject S M := by
  refine ⟨fun h ↦ ?_, constructible_comapIso φ M⟩
  exact constructible_of_iso S ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm
    (constructible_comapIso (inv φ) _ h)

private theorem indConstructible_comapIso :
    ObjectProperty.ind.{u + 1} (IsConstructibleModuleObject S) =
      ObjectProperty.inverseImage (ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject R)) (Mod.comap φ) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e h ↦ constructible_of_iso R e h⟩
  have heq : IsConstructibleModuleObject S =
      ObjectProperty.inverseImage (IsConstructibleModuleObject R) (Mod.comap φ) := by
    funext M
    exact propext (constructible_comapIso_iff φ M).symm
  let e := Mod.comapEquivalenceOfIsIso φ
  have :
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ).IsEquivalence := by
    change e.functor.IsEquivalence
    infer_instance
  rw [heq, ObjectProperty.ind_inverseImage_eq_of_isEquivalence]

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.ObjectProperty
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [PreservesFiniteColimits F] in
private theorem kernels_inverseImage_of_exact [P.IsClosedUnderKernels] :
    (P.inverseImage F).IsClosedUnderKernels := by
  constructor
  rintro _ ⟨f, c, hc, hA, hB⟩
  have h := P.prop_of_iso (PreservesKernel.iso F f).symm
    (P.prop_kernel (F.map f) hA hB)
  exact P.prop_of_iso (F.mapIso ((kernelIsKernel f).conePointUniqueUpToIso hc)) h

omit [PreservesFiniteLimits F] in
private theorem cokernels_inverseImage_of_exact [P.IsClosedUnderCokernels] :
    (P.inverseImage F).IsClosedUnderCokernels := by
  constructor
  rintro _ ⟨f, c, hc, hA, hB⟩
  have h := P.prop_of_iso (PreservesCokernel.iso F f).symm
    (P.prop_cokernel (F.map f) hA hB)
  exact P.prop_of_iso (F.mapIso ((cokernelIsCokernel f).coconePointUniqueUpToIso hc)) h
end CategoryTheory.ObjectProperty

namespace Profinite
variable {E F : Type} [NormedField E] [NormedField F]
private noncomputable def continuousMapRingSheafIso
    (e : E ≃+* F) (he : Continuous e) (hi : Continuous e.symm) :
    continuousMapRingSheaf.{u} E ≅ continuousMapRingSheaf F where
  hom := continuousMapRingSheafMap e.toRingHom he
  inv := continuousMapRingSheafMap e.symm.toRingHom hi
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
    exact e.apply_symm_apply _
end Profinite
namespace AlgebraicGeometry.ProEtale
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
private theorem exists_continuous_finiteSubfield_equiv :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      ∃ e : E ≃ₐ[ℚ_[ℓ]] F, Continuous e ∧ Continuous e.symm := by
  let emb : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let e := emb.equivFieldRange
  have : FiniteDimensional ℚ_[ℓ] emb.fieldRange := e.toLinearEquiv.finiteDimensional
  refine ⟨⟨emb.fieldRange, inferInstance⟩, e, ?_, ?_⟩
  · exact e.toLinearMap.continuous_of_finiteDimensional
  · exact e.symm.toLinearMap.continuous_of_finiteDimensional
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
include k

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem continuous_indConstructible_weakSerre
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    let P := ObjectProperty.ind.{u + 1}
      (IsConstructibleModuleObject
        (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  have : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  have : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  have : IsNoetherian X.left := {}
  obtain ⟨F, e, he, hi⟩ := exists_continuous_finiteSubfield_equiv ℓ E
  let eR := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
      (Profinite.continuousMapRingSheafIso e.toRingEquiv he hi)
  let φ := (upperStarFromPoint X.left).map eR.inv
  have : IsMonHom eR.inv := Sheaf.isMonHom_sheafCompose_map
    (coherentTopology Profinite.{u}) (Profinite.continuousMapRingSheafIso e.toRingEquiv he hi).inv
  have : IsMonHom φ := inferInstance
  have : IsIso φ := inferInstance
  rw [indConstructible_comapIso φ]
  have heq := constructible_eq_constantModels_of_lfp_locally_free
    (Profinite.continuousMapRingObj F) (finite_lf ℓ F) X.left
  rw [heq]
  let Q := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.continuousMapRingObj F) X.left)
  have hKC := (indHeart_kernelsCokernels ℓ (ringChar k) k
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) X.left).1 F
  have : Q.IsClosedUnderKernels := by
    constructor
    rintro _ ⟨f, c, hc, hA, hB⟩
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hKC _ _ f hA hB
    exact Q.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hc) hk
  have : Q.IsClosedUnderCokernels := by
    constructor
    rintro _ ⟨f, c, hc, hA, hB⟩
    obtain ⟨_, _, _, _, _, _, _, _, hk⟩ := hKC _ _ f hA hB
    exact Q.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hc) hk
  have : Q.IsClosedUnderExtensions :=
    ⟨fun hS hA hB ↦ indConstructible_of_shortExact ℓ F X.left _ hS hA hB⟩
  exact ⟨Q.kernels_inverseImage_of_exact (Mod.comap φ),
    Q.cokernels_inverseImage_of_exact (Mod.comap φ), inferInstance⟩
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] [IsIso a] {X Y : Scheme.{u}} (f : X ⟶ Y)

include a in
private theorem proper_heart_bound_of_coefficient_iso (c : ℕ)
    (h : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
      ObjectProperty.ind.{u + 1} (IsConstructibleModuleObject (condensedRingObj Λ X)) M →
      ∀ j : ℤ, (c : ℤ) < j → IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((R((f)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj M)))) :
    ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X),
      ObjectProperty.ind.{u + 1} (IsConstructibleModuleObject (condensedRingObj Λ' X)) M →
      ∀ j : ℤ, (c : ℤ) < j → IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((R((f)_*⟦Λ'⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have hflat (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv (coefficientMap a T)).symm
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (coefficientMap a Y)
  have : U.Faithful :=
    (Mod.comapEquivalenceOfIsIso (coefficientMap a Y)).fullyFaithfulFunctor.faithful
  intro M hM j hj
  have hM' := hM
  rw [indConstructible_comapIso (coefficientMap a X)] at hM'
  have hz := h _ hM' j hj
  let e := (derivedComapLowerStarIso a f).app ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    (R((f)_*⟦Λ⟧)).mapIso
      (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).app M)
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso e)
  have hz'' := hz'.of_iso
    ((U.mapDerivedCategoryHomologyFunctorIso j).app
      ((R((f)_*⟦Λ'⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj M)))
  rw [IsZero.iff_id_eq_zero]
  apply U.map_injective
  calc
    U.map (𝟙 _) = 𝟙 _ := U.map_id _
    _ = 0 := hz''.eq_of_src _ _
    _ = U.map 0 := (U.map_zero _ _).symm
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem continuous_proper_heart_upper_bound
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ c : ℕ, ∀ M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z.left),
      ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.continuousMapRingObj E) Z.left)) M →
      ∀ j : ℤ, (c : ℤ) < j →
        IsZero ((DerivedCategory.homologyFunctor _ j).obj
          ((R((g.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj
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
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := {}
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le Z.hom
  have hdim (y : Y.left) (n : ℕ)
      (hn : (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback g.left (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.left.residueField y) (AlgebraicClosure (Y.left.residueField y)))) ≫
            Y.left.fromSpecResidueField y) : Scheme.{u})) : (n : ℤ) ≤ d := by
    have h := hn.trans ((topologicalKrullDim_pullback_le g.left _).trans hd)
    exact_mod_cast h
  obtain ⟨F, eF, he, hi⟩ := exists_continuous_finiteSubfield_equiv ℓ E
  have heq := constructible_eq_constantModels_of_lfp_locally_free
    (Profinite.continuousMapRingObj F) (finite_lf ℓ F) Z.left
  have h := (properHeartBound ℓ F k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ)
    Z.left Y.left g.left d hdim).1
  let eR := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
      (Profinite.continuousMapRingSheafIso eF.toRingEquiv he hi)
  have : IsMonHom eR.inv := Sheaf.isMonHom_sheafCompose_map
    (coherentTopology Profinite.{u}) (Profinite.continuousMapRingSheafIso eF.toRingEquiv he hi).inv
  refine ⟨2 * d + 1, proper_heart_bound_of_coefficient_iso eR.inv g.left (2 * d + 1) ?_⟩
  intro M hM j hj
  rw [heq] at hM
  exact (h M hM).1 j (by exact_mod_cast hj)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

include k

/-- The ind-constructible heart for finite field and integral coefficients is weak Serre.

Source: blueprint `sk-prop-ind-heart`, kernel/cokernel and extension steps, and
`det-prop-int-compactness-compact` (1)-(2).
(blueprint: new-lem-sfb-adic-ind-heart-weak-serre)

Proof: identify finite local presentations with finite constant coefficient models on
strata. For continuous finite field coefficients use local finite freeness, then
transport the finite extension to a subfield of the fixed algebraic closure. For
integral coefficients use continuous local Smith presentations and their torsion charts.
Finite presentations descend morphisms and relations to common filtered stages.
The exact ambient ind-realization therefore identifies kernels and cokernels with
filtered colimits of their constructible counterparts. For extensions, first pull back
along a constructible stage of the quotient, descend its extension class to a stage of
the subobject by Ext-continuity, and push out the finite-stage extension. Taking the
filtered colimit over quotient stages recovers the original sequence by exactness and
the short five lemma. This proves the three closure conditions. Zero modules and
empty schemes are covered by the same presentations. -/
theorem ellAdic_finite_indConstructible_weakSerre :
    (∀ (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E],
      let P := ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
      P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions) ∧
    (∀ (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
      [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E],
      let P := ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
      P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions) := by
  exact ⟨continuous_indConstructible_weakSerre ℓ X,
    ellAdic_integral_indConstructible_weakSerre ℓ X⟩

end AlgebraicGeometry.ProEtale.CondensedRing
