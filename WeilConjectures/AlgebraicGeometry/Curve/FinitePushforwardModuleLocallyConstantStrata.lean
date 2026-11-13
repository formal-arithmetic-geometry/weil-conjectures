/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardModuleGenericReflection
import WeilConjectures.AlgebraicGeometry.Curve.DiscreteSchemeModuleLocallyConstant
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenFiniteComplement
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Data.Fin.VecNotation

/-! # Locally constant source strata for a finite direct image

Source: Stacks Project, Tags 095K, 0959, 04DZ and 0A5D, with the generic
finite-algebra splitting refinement for module coefficients.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The local constancy part of finite direct-image constructibility reflection.
Source: Stacks Project, Tag 095K, Tag 0959, Tag 04DZ, and the finite-stratification refinement of
Tag 0A5D. -/
theorem Scheme.exists_locallyConstant_stratification_of_finite_lowerStar_module
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsCurve g] [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : Scheme.IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) :
    ∃ S : Scheme.Stratification X, ∀ i : Fin S.n,
      Scheme.IsLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion i)).obj F) := by
  classical
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType g
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let : Scheme.IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := h
  obtain ⟨V, hV, hlocV⟩ := Scheme.IsConstructibleSheaf.exists_dense_open
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)
  obtain ⟨U, _, hU, hloc⟩ :=
    Scheme.exists_dense_open_locallyConstant_of_finite_lowerStar_module Λ f F V hV hlocV
  let W : X.Opens := f ⁻¹ᵁ U
  let Z := (Scheme.IdealSheafData.vanishingIdeal
    ⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩).subscheme
  let i : Z ⟶ X := W.closedComplement
  have hZrange : Set.range i = (W : Set X)ᶜ := W.range_closedComplement
  have hfin : ((W : Set X)ᶜ).Finite := by
    simpa only [W, Scheme.Hom.coe_preimage, Set.preimage_compl] using
      f.finite_preimage (IsCurve.dense_open_finite_complement g U hU).1
  let : Finite Z := (Set.finite_range_iff i.isClosedEmbedding.injective).mp (hZrange.symm ▸ hfin)
  let : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace (i ≫ f ≫ g)
  let : DiscreteTopology Z := inferInstance
  have hboundary := Scheme.isLocallyConstantSheaf_of_discrete_finiteType_module Λ
    (i ≫ f ≫ g) ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)
  let S : Scheme.Stratification X := Scheme.Stratification.ofNoetherianSpace 2
    ![(W : Set X), (W : Set X)ᶜ]
    (by intro a; fin_cases a
        · exact W.isOpen.isLocallyClosed
        · exact W.isOpen.isClosed_compl.isLocallyClosed)
    (by
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ W
      · exact Set.mem_iUnion.mpr ⟨0, hx⟩
      · exact Set.mem_iUnion.mpr ⟨1, hx⟩)
    (by intro a b hab; fin_cases a <;> fin_cases b <;>
      simp_all only [Function.onFun, Matrix.cons_val_zero,
      ne_eq, not_true_eq_false, Fin.zero_eta, Fin.isValue] <;>
      first | exact disjoint_compl_right | exact disjoint_compl_left)
    ![W.toScheme, Z]
    (fun a ↦ match a with
      | 0 => W.ι
      | 1 => i)
    (by intro a; fin_cases a <;> dsimp [i] <;> infer_instance)
    (by intro a; fin_cases a
        · exact W.range_ι
        · exact hZrange)
  refine ⟨S, ?_⟩
  intro a
  fin_cases a
  · exact hloc
  · exact hboundary

end AlgebraicGeometry
