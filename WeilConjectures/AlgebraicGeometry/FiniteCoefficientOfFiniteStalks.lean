/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.ConstructibleFiniteStalkAnnihilatorDetection
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Finite coefficients of a finite-stalk module sheaf
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite module has a finite quotient of its coefficient ring by its annihilator. -/
private theorem finite_quotient_annihilator (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Finite M] :
    Finite (R ⧸ Module.annihilator R M) := by
  have : Finite (AddMonoid.End M) :=
    Finite.of_injective (fun f : AddMonoid.End M ↦ (f : M → M)) DFunLike.coe_injective
  exact Finite.of_injective (RingHom.kerLift (Module.toAddMonoidEnd R M))
    (RingHom.kerLift_injective _)

/-- The canonical sectionwise annihilator of a constructible module sheaf with finite
stalks has finite quotient. -/
theorem finite_quotient_section_annihilator_of_finite_stalks
    (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Finite ((((pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F)) :
    Finite (Λ ⧸ ⨅ U : X.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U)) := by
  classical
  obtain ⟨n, x, hx⟩ := exists_finite_stalk_annihilator_detection Λ F hF
  let M (i : Fin n) :=
    (((pointSmallEtale (X.algClosurePoint (x i))).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F
  have (i : Fin n) : Finite (M i) := hfin _ (X.algClosurePoint (x i))
  have : Finite (Λ ⧸ Module.annihilator Λ (∀ i : Fin n, M i)) :=
    finite_quotient_annihilator Λ (∀ i : Fin n, M i)
  have hle : Module.annihilator Λ (∀ i : Fin n, M i) ≤
      ⨅ U : X.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U) := by
    rw [Module.annihilator_pi]
    exact hx
  exact Finite.of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)

end AlgebraicGeometry.Scheme
