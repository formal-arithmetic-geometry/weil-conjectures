/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneLocalData
import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer

/-! # Kummer classes of Laurent monomials

Source: Milne, Lectures on Etale Cohomology, Section 14, Proposition 14.3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

attribute [local implicit_reducible] Functor.mapHomologicalComplex
  HomologicalComplex.homologyFunctor


private def kummerAddHom (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F) :
    Additive Γ(W.left, ⊤)ˣ →+
      ((sections X.smallEtaleTopology A W).rightDerived 1).obj F := by
  letI := (Etale.module_cohomology_conventions A X).2.1 F W 1
  let up : Additive Γ(W.left, ⊤)ˣ →+ X.gmSheaf.obj.obj (op W) :=
    { toFun := ULift.up
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let s := (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W X.gmSheaf).symm
  exact (asIso ((Etale.moduleEvaluationForgetComparison A X W 1).app F)).inv.hom.comp
    (((evaluationExt X W 1).inv.app ((Etale.moduleAbelianForget A X).obj F)).hom.comp
      (((Abelian.Ext.mk₀ f).postcomp _ (add_zero 1)).comp
        (((X.kummerSequence_shortExact m hm).extClass.postcomp _ (zero_add 1)).comp
          (Abelian.Ext.addEquiv₀.symm.toAddMonoidHom.comp
            (s.toAddMonoidHom.comp up)))))

/-- Scalar units are m-th powers over an algebraically closed field. The Kummer
class of a Laurent monomial therefore records just its integral exponent.
Source: Milne, Section 14, Proposition 14.3; blueprint local calculation, Step 5.

Proof: the represented section map, Yoneda composition with the Kummer extension,
and both canonical cohomology comparisons are additive. Thus the Kummer class is
an additive homomorphism from multiplicative units. Choose an m-th root d of c in
Omega. The class of its constant pullback raised to m is m times its class, hence
zero because m annihilates A and every A-module. Integer powers of the coordinate
map to integer multiples, including negative powers and the zeroth power.
(blueprint: lem-pur-rank-one-kummer-monomial). -/
theorem kummer_monomial
    (A : Type (u + 1)) [CommRing A] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (m : ℕ) (hmpos : 0 < m) (hA : (m : A) = 0)
    (F : Sheaf (Line (Spec (.of Ω))).smallEtaleTopology (ModuleCat.{u + 1} A))
    (hm : IsUnit (m : Γ(Line (Spec (.of Ω)), ⊤)))
    (f : (Line (Spec (.of Ω))).rootsOfUnitySheaf m ⟶
      (Etale.moduleAbelianForget A (Line (Spec (.of Ω)))).obj F)
    (c : Ωˣ) (r : ℤ) :
    kummerClass A _ (openObject (Spec (.of Ω))) F m hm f
        (constantUnit Ω c * coordinateUnit (Spec (.of Ω)) ^ r) =
      r • kummerClass A _ (openObject (Spec (.of Ω))) F m hm f
        (coordinateUnit (Spec (.of Ω))) := by
  let κ := kummerAddHom A (Line (Spec (.of Ω))) (openObject (Spec (.of Ω))) F m hm f
  obtain ⟨d, hd⟩ := AffineSpace.exists_pow_eq_units_of_isAlgClosed hmpos c
  have hconst : κ (Additive.ofMul (constantUnit Ω c)) = 0 := by
    have heq : constantUnit Ω c = constantUnit Ω d ^ m := by
      rw [← hd]
      exact map_pow _ _ _
    rw [heq]
    change κ (m • Additive.ofMul (constantUnit Ω d)) = 0
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul A, hA, zero_smul]
  change κ (Additive.ofMul (constantUnit Ω c) +
    r • Additive.ofMul (coordinateUnit (Spec (.of Ω)))) =
      r • κ (Additive.ofMul (coordinateUnit (Spec (.of Ω))))
  calc
    _ = κ (Additive.ofMul (constantUnit Ω c)) +
        κ (r • Additive.ofMul (coordinateUnit (Spec (.of Ω)))) := κ.map_add _ _
    _ = 0 + κ (r • Additive.ofMul (coordinateUnit (Spec (.of Ω)))) :=
      congrArg (fun z ↦ z + κ (r • Additive.ofMul (coordinateUnit (Spec (.of Ω))))) hconst
    _ = κ (r • Additive.ofMul (coordinateUnit (Spec (.of Ω)))) := zero_add _
    _ = _ := κ.map_zsmul _ _

end WeilConjectures.PurityFiniteSetting.RankOne
