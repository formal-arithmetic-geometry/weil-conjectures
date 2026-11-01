/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.AlgebraicGeometry.NativeCoefficientTateTwist
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTateLineInvertible

/-! # Oriented perfect duality with ordinary condensed coefficients

Source: the current blueprint, sec-six-functors/sk-thm-sf-dual-perfect, statement
and proof (blueprint: sk-thm-sf-dual-perfect).

The categorical argument works for any invertible oriented line in a closed symmetric
monoidal category. Its condensed specialization below uses the actual ordinary derived
category of modules over the pulled-back condensed coefficient ring. In particular its
Qbar line is the upstream native Tate twist, rather than a common-stage coefficient object.
The two recorded closed-model maps remain available to existing consumers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance] DerivedCategory.symmetricCategory'
universe u a b
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- Oriented perfect duality for the chosen closed structure. The inverse of theta,
its evaluation normalization, and the cancellation arrow are specified, so the final
equation compares the canonical biduality maps. The equivalence restricts the actual
contravariant internal-Hom functor.
Source: current blueprint theorem and proof (blueprint: sk-thm-sf-dual-perfect). -/
def SfNativeOrientedPerfectDuality {B : Type a} [Category.{b} B]
    [MonoidalCategory B] [MonoidalClosed B] [SymmetricCategory B]
    {L W : B} (gamma : L ≅ W) : Prop :=
  ∃ theta : internalHom.flip.obj W ≅ internalHom.flip.obj (𝟙_ B) ⋙ tensorRight L,
    (∀ K : B, (theta.app (op K)).inv =
      ihomTensorToIhom K (𝟙_ B) L ≫ (ihom K).map (λ_ L).hom ≫
        (ihom K).map gamma.hom) ∧
    (∀ K : B, K ◁ (theta.app (op K)).hom ≫ (α_ _ _ _).inv ≫
      (ihom.ev K).app (𝟙_ B) ▷ L ≫ (λ_ L).hom =
        (ihom.ev K).app W ≫ gamma.inv) ∧
    (∃ e : (ObjectProperty.FullSubcategory (IsDualizable (C := B)))ᵒᵖ ≌
        ObjectProperty.FullSubcategory (IsDualizable (C := B)),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IsDualizable (C := B)) ≅
        (ObjectProperty.ι (IsDualizable (C := B))).op ⋙ internalHom.flip.obj W)) ∧
    (∀ (K : B), IsDualizable K → IsDualizable ((ihom K).obj W)) ∧
    (∀ (K : B), IsDualizable K → IsIso (toIhomIhom W K)) ∧
    (∀ K : B, ∃ c : (ihom ((ihom K).obj (𝟙_ B))).obj (𝟙_ B) ≅
        (ihom ((ihom K).obj (𝟙_ B) ⊗ L)).obj L,
      c.hom = ihomUnitToIhomTensor ((ihom K).obj (𝟙_ B)) L ∧
      toIhomIhom W K ≫ (pre (theta.app (op K)).inv).app W ≫
        (ihom ((ihom K).obj (𝟙_ B) ⊗ L)).map gamma.inv ≫ c.inv =
          toIhomIhomUnit K)

/-- Duality into an oriented invertible line is the twisted coefficient dual, naturally,
and is an anti-equivalence on perfect (dualizable) objects, with coefficient biduality.
Source: current blueprint dual-perfect proof.
Proof: use the inverse of the evaluation-transpose twist comparison after applying Hom
to the inverse orientation. Its naturality and evaluation normalization follow by
uncurrying. The inverse line gives canonical Hom cancellation. Under that cancellation,
the double-dual transpose is coefficient biduality; hence it is invertible on dualizable
objects. Restrict the internal-Hom functor and its canonical double-dual natural map to
obtain the anti-equivalence. No assumption on a base scheme is used.
(blueprint: sk-thm-sf-dual-perfect). -/
theorem sfOrientedInvertibleLineDuality {B : Type a} [Category.{b} B]
    [MonoidalCategory B] [MonoidalClosed B] [SymmetricCategory B]
    {L W : B} (gamma : L ≅ W) (hL : IsInvertible L) :
    SfNativeOrientedPerfectDuality gamma := by
  refine ⟨ihomFlipIsoIhomUnitTensor gamma hL,
    ihomIsoIhomUnitTensor_inv gamma hL,
    whiskerLeft_ihomIsoIhomUnitTensor_hom_comp gamma hL, ?_,
    fun _ hK ↦ isDualizable_ihom_obj gamma hL hK,
    fun _ hK ↦ isIso_toIhomIhom_of_isDualizable gamma hL hK, ?_⟩
  · refine ⟨dualizableIhomEquivalence gamma hL, ⟨?_⟩⟩
    exact Iso.refl _
  · intro K
    have := isIso_ihomUnitToIhomTensor ((ihom K).obj (𝟙_ B)) hL
    refine ⟨asIso (ihomUnitToIhomTensor ((ihom K).obj (𝟙_ B)) L), rfl, ?_⟩
    change toIhomIhom W K ≫ (ihomIhomIsoIhomIhomUnit gamma hL K).hom = _
    exact toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom gamma hL K

/-- Oriented perfect duality over any commutative condensed coefficient ring under Z_l.
All coefficient categories are ordinary derived categories of modules over the pulled-back
ring. W can be the exceptional image of the base unit for any base scheme. In particular
n = 2d is the smooth relative orientation in the paper; the statement here is stronger,
allowing every shift and every signed power.
Source: current blueprint theorem and its proof.
Proof: scalar extension of the actual integral Tate module gives a locally rank-one
coefficient line. Its signed powers and all shifts are invertible in the ordinary derived
category. Apply the evaluation-normalized categorical theorem. No choice of a finite
coefficient stage, adic system, rationalization or common-stage presentation enters.
(blueprint: sk-thm-sf-dual-perfect). -/
theorem sfOrientedPerfectDuality
    (X : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (phi : Profinite.continuousMapRingObj ℤ_[ell] ⟶ Λ) [IsMonHom phi]
    (hell : IsUnit (ell : Γ(X, ⊤))) (d n : ℤ)
    {W : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (ProEtale.condensedRingObj Λ X))}
    (gamma : (ProEtale.sfCondensedTateTwistDerived X ell Λ phi d) ⟦n⟧ ≅ W) :
    SfNativeOrientedPerfectDuality gamma :=
  sfOrientedInvertibleLineDuality gamma
    (ProEtale.CondensedRing.nativeShiftedCoefficientTateTwistInvertible
      X ell Λ phi hell d n)

/-- The relative (and, for a structure map, absolute) dual-perfect theorem in the ordinary
native condensed Qbar coefficient category. The orientation is a hypothesis, just as in
the paper: W is the exceptional image of the base coefficient unit. The conclusion is
valid for any such W, so it adds no hypothesis on the base or on a purity construction.
Source: current blueprint theorem, with Lambda = the pulled-back condensed Qbar ring.
Proof: the shifted native Tate line is invertible, using a compatible-root cover and
ordinary derived tensor. Apply the general evaluation-normalized duality theorem. For
a smooth map of relative dimension d, take n = 2d and W = Rf! Lambda; for its structure
map this is W = omega_X. All comparisons use the signed derived symmetry.
(blueprint: sk-thm-sf-dual-perfect). -/
theorem sfCondensedOrientedPerfectDuality
    (X : AlgebraicGeometry.Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : IsUnit (ell : Γ(X, ⊤))) (d n : ℤ)
    {W : DerivedCategory
      (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1})
        (AlgebraicGeometry.ProEtale.condensedRingObj
          (Profinite.padicAlgClRingObj ell) X))}
    (gamma : (AlgebraicGeometry.ProEtale.tateTwistDerived X ell d) ⟦n⟧ ≅ W) :
    SfNativeOrientedPerfectDuality gamma :=
  sfOrientedInvertibleLineDuality gamma
    (AlgebraicGeometry.ProEtale.CondensedRing.nativeShiftedTateTwistInvertible
      X ell hell d n)

end WeilConjectures
