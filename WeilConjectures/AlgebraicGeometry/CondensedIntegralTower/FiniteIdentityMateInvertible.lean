/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.GeometricTowerStatement
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Identity transition in the finite exceptional mate
Source: the normalization step of sk-prop-sp-integral-adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def fullLiftIdentityIso {C : Type*} [Category* C] (P : ObjectProperty C)
    (F : C ⥤ C) (h : ∀ K : P.FullSubcategory, P (F.obj K.obj)) (e : F ≅ 𝟭 C) :
    P.lift (P.ι ⋙ F) h ≅ 𝟭 P.FullSubcategory :=
  NatIso.ofComponents (fun K ↦ P.isoMk (e.app K.obj))
    (fun {K L} f ↦ by
      apply P.hom_ext
      exact e.hom.naturality f.hom)

set_option maxHeartbeats 1600000 in
-- Identity scalar comparisons unfold the dependent system-extension coordinates.
/-- The finite exceptional mate for an identity quotient transition is invertible.
Source: sk-prop-sp-integral-adjunction, normalization in its opening comparison;
sk-prop-sp-tower-geometric, identity transition
(blueprint: lem-sp-finite-identity-mate-invertible).

Proof: the scalar-tensor unit identifies both horizontal scalar functors with the
identity, so they are equivalences. The actual finite base-change square is an
isomorphism. Its right mate is therefore invertible. Apply the inverse adjunction
Hom bijection to identify that mate with the specified finite mate: both transpose
to the base-change component followed by the image of the given counit. This uses
the actual adjunction maps, without a choice of right adjoint. -/
theorem finiteMateIdentity {X Y : Scheme.{u}} {f : X ⟶ Y}
    (DX : Model l E X) (DY : Model l E Y) (c : Compactification f)
    (A : FiniteAdjunctions l E DX DY c) (n : ℕ) (K : FiniteCtf l E Y n) :
    IsIso (A.mate l E (Nat.le_refl n) K) := by
  let eX := fullLiftIdentityIso (finiteCtf l E X n)
    (SheafOfModules.systemDerivedTensor DX.scalar (rings l E X) (Nat.le_refl n))
    (A.scalarClosedX (Nat.le_refl n)) (DX.reductions.tensor.derivedUnit (rings l E X) n)
  let eY := fullLiftIdentityIso (finiteCtf l E Y n)
    (SheafOfModules.systemDerivedTensor DY.scalar (rings l E Y) (Nat.le_refl n))
    (A.scalarClosedY (Nat.le_refl n)) (DY.reductions.tensor.derivedUnit (rings l E Y) n)
  let : (A.scalarX l E (Nat.le_refl n)).IsEquivalence :=
    Functor.isEquivalence_of_iso eX.symm
  let : (A.scalarY l E (Nat.le_refl n)).IsEquivalence :=
    Functor.isEquivalence_of_iso eY.symm
  let α : TwoSquare (A.scalarX l E (Nat.le_refl n)) (A.support l E n)
      (A.support l E n) (A.scalarY l E (Nat.le_refl n)) :=
    TwoSquare.mk _ _ _ _ (A.baseChange (Nat.le_refl n)).hom
  let : IsIso α.natTrans := by dsimp only [α]; infer_instance
  let := isIso_mateEquiv_of_isEquivalence (A.adjunction n) (A.adjunction n) α
  have he : (mateEquiv (A.adjunction n) (A.adjunction n) α).app K =
      A.mate l E (Nat.le_refl n) K := by
    apply ((A.adjunction n).homEquiv _ _).symm.injective
    erw [FiniteAdjunctions.mate, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact mateEquiv_counit (A.adjunction n) (A.adjunction n) α K
  rw [← he]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
