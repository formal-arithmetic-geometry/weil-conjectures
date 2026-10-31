/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ShiftedExponentTransitionPullback
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition

/-! # Pullback of the ordered root transition

Source: finite Tate descent and the canonical Tate identifications in vector integration.
(blueprint: lem-pur-ordered-tate-exponent-pullback)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open MonoidalCategory
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.rootsOfUnitySheaf Scheme.finiteEtaleTateTwist
  Etale.ordinaryFiniteDegreeZero
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem unit_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K : C} {L : D} (b : F.obj K ⟶ L) :
    F.map (𝟙 K) ≫ b = b ≫ 𝟙 L := by
  calc
    F.map (𝟙 K) ≫ b = 𝟙 (F.obj K) ≫ b :=
      congrArg (fun q ↦ q ≫ b) (F.map_id K)
    _ = b := Category.id_comp b
    _ = b ≫ 𝟙 L := (Category.comp_id b).symm

private theorem tensor_square
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) {K L K' L' : C} {M N M' N' : D}
    (a : K ⟶ K') (b : L ⟶ L') (c : F.obj K' ⟶ M') (d : F.obj L' ⟶ N')
    (e : F.obj K ⟶ M) (g : F.obj L ⟶ N) (i : M ⟶ M') (j : N ⟶ N')
    (δ : F.obj (K ⊗ L) ⟶ F.obj K ⊗ F.obj L)
    (δ' : F.obj (K' ⊗ L') ⟶ F.obj K' ⊗ F.obj L')
    (hn : δ ≫ (F.map a ⊗ₘ F.map b) = F.map (a ⊗ₘ b) ≫ δ')
    (ha : F.map a ≫ c = e ≫ i) (hb : F.map b ≫ d = g ≫ j) :
    F.map (a ⊗ₘ b) ≫ (δ' ≫ (c ⊗ₘ d)) =
      (δ ≫ (e ⊗ₘ g)) ≫ (i ⊗ₘ j) := by
  rw [← Category.assoc, ← hn, Category.assoc, tensorHom_comp_tensorHom, ha, hb]
  rw [← tensorHom_comp_tensorHom, ← Category.assoc]

private theorem comparison_zero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    baseExponentComparison l E n T hT r s hrs hr hs 0 = Iso.refl _ := by
  with_unfolding_all rfl

private theorem comparison_succ
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    baseExponentComparison l E n T hT r s hrs hr hs (d + 1) =
      Etale.ordinaryFiniteTensorRightMapIso _ T
        (baseExponentComparison l E n T hT r s hrs hr hs d)
        ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
          (exponentTransition l E n T hT r s hrs hr hs 1))) := by
  with_unfolding_all rfl

private theorem comparison_succ_hom
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (baseExponentComparison l E n T hT r s hrs hr hs (d + 1)).hom =
      (baseExponentComparison l E n T hT r s hrs hr hs d).hom ⊗ₘ
        (shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map
          (exponentTransition l E n T hT r s hrs hr hs 1).hom) := by
  simp only [comparison_succ, Etale.tensor_mapIso_hom, Functor.mapIso_hom]
  rfl

private theorem ordered_square (A : Type (u + 1)) [CommRing A]
    (Nr Ns : ℕ) (hr : (Nr : A) = 0) (hs : (Ns : A) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport A Nr hr)
    (ts : Etale.OrdinaryFiniteTwistTransport A Ns hs)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hYr : IsUnit (Nr : Γ(Y, ⊤))) (hYs : IsUnit (Ns : Γ(Y, ⊤)))
    (cY : (Etale.ordinaryFiniteLine A Ns hs Y)⟦(2 : ℤ)⟧ ⟶
      (Etale.ordinaryFiniteLine A Nr hr Y)⟦(2 : ℤ)⟧)
    (cX : (Etale.ordinaryFiniteLine A Ns hs X)⟦(2 : ℤ)⟧ ⟶
      (Etale.ordinaryFiniteLine A Nr hr X)⟦(2 : ℤ)⟧)
    (aY : ∀ d, Etale.affineLinearBaseCoefficient A Ns hs Y d ⟶
      Etale.affineLinearBaseCoefficient A Nr hr Y d)
    (aX : ∀ d, Etale.affineLinearBaseCoefficient A Ns hs X d ⟶
      Etale.affineLinearBaseCoefficient A Nr hr X d)
    (hy0 : aY 0 = 𝟙 (Etale.affineLinearBaseCoefficient A Ns hs Y 0))
    (hx0 : aX 0 = 𝟙 (Etale.affineLinearBaseCoefficient A Ns hs X 0))
    (hyS : ∀ d, aY (d + 1) = aY d ⊗ₘ cY)
    (hxS : ∀ d, aX (d + 1) = aX d ⊗ₘ cX)
    (hl : (Etale.ordinaryFinitePullback A f).map cY ≫
        (Etale.ordinaryFiniteShiftedLinePullback A Nr hr tr f hYr).hom =
      (Etale.ordinaryFiniteShiftedLinePullback A Ns hs ts f hYs).hom ≫ cX) (d : ℕ) :
    (Etale.ordinaryFinitePullback A f).map (aY d) ≫
        (Etale.vectorIntegrationBaseCoefficientPullback A Nr hr tr f hYr d).hom =
      (Etale.vectorIntegrationBaseCoefficientPullback A Ns hs ts f hYs d).hom ≫ aX d := by
  induction d with
  | zero =>
    rw [hy0, hx0]
    change (Etale.ordinaryFinitePullback A f).map (𝟙 (Etale.ordinaryFiniteUnit A Y)) ≫
        (Etale.ordinaryFiniteUnitPullback A f).hom =
      (Etale.ordinaryFiniteUnitPullback A f).hom ≫ 𝟙 (Etale.ordinaryFiniteUnit A X)
    exact unit_square (Etale.ordinaryFinitePullback A f) _
  | succ d ih =>
    rw [hyS, hxS, Etale.coefficient_succ_hom, Etale.coefficient_succ_hom]
    exact tensor_square (Etale.ordinaryFinitePullback A f) _ _ _ _ _ _ _ _ _ _
      (Etale.leftDerivedUpperStarTensorComparison_naturality
        (ModuleCat.{u + 1} A) f _ _) ih hl

/-- Pullback of the ordered shifted Tate coefficient commutes with root transition.
This is a coefficient equation, with no compact support, trace, bundle or frame.
Source: finite Tate site descent, root and pullback normalization; vector integration,
canonical Tate identifications; Stacks 03PK and 03Q1.
(blueprint: lem-pur-ordered-tate-exponent-pullback).

Proof: at degree one the normalized root pullback maps commute with the power map:
both send a root z to the pullback of z raised to ell^(s-r). Cancel the monomorphism
of the roots sheaf into the units sheaf to verify this square. Scalar extension
preserves this equality: transpose under the pullback adjunction and evaluate on
pure generators a tensor z, which generate the scalar-extended sheaf after
sheafification. The defining normalization of finite Tate descent identifies its
exponentTransition with this root-power map. The normalized transports tr and ts
have exactly these root and generator formulas, so the argument applies to both.
Apply the degree-zero derived embedding and the shift comparison; their naturality
gives the square for shifted lines. Induct on d. At zero both transitions are the
identity and both pullback comparisons are the constant-unit comparison. At a
successor, expand baseExponentComparison and vectorIntegrationBaseCoefficientPullback.
Naturality of the derived tensor pullback moves the two coefficient maps past that
comparison. Apply the induction hypothesis to the first factor and the shifted-line
square to the second factor, then use bifunctoriality of tensor. This is the stated
square. No flatness of the finite coefficient ring is used; d=0, empty schemes,
equal exponents and ramified coefficient quotients are included. -/
theorem baseExponentComparison_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (l : Γ(Y, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr)
    (ts : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs) (d : ℕ) :
    (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n) f).map
        (baseExponentComparison l E n Y hY r s hrs hr hs d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback _ (l ^ (r + 1)) hr tr f
        (by simpa only [Nat.cast_pow] using hY.pow (r + 1)) d).hom =
    (Etale.vectorIntegrationBaseCoefficientPullback _ (l ^ (s + 1)) hs ts f
        (by simpa only [Nat.cast_pow] using hY.pow (s + 1)) d).hom ≫
      (baseExponentComparison l E n X
        (by simpa using hY.map f.appTop.hom) r s hrs hr hs d).hom := by
  let A := Scheme.finiteTateCoefficient l E n
  let hX : IsUnit (l : Γ(X, ⊤)) := by simpa using hY.map f.appTop.hom
  have hl := shiftedExponentTransition_pullback l E n f hY r s hrs hr hs tr ts
  exact ordered_square A (l ^ (r + 1)) (l ^ (s + 1)) hr hs tr ts f
    (by simpa only [Nat.cast_pow] using hY.pow (r + 1))
    (by simpa only [Nat.cast_pow] using hY.pow (s + 1)) _ _
    (fun e ↦ (baseExponentComparison l E n Y hY r s hrs hr hs e).hom)
    (fun e ↦ (baseExponentComparison l E n X hX r s hrs hr hs e).hom)
    (by rw [comparison_zero]; rfl) (by rw [comparison_zero]; rfl)
    (comparison_succ_hom l E n Y hY r s hrs hr hs)
    (comparison_succ_hom l E n X hX r s hrs hr hs) hl d

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
