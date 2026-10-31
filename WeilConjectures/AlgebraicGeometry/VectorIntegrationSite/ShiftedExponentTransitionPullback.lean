/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
import all WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateNormalizedCoherence
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition

/-! # Pullback of the shifted degree-one root transition

Source: finite Tate descent and normalized root pullback, Stacks 03PK and 03Q1.
(blueprint: lem-pur-shifted-exponent-transition-pullback).
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

private theorem single_square
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (S : C₀ ⥤ C) (T : D₀ ⥤ D) (U : C₀ ⥤ D₀) (F : C ⥤ D)
    (c : S ⋙ F ≅ U ⋙ T) {K L : C₀} {K' L' : D₀}
    (a : K ⟶ L) (b : U.obj L ⟶ L') (e : U.obj K ⟶ K') (d : K' ⟶ L')
    (h : U.map a ≫ b = e ≫ d) :
    F.map (S.map a) ≫ (c.hom.app L ≫ T.map b) =
      (c.hom.app K ≫ T.map e) ≫ T.map d := by
  have hn := c.hom.naturality a
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← T.map_comp, h, T.map_comp]

private theorem shift_square
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {K L : C} {K' L' : D}
    (a : K ⟶ L) (b : F.obj L ⟶ L') (c : F.obj K ⟶ K') (d : K' ⟶ L')
    (h : F.map a ≫ b = c ≫ d) (m : ℤ) :
    F.map (a⟦m⟧') ≫ ((F.commShiftIso m).hom.app L ≫ b⟦m⟧') =
      ((F.commShiftIso m).hom.app K ≫ c⟦m⟧') ≫ d⟦m⟧' := by
  have hn := (F.commShiftIso m).hom.naturality a
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, h, Functor.map_comp]

private theorem roots_pullback_value (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A m hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (m : Γ(Y, ⊤)))
    (U : Y.Etaleᵒᵖ) (z : (Y.rootsOfUnitySheaf m).obj.obj U) :
    Scheme.finiteTateEtaleRootValue X m _
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (t.roots f hY).hom).hom.app U z) =
      Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom
        (Scheme.finiteTateEtaleRootValue Y m U z) := by
  have h := congrArg
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
      (t.roots_normalization f hY)
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right] at h
  unfold Scheme.upperStarGmSheafToGmSheaf at h
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun g ↦ Additive.toMul ((g.hom.app U z).down)) h.symm

private theorem exponent_sheaf_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (l : Γ(Y, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr)
    (ts : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs) :
    (Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) f).map
        (exponentTransition l E n Y hY r s hrs hr hs 1).hom ≫
      (tr.line f (by simpa only [Nat.cast_pow] using hY.pow (r + 1))).hom =
    (ts.line f (by simpa only [Nat.cast_pow] using hY.pow (s + 1))).hom ≫
      (exponentTransition l E n X (by simpa using hY.map f.appTop.hom)
        r s hrs hr hs 1).hom := by
  let A := Scheme.finiteTateCoefficient l E n
  let hX : IsUnit (l : Γ(X, ⊤)) := by simpa using hY.map f.appTop.hom
  have hy := ((Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1
    Y hY r s hrs hr hs 1).exists.choose_spec.1
  have hx := ((Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1
    X hX r s hrs hr hs 1).exists.choose_spec.1
  with_unfolding_all
    change Scheme.IsFiniteTateEtaleTransition l E n Y r s hr hs 1
      (exponentTransition l E n Y hY r s hrs hr hs 1) at hy
  with_unfolding_all
    change Scheme.IsFiniteTateEtaleTransition l E n X r s hr hs 1
      (exponentTransition l E n X hX r s hrs hr hs 1) at hx
  obtain ⟨q, _, hq, _⟩ := Scheme.etale_transition_normalized l E n Y hY r s hrs hr hs 1
  apply ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply (Scheme.lineHomEquiv Y (l ^ (s + 1)) A hs _).injective
  ext U z
  simp only [Scheme.lineHomEquiv_generator]
  change ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      (tr.line f _).hom).hom.app U
      ((exponentTransition l E n Y hY r s hrs hr hs 1).hom.hom.app U
        (Scheme.finiteEtaleTateOneGenerator A (l ^ (s + 1)) Y hs U 1 z)) =
    (exponentTransition l E n X hX r s hrs hr hs 1).hom.hom.app _
      (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        (ts.line f _).hom).hom.app U
          (Scheme.finiteEtaleTateOneGenerator A (l ^ (s + 1)) Y hs U 1 z))
  have hyz := hy U 1 (fun _ ↦ z) (fun _ ↦ q.hom.app U z) (fun _ ↦ hq U z)
  change (exponentTransition l E n Y hY r s hrs hr hs 1).hom.hom.app U
      (Scheme.finiteEtaleTateOneGenerator A (l ^ (s + 1)) Y hs U 1 z) =
    Scheme.finiteEtaleTateOneGenerator A (l ^ (r + 1)) Y hr U 1
      (q.hom.app U z) at hyz
  rw [hyz, tr.line_normalization, ts.line_normalization]
  symm
  apply hx _ 1 (fun _ ↦ _) (fun _ ↦ _)
  intro i
  rw [roots_pullback_value, roots_pullback_value, hq, map_pow]
  rfl

private theorem shifted_line_square (A : Type (u + 1)) [CommRing A]
    (Nr Ns : ℕ) (hr : (Nr : A) = 0) (hs : (Ns : A) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport A Nr hr)
    (ts : Etale.OrdinaryFiniteTwistTransport A Ns hs)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hYr : IsUnit (Nr : Γ(Y, ⊤))) (hYs : IsUnit (Ns : Γ(Y, ⊤)))
    (a : Scheme.finiteEtaleTateLine Y Ns A hs ⟶ Scheme.finiteEtaleTateLine Y Nr A hr)
    (b : Scheme.finiteEtaleTateLine X Ns A hs ⟶ Scheme.finiteEtaleTateLine X Nr A hr)
    (h : (Etale.upperStar (ModuleCat.{u + 1} A) f).map a ≫ (tr.line f hYr).hom =
      (ts.line f hYs).hom ≫ b) :
    (Etale.ordinaryFinitePullback A f).map
        (((DerivedCategory.singleFunctor _ 0).map a)⟦(2 : ℤ)⟧') ≫
      (Etale.ordinaryFiniteShiftedLinePullback A Nr hr tr f hYr).hom =
    (Etale.ordinaryFiniteShiftedLinePullback A Ns hs ts f hYs).hom ≫
      ((DerivedCategory.singleFunctor _ 0).map b)⟦(2 : ℤ)⟧' := by
  have h₀ := single_square (Etale.ordinaryFiniteSingleFunctor A Y)
    (Etale.ordinaryFiniteSingleFunctor A X) (Etale.upperStar (ModuleCat.{u + 1} A) f)
    (Etale.ordinaryFinitePullback A f) (Etale.ordinaryFiniteSinglePullbackIso A f)
    a (tr.line f hYr).hom (ts.line f hYs).hom b h
  let : (Etale.ordinaryFinitePullback A f).CommShift ℤ :=
    Etale.commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  have h₂ := shift_square (Etale.ordinaryFinitePullback A f)
    ((Etale.ordinaryFiniteSingleFunctor A Y).map a) _ _
    ((Etale.ordinaryFiniteSingleFunctor A X).map b) h₀ (2 : ℤ)
  simpa only [Etale.ordinaryFiniteShiftedLinePullback_eq, Iso.trans_hom,
    Iso.app, Functor.mapIso_hom, Functor.map_comp,
    Etale.ordinaryFiniteSingleFunctor_eq, Etale.ordinaryFiniteLine,
    Etale.ordinaryFiniteDegreeZero, Category.assoc] using h₂

/-- The shifted degree-one root transition commutes with the normalized finite Tate
pullback. Source: finite Tate descent and normalized root pullback; Stacks 03PK, 03Q1.
(blueprint: lem-pur-shifted-exponent-transition-pullback).

Proof: the transition sends each root z to z raised to ell^(s-r), and the two
normalized root pullbacks send it to its underlying pulled-back unit. Pullback is
multiplicative, so these values agree. The root inclusion is monic and scalar-extended
root generators determine the coefficient-line map. The degree-zero embedding and
shift comparison are natural, so the sheaf square gives the displayed shifted square.
This includes equal exponents and the empty scheme; no coefficient flatness is used. -/
theorem shiftedExponentTransition_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (l : Γ(Y, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr)
    (ts : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs) :
    (Etale.ordinaryFinitePullback _ f).map
        (((DerivedCategory.singleFunctor _ 0).map
          (exponentTransition l E n Y hY r s hrs hr hs 1).hom)⟦(2 : ℤ)⟧') ≫
      (Etale.ordinaryFiniteShiftedLinePullback _ (l ^ (r + 1)) hr tr f
        (by simpa only [Nat.cast_pow] using hY.pow (r + 1))).hom =
    (Etale.ordinaryFiniteShiftedLinePullback _ (l ^ (s + 1)) hs ts f
        (by simpa only [Nat.cast_pow] using hY.pow (s + 1))).hom ≫
      (((DerivedCategory.singleFunctor _ 0).map
        (exponentTransition l E n X (by simpa using hY.map f.appTop.hom)
          r s hrs hr hs 1).hom)⟦(2 : ℤ)⟧') := by
  exact shifted_line_square _ _ _ hr hs tr ts f _ _ _ _
    (exponent_sheaf_pullback l E n f hY r s hrs hr hs tr ts)

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
