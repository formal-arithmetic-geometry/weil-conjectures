/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundarySourceEndpointTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryTargetEndpointTransport
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport

/-! The finite boundary square assembled after its two endpoint transports. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

abbrev source_endpoint_statement
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) : Prop :=
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let e := finiteBoundaryRestrictionUnderlying l T r n
  S.map (finiteQuotient l (ULift (Padic l)) T n) ≫
      S.map (e.inv.app (coefficient T (Arings l (ULift (Padic l)) T))) =
    S.map (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
      k.coefficientForget.inv.app (op n))

abbrev target_endpoint_statement
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) : Prop :=
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let e := finiteBoundaryRestrictionUnderlying l T r n
  S.map (finiteRootMap l (ULift (Padic l)) T n) ≫
      S.map ((finiteForget l (ULift (Padic l)) T n).mapIso
        (lineEvaluation l (ULift (Padic l)) c n)).inv ≫
      S.map (e.inv.app (lineModule l (ULift (Padic l)) c)) ≫
      S.map (k.lineForget.hom.app (op n)) ≫
      S.map (cartierProRootMap A (l ^ (n + 1)) hA T
        (pow_pos (Fact.out : l.Prime).pos _) hN) =
    S.map (cartierProRootMap A (l ^ (n + 1)) hA T
      (pow_pos (Fact.out : l.Prime).pos _) hN)

private theorem mapSingleArrow_ext {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasExt C] [HasExt D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} (n : ℕ) (b : Ext X Y n) :
    (b.mapExactFunctor F).hom = mapSingleArrow F (n : ℤ) b.hom := by
  simp only [Ext.mapExactFunctor_hom, ShiftedHom.map, mapSingleArrow, Category.assoc]

private theorem kummerComposite_hom {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [HasExt C]
    (s : ShortComplex C) (hs : s.ShortExact) {X : C} (b : Ext X s.X₃ 1) :
    (b.comp hs.extClass (rfl : 1 + 1 = 2)).hom = kummerComposite s hs b.hom := by
  simp only [kummerComposite, Ext.comp_hom, hs.extClass_hom, ShiftedHom.comp,
    Int.natCast_add, Int.natCast_one, shiftFunctorAdd'_eq_shiftFunctorAdd]

private theorem mapKummer {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasExt C] [HasExt D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (s : ShortComplex C) (hs : s.ShortExact) {X : C}
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧) :
    (((Ext.homEquiv.symm f).comp hs.extClass (rfl : 1 + 1 = 2)).mapExactFunctor F).hom =
      mapSingleArrow F (2 : ℤ) (kummerComposite s hs f) := by
  rw [mapSingleArrow_ext, kummerComposite_hom]
  exact congrArg (fun b ↦ mapSingleArrow F (2 : ℤ) (kummerComposite s hs b))
    (Ext.homEquiv.apply_symm_apply f)

/-- Turn normalization into an Ext equality before changing the derived localization. -/
private theorem finiteNormalization_ext
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (c : Chern l (ULift.{u} (Padic l)) T)
    (hc : FiniteChernNormalization l (ULift.{u} (Padic l)) c) (P : T.Pic) (n : ℕ) :
    (Ext.mk₀ (finiteQuotient l (ULift.{u} (Padic l)) T n)).comp
      (((Ext.homEquiv.symm (evaluatedChern l (ULift.{u} (Padic l)) c P n) :
        Ext.{u + 2} _ _ 2)).mapExactFunctor
        (finiteForget l (ULift.{u} (Padic l)) T n)) (zero_add 2) =
    ((((Ext.homEquiv.symm (lineBundleClass T P) : Ext.{u + 2} _ _ 1)).comp
      c.kummer.exact.extClass
      (rfl : 1 + 1 = 2)).mapExactFunctor (abEvaluation T n)).comp
        (Ext.mk₀ (finiteRootMap l (ULift.{u} (Padic l)) T n)) (add_zero 2) := by
  apply Ext.ext
  rcases hc P n with ⟨a, b, ha, hb, hab⟩
  rw [eq_of_heq ha, eq_of_heq hb] at hab
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, mapSingleArrow_inverseExt]
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, mapKummer]
  exact hab

/-- Assemble the finite boundary square once the source coefficient-one and
root endpoint equations have been supplied.  The assembly is the exact
single-arrow naturality square followed by the two endpoint substitutions; its
proof is independent of the coefficient and root calculations.
(blueprint: lem-diagonal-local-finite-boundary-assembly) -/
theorem finiteBoundary_transport_assembly
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (hc : FiniteChernNormalization l (ULift.{u} (Padic l)) c) (P : T.Pic)
    (hs : source_endpoint_statement l T c r k n)
    (ht : target_endpoint_statement l T c r k A n hA hN) :
    (finiteConeChernClass l T c r k A n hA hN
        (firstChern l (ULift.{u} (Padic l)) c P)).hom =
      (evaluatedIntegralKummerClass l T A n hA c.kummer hN P).hom := by
  classical
  let S := DerivedCategory.singleFunctor.{u + 1} (DiagonalAb T) 0
  let e : r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙
      diagonalForget l T ≅
      SpTowerShriek.ev l (ULift.{u} (Padic l)) T n ⋙
        finiteForget l (ULift.{u} (Padic l)) T n :=
    finiteBoundaryRestrictionUnderlying l T r n
  let theta := firstChern l (ULift.{u} (Padic l)) c P
  let t := cartierProRootMap A (l ^ (n + 1)) hA T
    (pow_pos (Fact.out : l.Prime).pos _) hN
  let R := r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙
    diagonalForget l T
  let : r.F.Additive := inferInstance
  let : ((evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n)).Additive := inferInstance
  let : (diagonalForget l T).Additive := diagonalForget_additive l T
  let : R.Additive := by infer_instance
  let : PreservesFiniteLimits R := by infer_instance
  let : PreservesFiniteColimits R := by infer_instance
  have he := mapSingleArrow_natIso
    (C := Systems T (Arings l (ULift.{u} (Padic l)) T)) (D := DiagonalAb T)
    (SpTowerShriek.ev l (ULift.{u} (Padic l)) T n ⋙
      finiteForget l (ULift.{u} (Padic l)) T n) R e.symm (2 : ℤ) theta
  have htheta : mapSingleArrow
      (SpTowerShriek.ev l (ULift.{u} (Padic l)) T n ⋙
        finiteForget l (ULift.{u} (Padic l)) T n) (2 : ℤ) theta =
      mapSingleArrow (finiteForget l (ULift.{u} (Padic l)) T n) (2 : ℤ)
          (evaluatedChern l (ULift.{u} (Padic l)) c P n) ≫
        (S.map ((finiteForget l (ULift.{u} (Padic l)) T n).map
          (lineEvaluation l (ULift.{u} (Padic l)) c n).inv))⟦(2 : ℤ)⟧' := by
    dsimp only [S, theta]
    unfold evaluatedChern
    rw [mapSingleArrow_postcompose, mapSingleArrow_composite]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  let : HasDerivedCategory.{u + 2} (Ab T) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2}
      (WeilConjectures.SemilinearSections.Mod (Scheme.ProEt.topology T)
        (SpTowerShriek.B l (ULift.{u} (Padic l)) T n)) := HasDerivedCategory.standard _
  have hab' := congrArg (fun x ↦ x.hom) (finiteNormalization_ext l T c hc P n)
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, mapSingleArrow_inverseExt,
    Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, mapKummer] at hab'
  simp only [Nat.reduceAdd, Nat.cast_ofNat] at hab'
  have hs' := hs
  have ht' := ht
  dsimp only [source_endpoint_statement] at hs'
  dsimp only [target_endpoint_statement] at ht'
  have hf : (finiteConeChernClass l T c r k A n hA hN theta).hom =
      S.map (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
        k.coefficientForget.inv.app (op n)) ≫ mapSingleArrow R (2 : ℤ) theta ≫
        (S.map (k.lineForget.hom.app (op n) ≫ t))⟦(2 : ℤ)⟧' := by
    unfold finiteConeChernClass
    exact Ext.homEquiv.apply_symm_apply _
  rw [hf]
  dsimp only [S, R, theta, t, e] at he
  rw [← hs']
  simp only [Category.assoc]
  erw [reassoc_of% he]
  rw [htheta]
  simp only [← (shiftFunctor (DerivedCategory (DiagonalAb T)) (2 : ℤ)).map_comp,
    Category.assoc]
  have hnorm := congrArg (fun f : S.obj ((abEvaluation T n).obj (integers T)) ⟶
      (S.obj ((finiteForget l (ULift.{u} (Padic l)) T n).obj
        (finiteLine l (ULift.{u} (Padic l)) T n)))⟦(2 : ℤ)⟧ ↦ f ≫
    (S.map ((finiteForget l (ULift.{u} (Padic l)) T n).map
      (lineEvaluation l (ULift.{u} (Padic l)) c n).inv) ≫
      S.map (e.inv.app (lineModule l (ULift.{u} (Padic l)) c)) ≫
      S.map (k.lineForget.hom.app (op n) ≫ t))⟦(2 : ℤ)⟧') hab'
  dsimp only [S, e] at hnorm
  simp only [Category.assoc] at hnorm
  erw [hnorm]
  simp only [Functor.map_comp]
  simp only [← (shiftFunctor (DerivedCategory (DiagonalAb T)) (2 : ℤ)).map_comp]
  erw [ht']
  unfold evaluatedIntegralKummerClass
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  exact congrArg (fun f ↦ f ≫
      (S.map (cartierProRootMap A (l ^ (n + 1)) hA T
        (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧')
    (mapKummer (abEvaluation T n) _ c.kummer.exact (lineBundleClass T P)).symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
