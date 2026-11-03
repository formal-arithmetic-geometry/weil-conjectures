/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import all WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact

/-! The ordinary strict-tower arrows before localization.
Source: current blueprint, tower-geometric Gluing paragraph.
(blueprint: lem-dla1-tower-open-cover-ordinary-sequence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

/-- Ordinary support, before passing to complexes.
Source: blueprint Gluing (blueprint: lem-dla1-tower-open-cover-ordinary-sequence). -/
abbrev ordinarySupport {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (o.geometry j).pull ⋙ (o.openOp j).extension

/-- The natural nested arrow on strict towers.
Source: blueprint Gluing (blueprint: lem-dla1-tower-open-cover-ordinary-sequence). -/
def ordinaryAlpha {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion k]
    (w : a ≫ j = k) : ordinarySupport l E b o k ⟶ ordinarySupport l E b o j :=
by
  let RU := (o.geometry j).pull
  let RW := (o.geometry k).pull
  let T := (o.geometry a).pull
  let SU := (o.openOp j).extension
  let c := o.ordinaryComp a j ≪≫
    eqToIso (congrArg (fun h ↦ (o.geometry h).pull) w)
  let t : RW ⟶ (RU ⋙ SU) ⋙ RW :=
    c.inv ≫ Functor.whiskerRight
      (Functor.whiskerLeft RU (o.openOp j).ordinaryAdjunction.unit) T ≫
      (Functor.associator RU SU (RU ⋙ T)).inv ≫
      Functor.whiskerLeft (RU ⋙ SU) c.hom
  exact
    { app := fun M ↦ ((o.openOp k).ordinaryAdjunction.homEquiv _ _).symm (t.app M)
      naturality := fun {M N} f ↦
        (o.openOp k).ordinaryAdjunction.homEquiv_naturality_right_square
          (RW.map f) (t.app N) (t.app M) ((RU ⋙ SU).map f) (t.naturality f) }

/-- A nested arrow followed by the counit is the overlap counit.
Source: blueprint Gluing (blueprint: lem-dla1-tower-open-cover-ordinary-sequence). -/
theorem ordinaryAlpha_counit {W U X : Scheme.{u}}
    (a : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion k]
    (w : a ≫ j = k) (M : SpTowerShriek.S l E X) :
    (ordinaryAlpha l E b o a j k w).app M ≫
      (o.openOp j).ordinaryAdjunction.counit.app M =
        (o.openOp k).ordinaryAdjunction.counit.app M := by
  simpa [ordinaryAlpha] using
    SheafOfModules.nestedTranspose_counit _ _ _ _ _
    (o.openOp j).ordinaryAdjunction (o.openOp k).ordinaryAdjunction
    (o.ordinaryComp a j ≪≫ eqToIso (congrArg (fun h ↦ (o.geometry h).pull) w)) M

/-- The nested arrow applied in each degree.
Source: blueprint Gluing (blueprint: lem-dla1-tower-open-cover-ordinary-sequence). -/
def ordinaryAlphaComplex {W U X : Scheme.{u}}
    (a : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion k]
    (w : a ≫ j = k) (K : CochainComplex (SpTowerShriek.S l E X) ℤ) :
    ((o.openOp k).extension.mapHomologicalComplex (.up ℤ)).obj
        (((o.geometry k).pull.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      ((o.openOp j).extension.mapHomologicalComplex (.up ℤ)).obj
        (((o.geometry j).pull.mapHomologicalComplex (.up ℤ)).obj K) where
  f n := (ordinaryAlpha l E b o a j k w).app (K.X n)
  comm' m n _ := ((ordinaryAlpha l E b o a j k w).naturality (K.d m n)).symm

/-- The signed short complex at a single strict tower.
Source: blueprint Gluing (blueprint: lem-dla1-tower-open-cover-ordinary-sequence). -/
def ordinarySequence {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW) (M : SpTowerShriek.S l E X) :
    ShortComplex (SpTowerShriek.S l E X) :=
  ShortComplex.mk
    (biprod.lift ((ordinaryAlpha l E b o aU jU jW wU).app M)
      (-((ordinaryAlpha l E b o aV jV jW wV).app M)))
    (biprod.desc ((o.openOp jU).ordinaryAdjunction.counit.app M)
      ((o.openOp jV).ordinaryAdjunction.counit.app M)) (by
    simp only [biprod.lift_desc, Preadditive.neg_comp,
      ordinaryAlpha_counit, add_neg_cancel])

/-- The signed overlap and counit sum on complexes have zero composite.
Source: blueprint Gluing (blueprint: lem-dla1-tower-open-cover-ordinary-sequence). -/
def ordinaryComplexSequence {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    (K : CochainComplex (SpTowerShriek.S l E X) ℤ) :
    ShortComplex (CochainComplex (SpTowerShriek.S l E X) ℤ) :=
  ShortComplex.mk
    (biprod.lift (ordinaryAlphaComplex l E b o aU jU jW wU K)
      (-ordinaryAlphaComplex l E b o aV jV jW wV K))
    (biprod.desc
      (((o.openOp jU).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app K)
      (((o.openOp jV).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app K)) (by
    rw [biprod.lift_desc]
    apply HomologicalComplex.Hom.ext
    funext n
    change _ + _ = 0
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.neg_f_apply, Preadditive.neg_comp,
      Adjunction.mapHomologicalComplex_counit_app_f]
    change (ordinaryAlpha l E b o aU jU jW wU).app (K.X n) ≫
        (o.openOp jU).ordinaryAdjunction.counit.app (K.X n) +
      -((ordinaryAlpha l E b o aV jV jW wV).app (K.X n) ≫
        (o.openOp jV).ordinaryAdjunction.counit.app (K.X n)) = 0
    rw [ordinaryAlpha_counit, ordinaryAlpha_counit, add_neg_cancel])

/-- A chain map induces a morphism of the specified short complexes.
Source: blueprint Gluing (blueprint: lem-dla1-tower-open-cover-ordinary-sequence). -/
def ordinaryComplexSequenceMap {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    {K L : CochainComplex (SpTowerShriek.S l E X) ℤ} (f : K ⟶ L) :
    ordinaryComplexSequence l E b o aU aV jU jV jW wU wV K ⟶
      ordinaryComplexSequence l E b o aU aV jU jV jW wU wV L where
  τ₁ := ((o.openOp jW).extension.mapHomologicalComplex (.up ℤ)).map
    (((o.geometry jW).pull.mapHomologicalComplex (.up ℤ)).map f)
  τ₂ := biprod.map
    (((o.openOp jU).extension.mapHomologicalComplex (.up ℤ)).map
      (((o.geometry jU).pull.mapHomologicalComplex (.up ℤ)).map f))
    (((o.openOp jV).extension.mapHomologicalComplex (.up ℤ)).map
      (((o.geometry jV).pull.mapHomologicalComplex (.up ℤ)).map f))
  τ₃ := f
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [ordinaryComplexSequence, Category.assoc,
        biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      apply HomologicalComplex.Hom.ext
      funext n
      exact (ordinaryAlpha l E b o aU jU jW wU).naturality (f.f n)
    · simp only [ordinaryComplexSequence, Category.assoc,
        biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
      apply HomologicalComplex.Hom.ext
      funext n
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply,
        ordinaryAlphaComplex, ordinarySupport, Functor.comp_map,
        Functor.mapHomologicalComplex_map_f,
        Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg Neg.neg ((ordinaryAlpha l E b o aV jV jW wV).naturality (f.f n))
  comm₂₃ := by
    apply biprod.hom_ext'
    · simpa only [ordinaryComplexSequence, Category.assoc, Functor.comp_map, Functor.id_map,
        biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc] using
        ((o.openOp jU).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.naturality f
    · simpa only [ordinaryComplexSequence, Category.assoc, Functor.comp_map, Functor.id_map,
        biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc] using
        ((o.openOp jV).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.naturality f

end AlgebraicGeometry.ProEtale.TowerOpenCover
