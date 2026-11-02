/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceGeometricData
import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import all WeilConjectures.AlgebraicGeometry.Exact.ExactCondensedExchangeComparison

/-! # Geometric composition and tensor compatibility for scalar pullback

Source: scalar-six pullback, composition and balanced tensor normalization.
(blueprint: lem-pur-field-composition-source-geometry). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Scheme
open CategoryTheory.Functor.OplaxMonoidal
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
attribute [local irreducible] DerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private def scalarPullTransport
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {F I : B ⥤ A} {F' I' : B' ⥤ A'} (U : A ⥤ A') (V : B ⥤ B')
    (e : F ≅ I) (e' : F' ≅ I') (t : I ⋙ U ≅ V ⋙ I') : F ⋙ U ≅ V ⋙ F' :=
  Functor.isoWhiskerRight e U ≪≫ t ≪≫ (Functor.isoWhiskerLeft V e').symm

private theorem scalarPullComposition
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {F I : B ⥤ A} {G J : C ⥤ B} {H K : C ⥤ A}
    {F' I' : B' ⥤ A'} {G' J' : C' ⥤ B'} {H' K' : C' ⥤ A'}
    (U : A ⥤ A') (V : B ⥤ B') (W : C ⥤ C')
    (ef : F ≅ I) (eg : G ≅ J) (eh : H ≅ K)
    (ef' : F' ≅ I') (eg' : G' ≅ J') (eh' : H' ≅ K')
    (kf : H ≅ G ⋙ F) (ki : K ≅ J ⋙ I)
    (kf' : H' ≅ G' ⋙ F') (ki' : K' ≅ J' ⋙ I')
    (tf : I ⋙ U ≅ V ⋙ I') (tg : J ⋙ V ≅ W ⋙ J') (th : K ⋙ U ≅ W ⋙ K')
    (hn : ∀ N, kf.hom.app N ≫ ef.hom.app (G.obj N) ≫ I.map (eg.hom.app N) =
      eh.hom.app N ≫ ki.hom.app N)
    (hn' : ∀ N, kf'.hom.app N ≫ ef'.hom.app (G'.obj N) ≫ I'.map (eg'.hom.app N) =
      eh'.hom.app N ≫ ki'.hom.app N)
    (ht : ∀ N, U.map (ki.hom.app N) ≫ tf.hom.app (J.obj N) ≫
      I'.map (tg.hom.app N) = th.hom.app N ≫ ki'.hom.app (W.obj N)) (N : C) :
    U.map (kf.hom.app N) ≫ (scalarPullTransport U V ef ef' tf).hom.app (G.obj N) ≫
        F'.map ((scalarPullTransport V W eg eg' tg).hom.app N) =
      (scalarPullTransport U W eh eh' th).hom.app N ≫ kf'.hom.app (W.obj N) := by
  apply (cancel_mono
    (ef'.hom.app (G'.obj (W.obj N)) ≫ I'.map (eg'.hom.app (W.obj N)))).mp
  have hf := ef'.hom.naturality ((scalarPullTransport V W eg eg' tg).hom.app N)
  simp only [Functor.comp_obj] at hf
  simp only [Category.assoc]
  rw [reassoc_of% hf, hn']
  simp only [scalarPullTransport, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Functor.map_comp]
  simp only [← I'.map_comp_assoc]
  simp only [I'.map_comp, Category.assoc]
  have htfn := tf.hom.naturality (eg.hom.app N)
  simp only [Functor.comp_map, Functor.comp_obj] at htfn
  rw [← reassoc_of% htfn]
  simp only [← U.map_comp_assoc]
  rw [hn]
  simp only [U.map_comp, Category.assoc]
  rw [← I'.map_comp, Iso.inv_hom_id_app, reassoc_of% ht]
  dsimp only [Functor.comp_obj]
  erw [I'.map_id, Category.comp_id]

set_option maxHeartbeats 1600000 in
-- Transport three total-derived pullbacks through their exact presentations.
/-- Scalar pullback respects the geometric compositor and the derived tensorator.
No Tate line, twist, compactification or trace occurs in these equations.
Source: scalar-six pullback (1), (3), and its balanced tensor construction.
(blueprint: lem-pur-field-composition-source-geometry).

Proof in words. First prove a categorical transport calculation for three
compatible pullback isomorphisms. Cancel the target exact comparison, use its
naturality, substitute the two compositor normalizations and the exact scalar
composition square, and cancel the inverse comparisons. Instantiate it with
the native scalarSixPullbackData theta maps and their thetaNormalization.
The total_comp_normalization theorem identifies both coefficient-side
compositors. This proves the first component. The second component is precisely
fieldCompositionSourceTensor, applied with the displayed flatness instances. -/
theorem fieldCompositionSourceGeometry
    (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI := fieldCompScalarMonoidal ell a X
    letI := fieldCompScalarMonoidal ell a Y
    (∀ K : c.derived ell Z,
      (scalarSixChange a X).map
          ((CondensedRing.leftDerivedUpperStarComp (c.obj ell) f g).hom.app K) ≫
        (fieldCompScalarPull ell a f).hom.app ((actualPull (c.obj ell) g).obj K) ≫
        (actualPull (c'.obj ell) f).map ((fieldCompScalarPull ell a g).hom.app K) =
      (fieldCompScalarPull ell a (f ≫ g)).hom.app K ≫
        (CondensedRing.leftDerivedUpperStarComp (c'.obj ell) f g).hom.app
          ((scalarSixChange a Z).obj K)) ∧
    (∀ N L : c.derived ell Y,
      (fieldCompScalarPull ell a f).hom.app (N ⊗ L) ≫
        (actualPull (c'.obj ell) f).map (δ (scalarSixChange a Y) N L) ≫
        δ (actualPull (c'.obj ell) f)
          ((scalarSixChange a Y).obj N) ((scalarSixChange a Y).obj L) =
      (scalarSixChange a X).map (δ (actualPull (c.obj ell) f) N L) ≫
        δ (scalarSixChange a X) ((actualPull (c.obj ell) f).obj N)
          ((actualPull (c.obj ell) f).obj L) ≫
        ((fieldCompScalarPull ell a f).hom.app N ⊗ₘ
          (fieldCompScalarPull ell a f).hom.app L)) := by
  constructor
  · intro K
    obtain ⟨C⟩ := scalarSixPullbackData_exists.{u}
    have hθ {U V : Scheme.{u}} (v : U ⟶ V) : scalarPullbackIso a v = C.theta a v := by
      apply Iso.ext
      exact (C.thetaNormalization a v).symm
    have h := scalarPullComposition
      (scalarSixChange a X) (scalarSixChange a Y) (scalarSixChange a Z)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) f)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) g)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) (f ≫ g))
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c'.obj ell) f)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c'.obj ell) g)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c'.obj ell) (f ≫ g))
      (CondensedRing.leftDerivedUpperStarComp (c.obj ell) f g)
      (RootCoordinateFace.upperComp (c.obj ell) f g)
      (CondensedRing.leftDerivedUpperStarComp (c'.obj ell) f g)
      (RootCoordinateFace.upperComp (c'.obj ell) f g)
      (C.theta a f) (C.theta a g) (C.theta a (f ≫ g))
      (total_comp_normalization (c.obj ell) f g)
      (total_comp_normalization (c'.obj ell) f g)
      (fun N ↦ (C.composition a f g N).symm) K
    simpa only [scalarPullTransport, fieldCompScalarPull, hθ] using h
  · exact fieldCompositionSourceTensor ell a f

end AlgebraicGeometry.ProEtale.PurityTransport
