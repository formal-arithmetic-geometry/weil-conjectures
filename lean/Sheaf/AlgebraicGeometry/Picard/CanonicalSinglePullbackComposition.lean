/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import Sheaf.AlgebraicGeometry.Picard.HomotopySinglePullbackComposition

/-! # Single-module comparison and composition of two pullbacks

Source: Stacks Project, Tag 0D5S, and the defining left-derived lift factorization.
(blueprint: lem-pc-canonical-single-pullback-composition).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 200000 in
-- The selected derived counits have large dependent types.
/-- Compatibility with composition of two morphisms, before comparing square paths.
Source: Stacks Project, Tag 0D5S, and `Functor.leftDerived_fac_app` applied to the
factorization in `exists_derivedPullbackComposition`.
(blueprint: lem-pc-canonical-single-pullback-composition).

Proof: Write ε for the chosen derived counits and t for the unique left-adjoint
isomorphism from tensor pullback to ordinary pullback. Evaluate the defining
leftDerivedLift factorization at the single complex of N. Its right side is
Lf*(ε_g) followed by ε_f at the termwise g-pullback and the termwise tensor
composition isomorphism. Postcompose with the single-complex comparison for f ≫ g
and with the single embedding of t_(f ≫ g). Naturality of ε_f moves the
single-complex comparison for g through ε_f. Compatibility of the single-complex
isomorphisms with mapping a composite functor then identifies this with the two
successive single comparisons and the single embedding of tensor composition.
The remaining underived equation is
T_f(t_g) ≫ t_f ≫ pullbackComp.hom = tensorComp.hom ≫ t_(f ≫ g).
Apply the conjugate-morphism equivalence of the composite adjunctions: the
leftAdjointUniq counit equations make both sides the same pushforward composition
map, while conjugateEquiv_pullbackComp_inv pins its ordinary pullback mate.
Injectivity proves the underived equation, and mapping it by the single functor
finishes. No derived single comparison is inverted, so no flatness is required;
identity morphisms, zero modules, and empty schemes are included. -/
theorem canonicalSinglePullbackComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f g).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N) ≫
      canonicalSinglePullbackMap (f ≫ g) N =
    (derivedPullback f).map (canonicalSinglePullbackMap g N) ≫
      canonicalSinglePullbackMap f ((pullback g).obj N) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((pullbackComp f g).hom.app N) := by
  let Q_X := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let Q_Y := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let Q_Z := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let E := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N
  let :=  (Classical.choose exists_derivedPullbackComposition.{u,w}) f
  let :=  (Classical.choose exists_derivedPullbackComposition.{u,w}) g
  let :=  (Classical.choose exists_derivedPullbackComposition.{u,w}) (f ≫ g)
  let C := (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u,w})))) f g
  let eps := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u,w})) (f ≫ g)
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ)
  let : (derivedPullback (f ≫ g)).IsLeftDerivedFunctor eps W :=
    (Classical.choose (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition.{u,w}))) (f ≫ g)
  have hfac := (derivedPullback (f ≫ g)).leftDerived_fac_app eps W
    (derivedPullback g ⋙ derivedPullback f)
    ((Functor.associator DerivedCategory.Qh (derivedPullback g)
        (derivedPullback f)).inv ≫
      Functor.whiskerRight
        ((Classical.choose (Classical.choose_spec
          exists_derivedPullbackComposition.{u,w})) g) (derivedPullback f) ≫
      (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
      Functor.whiskerLeft _
        ((Classical.choose (Classical.choose_spec
          exists_derivedPullbackComposition.{u,w})) f) ≫
      (Functor.associator _ _
        (DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))).inv ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso
          ((conjugateIsoEquiv
            (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
            ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
              (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
            (Scheme.Modules.pushforwardComp f g).symm)
          (ComplexShape.up ℤ)).hom
        (DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))) E
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u,w})))).1 f g
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp] at hfac
  have hfacC := (congrArg
    (fun α ↦ α.app (Q_Z.obj E) ≫ eps.app E) hc).trans hfac
  let ε_f := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u,w})) f
  let ε_g := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u,w})) g
  let t_f := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  let t_g := (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)
  let t_fg := (Classical.choose (exists_tensorPullbackAdjunction (f ≫ g))).leftAdjointUniq
    (pullbackPushforwardAdjunction (f ≫ g))
  let r_f := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app ((pullback g).obj N)) ≫
    (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (t_f.hom.app ((pullback g).obj N))
  let r_g := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (tensorPullback g) (ComplexShape.up ℤ) 0).hom.app N) ≫
    (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map (t_g.hom.app N)
  let r_fg := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (tensorPullback (f ≫ g)) (ComplexShape.up ℤ) 0).hom.app N) ≫
    (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (t_fg.hom.app N)
  let T_f := (tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)
  let T_g := (tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)
  let c := (Functor.mapHomotopyCategoryCompIso
    ((conjugateIsoEquiv
      (Classical.choose (exists_tensorPullbackAdjunction (f ≫ g)))
      ((Classical.choose (exists_tensorPullbackAdjunction g)).comp
        (Classical.choose (exists_tensorPullbackAdjunction f)))).symm
      (pushforwardComp f g).symm) (ComplexShape.up ℤ)).hom.app E
  let p := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map ((pullbackComp f g).hom.app N)
  have ht : c ≫ r_fg = T_f.map r_g ≫ r_f ≫ p :=
    homotopySinglePullbackComposition f g N
  have hn := ε_f.naturality r_g
  change (derivedPullback f).map (Q_Y.map r_g) ≫
      ε_f.app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj ((pullback g).obj N)) =
    ε_f.app (T_g.obj E) ≫ Q_X.map (T_f.map r_g) at hn
  change C.hom.app (Q_Z.obj E) ≫ eps.app E =
    (derivedPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
      Q_X.map c at hfacC
  have h : C.hom.app (Q_Z.obj E) ≫
      (eps.app E ≫ Q_X.map r_fg) =
    (derivedPullback f).map (ε_g.app E ≫ Q_Y.map r_g) ≫
      (ε_f.app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj ((pullback g).obj N)) ≫
        Q_X.map r_f) ≫ Q_X.map p := by
    calc
      _ = (C.hom.app (Q_Z.obj E) ≫ eps.app E) ≫
          Q_X.map r_fg := (Category.assoc _ _ _).symm
      _ = ((derivedPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
          Q_X.map c) ≫ Q_X.map r_fg :=
        congrArg (fun k ↦ k ≫ Q_X.map r_fg) hfacC
      _ = (derivedPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
          Q_X.map (c ≫ r_fg) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = (derivedPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
          Q_X.map (T_f.map r_g ≫ r_f ≫ p) :=
        congrArg (fun k ↦ (derivedPullback f).map (ε_g.app E) ≫
          ε_f.app (T_g.obj E) ≫ Q_X.map k) ht
      _ = _ := by
        simp only [Functor.map_comp, Category.assoc]
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (derivedPullback f).map (ε_g.app E) ≫
            k ≫ Q_X.map r_f ≫ Q_X.map p) hn.symm
  simpa only [canonicalSinglePullbackMap, r_f, r_g, r_fg, p, E, C, eps, ε_f, ε_g,
    t_f, t_g, t_fg, Q_X, Q_Y, Q_Z, DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    SingleFunctors.postcomp, Functor.map_comp, Functor.comp_map, Functor.comp_obj,
    Category.assoc] using h


end AlgebraicGeometry.Scheme.Modules
