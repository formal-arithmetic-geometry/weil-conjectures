/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison

/-! # The actual coefficient arrow for a Picard direct-image comparison

## References

* Stacks Project, Tags 01F7, 08HY and 0B91
* Stacks Project, Tag 01F7
* Stacks Project, Tags 01F7 and 08HY
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The base-changed coefficient morphism lies over W. -/
theorem picardCoefficientBaseMap_snd
    {X X' S : Scheme.{v}} (f : X ⟶ S) (f' : X' ⟶ S)
    (u : X' ⟶ X) (hu : u ≫ f = f') (W : Scheme.{v}) (k : W ⟶ S) :
    (((Over.pullback k).map
      (Over.homMk (U := Over.mk f') (V := Over.mk f) u hu)).left) ≫
        pullback.snd f k = pullback.snd f' k := by simp

/-- The other projection identifies the two pulled-back coefficients. -/
theorem picardCoefficientBaseMap_fst
    {X X' S : Scheme.{v}} (f : X ⟶ S) (f' : X' ⟶ S)
    (u : X' ⟶ X) (hu : u ≫ f = f') (W : Scheme.{v}) (k : W ⟶ S) :
    (((Over.pullback k).map
      (Over.homMk (U := Over.mk f') (V := Over.mk f) u hu)).left) ≫
        pullback.fst f k = pullback.fst f' k ≫ u := by simp

variable
  [∀ Y : Scheme.{v},
    HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- Construct the coefficient-induced arrow between base-changed direct images.

Construction: Let j:X'_W -> X_W be the pullback of u. The two projection
identities identify j^*(L_W) with (u^*L)_W by ordinary pullback composition and
the canonical isomorphisms from tensor pullback to ordinary pullback. Compose
the canonical derived-single pullback map with that coefficient isomorphism.
Apply the derived adjunction unit along j and direct-image composition, then
transport j followed by f_W to f'_W using its projection equation. This gives
the displayed arrow without any cohomology or affine-model comparison. There
is no properness, flatness or invertibility hypothesis on this construction. -/
noncomputable def picardDerivedCoefficientMap
    {X X' S : Scheme.{v}} (f : X ⟶ S) (f' : X' ⟶ S)
    (u : X' ⟶ X) (hu : u ≫ f = f') (L : X.Modules)
    (W : Scheme.{v}) (k : W ⟶ S) :
    (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L)) ⟶
    (schemeDerivedDirectImage (pullback.snd f' k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f' k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f' k)).obj
            ((Modules.tensorPullback u).obj L))) := by
  classical
  let j := ((Over.pullback k).map
    (Over.homMk (U := Over.mk f') (V := Over.mk f) u hu)).left
  have hj : j ≫ pullback.snd f k = pullback.snd f' k :=
    picardCoefficientBaseMap_snd f f' u hu W k
  have hc : j ≫ pullback.fst f k = pullback.fst f' k ≫ u :=
    picardCoefficientBaseMap_fst f f' u hu W k
  let M := (Modules.tensorPullback (pullback.fst f k)).obj L
  let Li := (Modules.tensorPullback u).obj L
  let Mi := (Modules.tensorPullback (pullback.fst f' k)).obj Li
  let t (Y Z : Scheme.{v}) (g : Y ⟶ Z) :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction g)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction g)
  let α : (Modules.pullback j).obj M ≅ Mi :=
    (Modules.pullback j).mapIso ((t _ _ (pullback.fst f k)).app L) ≪≫
      (Modules.pullbackComp j (pullback.fst f k)).app L ≪≫
      (Modules.pullbackCongr hc).app L ≪≫
      ((Modules.pullbackComp (pullback.fst f' k) u).app L).symm ≪≫
      (Modules.pullback (pullback.fst f' k)).mapIso ((t _ _ u).app L).symm ≪≫
      ((t _ _ (pullback.fst f' k)).app Li).symm
  let A := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj M
  let Ai := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings (pullback f' k).toRingedSpace)) 0).obj Mi
  let a : (derivedPullback j).obj A ⟶ Ai :=
    Modules.canonicalSinglePullbackMap j M ≫
      (DerivedCategory.singleFunctor _ 0).map α.hom
  exact relativeMVUnit j (pullback.snd f k) A ≫
    (schemeDerivedDirectImage (j ≫ pullback.snd f k)).map a ≫
      eqToHom (congrArg (fun g ↦ (schemeDerivedDirectImage g).obj Ai) hj)

end AlgebraicGeometry.Scheme
