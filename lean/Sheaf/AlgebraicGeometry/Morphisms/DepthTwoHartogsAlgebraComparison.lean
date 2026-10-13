/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction

/-! # Hartogs comparison with an actual algebra pushforward

Source: Stacks Project, Tag 0E9I.
(blueprint: lem-sbc-depth-two-hartogs-algebra-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def direct_image_algebra_module_iso {L X : Scheme.{u}} (g : X ⟶ L) :
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    B.toModule ≅ (Modules.pushforward g).obj (SheafOfModules.unit X.ringCatSheaf) := by
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
private theorem algebra_stalk_linearEquiv {L : Scheme.{u}} (B : L.CommAlgebraSheaf)
    (y : L) :
    let : Algebra (L.presheaf.stalk y)
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (X := L) y).obj B.right.obj) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (X := L) y).map B.hom.hom).hom.toAlgebra
    Nonempty ((TopCat.Presheaf.stalk (C := Ab.{u}) (X := L)
      B.toModule.val.presheaf y) ≃ₗ[L.presheaf.stalk y]
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (X := L) y).obj B.right.obj)) := by
  let : Algebra (L.presheaf.stalk y)
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (X := L) y).obj B.right.obj) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (X := L) y).map B.hom.hom).hom.toAlgebra
  let D := (TopologicalSpace.OpenNhds.inclusion y).op ⋙ B.right.obj
  let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u}
  let e : (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L)
      B.toModule.val.presheaf y) ≃+
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (X := L) y).obj B.right.obj) :=
    (CategoryTheory.preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (V : L.Opens) (hy : y ∈ V) (b : B.right.obj.obj (op V)) :
      e (TopCat.Presheaf.germ B.toModule.val.presheaf V y hy b) =
        TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := L) B.right.obj V y hy b := by
    change (CategoryTheory.Limits.colimit.ι (D ⋙ A)
      (op (⟨V, hy⟩ : TopologicalSpace.OpenNhds y)) ≫
        (CategoryTheory.preservesColimitIso A D).inv) b = _
    rw [CategoryTheory.ι_preservesColimitIso_inv]
    rfl
  let ℓ : (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L)
      B.toModule.val.presheaf y) →ₗ[L.presheaf.stalk y]
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (X := L) y).obj B.right.obj) :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨V, hyV, r, rfl⟩ := L.presheaf.exists_germ_eq r
        obtain ⟨W, hyW, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := L) B.toModule.val.presheaf m
        have hy : y ∈ V ⊓ W := ⟨hyV, hyW⟩
        rw [← L.presheaf.germ_res_apply (homOfLE inf_le_left) y hy r,
          ← TopCat.Presheaf.germ_res_apply (X := L) B.toModule.val.presheaf
            (homOfLE inf_le_right) y hy m,
          ← PresheafOfModules.germ_smul (R := L.presheaf)]
        let r' := L.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op r
        let m' : B.right.obj.obj (op (V ⊓ W)) :=
          B.toModule.val.presheaf.map (homOfLE inf_le_right : V ⊓ W ⟶ W).op m
        change e (TopCat.Presheaf.germ B.toModule.val.presheaf (V ⊓ W) y hy
          (B.hom.hom.app (op (V ⊓ W)) r' * m')) =
          (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (X := L) y).map B.hom.hom
            (L.presheaf.germ (V ⊓ W) y hy r') *
              e (TopCat.Presheaf.germ B.toModule.val.presheaf (V ⊓ W) y hy m')
        rw [hg, hg]
        erw [TopCat.Presheaf.stalkFunctor_map_germ_apply (V ⊓ W) y hy B.hom.hom r']
        exact map_mul
          (TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := L)
            B.right.obj (V ⊓ W) y hy).hom _ _ }
  exact ⟨LinearEquiv.ofBijective ℓ e.bijective⟩

/-- Hartogs identifies a supplied coherent depth-two extension with the actual
pushforward, including the scalar-compatible comparison of ring-valued stalks.

Source: Stacks Project, Tag 0E9I; stalks as filtered colimits, Tag 009E.
(blueprint: lem-sbc-depth-two-hartogs-algebra-comparison)

Proof: Apply isIso_restrictAdjunction_unit_of_depth_two (Tag 0E9I) to N.
The algebra's underlying module is definitionally the direct image of the
structure module along f followed by j. The composition isomorphism exhibits
it as an object in the essential image of j_*, so its restriction-adjunction
unit is invertible by full faithfulness. Push forward the supplied restriction
isomorphism and compose it with the unit for N and the inverse unit for B. On stalks apply
the module stalk functor to this isomorphism. Forgetting the rings of the
algebra sheaf to abelian groups commutes with the filtered colimit defining
the stalk, giving the additive comparison with the CommRingCat-valued stalk.
Its scalar compatibility follows on germs from the structure sheaf map:
the germ of r times the germ of b is the germ of r*b. Every scalar and vector
have representatives on a common neighbourhood, so the comparison is linear.
The inverse is linear by bijectivity. This uses no finiteness or etaleness of f
and no boundary depth assumption on the base ring. Empty stalks and empty
schemes obey the same functorial comparisons. -/
theorem depth_two_hartogs_algebra_comparison
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) :
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    Nonempty (Modules.restrict N U.ι ≅ Modules.restrict B.toModule U.ι) →
    Nonempty (N ≅ B.toModule) ∧
      ∀ y : L,
        letI : Algebra (L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj) :=
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).map B.hom.hom).hom.toAlgebra
        Nonempty ((TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)
          ≃ₗ[L.presheaf.stalk y]
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj)) := by
  dsimp only
  intro hrestrict
  obtain ⟨r⟩ := hrestrict
  let B : L.CommAlgebraSheaf := Under.mk
    (⟨(f ≫ U.ι).c⟩ : L.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ U.ι).base).obj X.sheaf)
  let P := (Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  let b : B.toModule ≅ (Modules.pushforward U.ι).obj P :=
    direct_image_algebra_module_iso (f ≫ U.ι) ≪≫
      ((Modules.pushforwardComp f U.ι).app (SheafOfModules.unit X.ringCatSheaf)).symm
  have := isIso_restrictAdjunction_unit_of_depth_two U N hqc hsections hdepth
  have := (Modules.restrictAdjunction U.ι).isIso_unit_app_of_iso b
  let e : N ≅ B.toModule :=
    asIso ((Modules.restrictAdjunction U.ι).unit.app N) ≪≫
      (Modules.pushforward U.ι).mapIso r ≪≫
        (asIso ((Modules.restrictAdjunction U.ι).unit.app B.toModule)).symm
  refine ⟨⟨e⟩, fun y => ?_⟩
  obtain ⟨a⟩ := algebra_stalk_linearEquiv
    (Under.mk (⟨(f ≫ U.ι).c⟩ : L.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ U.ι).base).obj X.sheaf)) y
  let S := RingedSpace.moduleStalkFunctor L.toRingedSpace y
  exact ⟨((S.mapIso e).toLinearEquiv).trans a⟩

end AlgebraicGeometry.Scheme
