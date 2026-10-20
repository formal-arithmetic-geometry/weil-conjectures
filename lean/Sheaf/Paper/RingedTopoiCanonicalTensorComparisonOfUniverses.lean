/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintenance
-/
module

public import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-!
# Canonical tensor pullback with independent site universes

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).

This is the general canonical representative interface, with a site-object universe s and an
independent site-morphism universe h. Rings and modules live in max s h, as in the
published K-flat interface. Both sites retain their actual Hom universe. The ring map is arbitrary,
  including coefficient quotients, and
the geometric morphism can be the etale-to-pro-etale comparison. The pure-tensor,
unit and signed total-complex normalizations are retained verbatim. Public imports
retain both earlier interfaces for existing callers.
-/

@[expose] public section

set_option autoImplicit false

universe s h w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.CanonicalTensorPullbackOfUniverses


set_option backward.isDefEq.respectTransparency false


variable {C D : Type s} [Category.{h} C] [Category.{h} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{max s h}) (S RI : Sheaf JD CommRingCat.{max s h})
  (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R) ⥤
      SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj S))
  (hobj : ∀ M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

/-- Bilinearity of the existing sheaf tensor, assembled from its additive tensor functors.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: the additive tensorLeft and tensorRight functors of MonoidalFree give the
four zero and addition laws of MonoidalPreadditive. Assemble those four laws. -/
theorem ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) _ _ (monoidalCategory R) :=
  by sorry

/-- The ordinary tensor comparison with its pure-tensor characterization.
The maps q insert 1 in scalar extension; the generalized-element equation fixes
mu on the inverse images of all pure tensors, hence on their sheafification.
Source: Stacks, Modules on Sites, 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
structure CanonicalRingedTensorComparison where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : ∀ M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj RI) ⋙
        sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{max s h})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S) ⋙
        sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{max s h})).obj (L.obj M))
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ∀ (M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R))
      (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W),
    (q M).hom.app W m = (eqToHom (hobj M).symm).val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂
        CommRingCat.{max s h}
      RingCat.{max s h})).obj S).obj)).unit.app
        (changeOfRingsPresheaf.{h, s, max s h} c (I.modules.obj M))).app W
          ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m))
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : ∀ M N : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)
  /-- Naturality in both variables. -/
  naturality : ∀ {M M' N N' : SheafOfModules.{max s h} ((sheafCompose JC (forget₂
    CommRingCat.{max s h}
      RingCat.{max s h})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ∀ (M N : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj
      R)) (Z : Sheaf JC (Type (max s h)))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{max s h})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{max s h})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{max s h})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      (tensorObjIsoSheafification M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JC (forget₂
          CommRingCat.{max s h}
      RingCat.{max s h})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app W (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        q ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S) ⋙
            sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{max s h})).map (mu M N).hom).hom.app W t =
      (tensorObjIsoSheafification (L.obj M) (L.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂
          CommRingCat.{max s h}
      RingCat.{max s h})).obj S).obj)).unit.app
          ((L.obj M).val ⊗ (L.obj N).val)).app W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M ≫ q M).hom.app W t
              ⊗ₜ[S.obj.obj W]
              (uInv.map y ≫ I.moduleUnderlying.inv.app N ≫ q N).hom.app W t))

/-- The pure-tensor conditions determine the ordinary comparison uniquely and are attainable.
Source: Stacks 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: apply the ordinary comparison theorem to the given inverse-image lift.
Its generalized-element normalization gives q and mu. Scalar-extension pure tensors
generate after sheafification, giving uniqueness of q. Bilinear generalized pure tensors
generate the sheaf tensor, giving uniqueness of mu; proof irrelevance handles the laws. -/
theorem canonicalRingedTensorComparison_existsUnique
    (uPush : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj
      R)} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm) :
    Nonempty (CanonicalRingedTensorComparison R S RI uInv I c L hobj) ∧
      Subsingleton (CanonicalRingedTensorComparison R S RI uInv I c L hobj) := sorry

/-- The ordinary unit normalization of the canonical tensor comparison.
Source: Stacks 03EL, pure tensors with the second factor the coefficient ring
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: scalar multiplication gives L(R) = S. On a generalized pure tensor m tensor r,
both composites multiply by the image of r in S. Sheafification extends equality.
The equation at M=R, together with the tensor unitors, uniquely determines j. -/
theorem canonicalRingedTensorComparison_unit
    (hmap : ∀ {M N : (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∃! j : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj S),
      ∀ M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{max s h}
          RingCat.{max s h})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) := sorry

/-- Chain-level representative of the canonical comparison.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def CanonicalRingedTensorComparison.total [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) :
    CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
      (@curriedTensor (SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S)) _ (monoidalCategory S)) ⟶
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor P Q (@curriedTensor (SheafOfModules.{max s h} ((sheafCompose JC
      (forget₂
      CommRingCat.{max s h} RingCat.{max s h})).obj R)) _ (monoidalCategory R))) := by
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  exact tensorPullbackTotal L k.mu k.naturality P Q

/-- The specified total comparison is an isomorphism.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: its summand maps are the inverse ordinary comparisons. Pullback is a left
adjoint and preserves the coproducts defining total complexes. Thus each component
is an isomorphism, and so is the chain map. -/
theorem CanonicalRingedTensorComparison.total_isIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) :
    IsIso (k.total R S RI uInv I c L hobj P Q) := sorry

/-- The canonical chain comparison as an isomorphism, with no arbitrary choice.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def CanonicalRingedTensorComparison.totalIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) :=
  @asIso _ _ _ _ (k.total R S RI uInv I c L hobj P Q)
    (k.total_isIso R S RI uInv I c L hobj V am P Q)

end SheafOfModules.CanonicalTensorPullbackOfUniverses
