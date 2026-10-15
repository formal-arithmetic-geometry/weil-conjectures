/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import Sheaf.CategoryTheory.ModulePullbackTensorIso
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Canonical representative comparison for tensor pullback

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) [L.Additive]
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)

/-- The inverse ordinary tensor comparison, summed over all bidegrees.
Source: Stacks 07A4, last display of the proof
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def tensorPullbackTotalComponent (P Q : CochainComplex A ℤ) (n : ℤ) :
    (CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).X n ⟶
        L.obj ((CochainComplex.mapBifunctor P Q (curriedTensor A)).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun a b h ↦
    (e (P.X a) (Q.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n h))

/-- The ordinary summand comparison commutes with the two tensor differentials.
Source: Stacks 07A4, construction of the total comparison
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: test on every summand. Naturality of e handles d_P and d_Q separately.
Additivity of L preserves the sign (-1)^a on the second differential. The two
summand equations add to the asserted chain-map equation. -/
theorem tensorPullbackTotalComponent_comm
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (P Q : CochainComplex A ℤ) (n m : ℤ) :
    tensorPullbackTotalComponent L e P Q n ≫
        L.map ((CochainComplex.mapBifunctor P Q (curriedTensor A)).d n m) =
      (CochainComplex.mapBifunctor
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).d n m ≫
          tensorPullbackTotalComponent L e P Q m := sorry

/-- The chain comparison is the signed total of the inverse ordinary comparisons.
Source: Stacks 07A4, final display
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def tensorPullbackTotal
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (P Q : CochainComplex A ℤ) :
    CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B) ⟶
        (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q (curriedTensor A)) where
  f := tensorPullbackTotalComponent L e P Q
  comm' n m _ := tensorPullbackTotalComponent_comm L e he P Q n m

/-- A left adjoint preserves the coproducts defining total tensor, so beta is invertible.
Source: Stacks 07A4 and Modules on Sites 03D7
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: each inverse ordinary comparison is invertible. The adjunction identifies
maps out of a pulled-back coproduct with families of maps out of the pulled-back
summands, so its coproduct comparison is invertible. Each degree of beta is the
composite of these two isomorphisms. A degreewise isomorphism of complexes is an
isomorphism of complexes. -/
theorem tensorPullbackTotal_isIso
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (adj : L ⊣ V) (P Q : CochainComplex A ℤ) :
    IsIso (tensorPullbackTotal L e he P Q) := sorry


universe wA wB

/-- Transport the homotopy left-derived comparison to the complex localization Q.
Source: Stacks 06YY and 07A4
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def derivedPullbackComplexComparison
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    LF.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
    epsilon.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- Transport the homotopy right-derived comparison to the complex localization Q.
Source: Stacks 070K (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def derivedPushforwardComplexComparison
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (V : B ⥤ A) [V.Additive] (RF : DerivedCategory B ⥤ DerivedCategory A)
    (eta : V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) (K : CochainComplex B ℤ) :
    DerivedCategory.Q.obj ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      RF.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso A).inv.app
      ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    DerivedCategory.Qh.map ((V.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
      eta.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K) ≫
        RF.map ((DerivedCategory.quotientCompQhIso B).hom.app K)

end CategoryTheory

namespace SheafOfModules


set_option backward.isDefEq.respectTransparency false

universe w

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

/-- Bilinearity of the existing sheaf tensor, assembled from its additive tensor functors.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: the additive tensorLeft and tensorRight functors of MonoidalFree give the
four zero and addition laws of MonoidalPreadditive. Assemble those four laws. -/
noncomputable abbrev ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ _ (monoidalCategory R) :=
  Classical.choice (tensorClosed R).1

/-- The ordinary tensor comparison with its pure-tensor characterization.
The maps q insert 1 in scalar extension; the generalized-element equation fixes
mu on the inverse images of all pure tensors, hence on their sheafification.
Source: Stacks, Modules on Sites, 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
structure CanonicalRingedTensorComparison where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M))
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W),
    (q M).hom.app W m = (eqToHom (hobj M).symm).val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
        (changeOfRingsPresheaf.{u, u, u} c (I.modules.obj M))).app W
          ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m))
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)
  /-- Naturality in both variables. -/
  naturality : ∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      (tensorObjIsoSheafification M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app W (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        q ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{u})).map (mu M N).hom).hom.app W t =
      (tensorObjIsoSheafification (L.obj M) (L.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
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
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
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
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∃! j : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) := sorry

/-- Chain-level representative of the canonical comparison.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def CanonicalRingedTensorComparison.total [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :
    CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
      (@curriedTensor (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) _ (monoidalCategory S)) ⟶
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor P Q (@curriedTensor (SheafOfModules.{u} ((sheafCompose JC
      (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) _ (monoidalCategory R))) := by
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
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :
    IsIso (k.total R S RI uInv I c L hobj P Q) := sorry

/-- The canonical chain comparison as an isomorphism, with no arbitrary choice.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def CanonicalRingedTensorComparison.totalIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :=
  @asIso _ _ _ _ (k.total R S RI uInv I c L hobj P Q)
    (k.total_isIso R S RI uInv I c L hobj V am P Q)

set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- Elaborate the full two-variable representative square.
/-- Canonical derived comparison, uniquely characterized on K-flat flat-term representatives.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: resolve both inputs by K-flat flat-term complexes; pullback preserves that class
by 0G7E. Their total tensor is K-flat by reassociating an acyclic test tensor and applying
K-flatness twice, and has flat terms by tensor-flatness and countable flat sums.
The left-derived comparison computes pullback on these representatives. Compose it
with the inverse image of the explicit chain comparison k.totalIso and rS. The displayed
square records exactly this construction relative to rR. Naturality of the summand
comparisons handles both differentials and their signs. Two-variable tensor descent
extends the square to all derived objects and makes its extension unique. The ordinary
unit normalization is canonicalRingedTensorComparison_unit, forced by k.pure. -/
theorem ringedTopoiCanonicalDerivedTensorPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V) :
    (∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        CochainComplex.IsKFlat ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
          ∀ n : ℤ,
            (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n).IsFlat) ∧
    ∃! alpha : TR ⋙ LF ≅ (LF.prod LF) ⋙ TS,
      ∀ (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (hp : PR P) (hq : PR Q),
        ∃ (hp' : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hq' : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          LF.map (rR.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
              alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
                TS.map (CategoryTheory.Prod.mkHom
                  (derivedPullbackComplexComparison uStar LF epsilon P)
                  (derivedPullbackComplexComparison uStar LF epsilon Q)) =
            derivedPullbackComplexComparison uStar LF epsilon
              (CochainComplex.mapBifunctor P Q
                (@curriedTensor (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ (monoidalCategory R))) ≫
              (DerivedCategory.Q.mapIso
                (k.totalIso R S RI uInv I c uStar hobj V am P Q)).inv ≫
                  rS.hom.app
                    (⟨(uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, hp'⟩,
                      ⟨(uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q, hq'⟩) := sorry

set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- Keep both tensor representative interfaces explicit.
/-- The canonical derived comparison selected by its unique representative characterization.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
The theorem specifies the natural isomorphism uniquely, so only its proof is postponed. -/
noncomputable def ringedTopoiCanonicalDerivedTensorComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V) :
    TR ⋙ LF ≅ (LF.prod LF) ⋙ TS :=
  Classical.choose (ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).2.exists

end SheafOfModules
