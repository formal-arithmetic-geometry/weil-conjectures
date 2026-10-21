/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RingedTensorSquarePresentation
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Paper.RingedSquareTensorCompatibility
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent

/-!
# Tensor and adjunction compatibility of canonical ringed-topos path comparisons

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 07A4, 07A6 and 0D6E
(blueprint: lem-sfb-ringed-comparison-tensor-adjunction).

## Main definitions

- `RingedPathRightDerived`: right-derived units and canonical derived adjunction witnesses.
- `canonicalRingedPullbackComparison`, `canonicalRingedDirectImageComparison`: the two
  universal derived path comparisons.
- `ringedPathTensorMap`: the composite of the two canonical tensor-pullback maps.

The recorded ringed tensor presentations keep the actual site module categories,
K-flat tensor models and structural ring maps. The right-derived witnesses below
add the comparison units and the canonical adjunction normalization. In particular
the direct-image comparison is constructed independently by right-derived uniqueness.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits SheafOfModules

namespace CategoryTheory

/-- The right-derived and adjunction witnesses of the recorded ringed tensor edge.
The normalization is the usual derived Hom comparison, not an arbitrary adjunction.
Source: Stacks 0D6E and 07A6 (blueprint: lem-sfb-ringed-comparison-tensor-adjunction). -/
class RingedPathRightDerived {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) where
  [additive : e.pushforward.Additive]
  eta : e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ e.right
  isRightDerived : e.right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
      ((sheafCompose B.topology (forget₂ CommRingCat RingCat)).obj B.ring))
      (ComplexShape.up ℤ))
  canonicalAdjunction : ∀
    (M : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose A.topology (forget₂ CommRingCat RingCat)).obj A.ring)) ℤ)
    (I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose B.topology (forget₂ CommRingCat RingCat)).obj B.ring)) ℤ)
    (a : (e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ I),
    e.derivedAdjunction.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
      (derivedPullbackComplexComparison e.pullback e.left e.epsilon M ≫
        DerivedCategory.Q.map a) =
      DerivedCategory.Q.map
        ((e.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv M I a) ≫
          eta.app I

attribute [instance] RingedPathRightDerived.additive

/-- The composite right-derived comparison unit, with the 0D6E normalization.
Source: Stacks 0D6E (blueprint: lem-sfb-ringed-comparison-tensor-adjunction). -/
def ringedPathRightUnit {W X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge X W) (g : RingedTensorEdge Y X)
    [df : RingedPathRightDerived f] [dg : RingedPathRightDerived g] :
    (f.pushforward ⋙ g.pushforward).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (f.right ⋙ g.right) :=
  Functor.whiskerRight
    (Functor.mapHomologicalComplexCompIso (Iso.refl (f.pushforward ⋙ g.pushforward))
      (ComplexShape.up ℤ)).inv DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft
    (f.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)) dg.eta ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight df.eta g.right ≫
    (Functor.associator _ _ _).hom

/-- The canonical left-derived comparison counit of a composite path.
This chooses the composite as the model of Lh*, so the 0D6D composition isomorphism
is the identity in this model. Source: Stacks 0D6D and 07A4
(blueprint: lem-sfb-ringed-comparison-tensor-adjunction). -/
def ringedPathLeftCounit {W X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge X W) (g : RingedTensorEdge Y X) :
    DerivedCategory.Qh ⋙ (g.left ⋙ f.left) ⟶
      (g.pullback ⋙ f.pullback).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight g.epsilon f.left ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft
      (g.pullback.mapHomotopyCategory (ComplexShape.up ℤ)) f.epsilon ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (g.pullback ⋙ f.pullback))
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh

/-- The canonical pullback comparison, characterized on flat K-flat representatives
by the ordinary ring-compatible path isomorphism. Its definition uses the universal
left-derived lift with the actual composite counits.
Source: Stacks 0D6D and 07A4
(blueprint: lem-sfb-ringed-comparison-tensor-adjunction). -/
def canonicalRingedPullbackComparison {W X₁ X₂ Y : RingedTensorCorner.{u, w}}
    {f₁ : RingedTensorEdge X₁ W} {f₂ : RingedTensorEdge X₂ W}
    {g₁ : RingedTensorEdge Y X₁} {g₂ : RingedTensorEdge Y X₂}
    (s : RingedTensorSquare Y X₁ X₂ W g₁ g₂ f₁ f₂)
    [l₁ : (g₁.left ⋙ f₁.left).IsLeftDerivedFunctor (ringedPathLeftCounit f₁ g₁)
      (HomotopyCategory.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring))
        (ComplexShape.up ℤ))]
    [l₂ : (g₂.left ⋙ f₂.left).IsLeftDerivedFunctor (ringedPathLeftCounit f₂ g₂)
      (HomotopyCategory.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring))
        (ComplexShape.up ℤ))] :
    g₂.left ⋙ f₂.left ≅ g₁.left ⋙ f₁.left :=
  Functor.leftDerivedNatIso (g₂.left ⋙ f₂.left) (g₁.left ⋙ f₁.left)
    (ringedPathLeftCounit f₂ g₂) (ringedPathLeftCounit f₁ g₁)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (g₂.pullback ⋙ f₂.pullback)) (ComplexShape.up ℤ)).symm ≪≫
        Functor.mapHomotopyCategoryCompIso s.modules (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The canonical right-derived comparison of the two ringed paths. The ordinary
right comparison is the conjugate of the ordinary ringed module comparison; its
right-derived lift is fixed by the actual comparison units. These are exactly the
normalized 0D6E composition/path maps, by right-derived uniqueness.
Source: Stacks 0D6E and 07A6
(blueprint: lem-sfb-ringed-comparison-tensor-adjunction). -/
def canonicalRingedDirectImageComparison {W X₁ X₂ Y : RingedTensorCorner.{u, w}}
    {f₁ : RingedTensorEdge X₁ W} {f₂ : RingedTensorEdge X₂ W}
    {g₁ : RingedTensorEdge Y X₁} {g₂ : RingedTensorEdge Y X₂}
    (s : RingedTensorSquare Y X₁ X₂ W g₁ g₂ f₁ f₂)
    [df₁ : RingedPathRightDerived f₁] [df₂ : RingedPathRightDerived f₂]
    [dg₁ : RingedPathRightDerived g₁] [dg₂ : RingedPathRightDerived g₂]
    [h₁ : (f₁.right ⋙ g₁.right).IsRightDerivedFunctor (ringedPathRightUnit f₁ g₁)
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose W.topology (forget₂ CommRingCat RingCat)).obj W.ring))
        (ComplexShape.up ℤ))]
    [h₂ : (f₂.right ⋙ g₂.right).IsRightDerivedFunctor (ringedPathRightUnit f₂ g₂)
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose W.topology (forget₂ CommRingCat RingCat)).obj W.ring))
        (ComplexShape.up ℤ))] :
    f₁.right ⋙ g₁.right ≅ f₂.right ⋙ g₂.right :=
  Functor.rightDerivedNatIso (f₁.right ⋙ g₁.right) (f₂.right ⋙ g₂.right)
    (ringedPathRightUnit f₁ g₁) (ringedPathRightUnit f₂ g₂)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (conjugateIsoEquiv (g₁.moduleAdjunction.comp f₁.moduleAdjunction)
          (g₂.moduleAdjunction.comp f₂.moduleAdjunction) s.modules) (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The composite canonical tensor-pullback map d_i, in the statement's direction.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-sfb-ringed-comparison-tensor-adjunction). -/
def ringedPathTensorMap {W X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge X W) (g : RingedTensorEdge Y X)
    (aW : RingedTensorModel W) (aX : RingedTensorModel X) (aY : RingedTensorModel Y)
    (K H : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring))) :
    (g.left ⋙ f.left).obj (Y.tensor.obj (K, H)) ⟶
      W.tensor.obj ((g.left ⋙ f.left).obj K, (g.left ⋙ f.left).obj H) :=
  f.left.map ((g.tensorComparison aY aX).hom.app (K, H)) ≫
    (f.tensorComparison aX aW).hom.app (g.left.obj K, g.left.obj H)

private theorem natTrans_transport_iso
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (a b : F ⟶ G) {X X' : A} (i : X ≅ X') (h : a.app X = b.app X) :
    a.app X' = b.app X' := by
  rw [← cancel_epi (F.map i.hom), a.naturality, b.naturality, h]

private theorem mate_comparison_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {P₁ P₂ : C ⥤ D} {V₁ V₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : P₁ ⊣ V₁) (b₂ : P₂ ⊣ V₂)
    {Q : A ⥤ C} {T : B ⥤ D}
    (α₁ : TwoSquare Q L₁ P₁ T) (α₂ : TwoSquare Q L₂ P₂ T)
    (σ : L₂ ⟶ L₁) (θ : P₂ ⟶ P₁)
    (fac : α₂.whiskerLeft σ = α₁.whiskerRight θ) :
    (mateEquiv a₂ b₂ α₂).whiskerTop (conjugateEquiv a₁ a₂ σ) =
      (mateEquiv a₁ b₁ α₁).whiskerBottom (conjugateEquiv b₁ b₂ θ) := by
  rw [← conjugateEquiv_mateEquiv_vcomp, fac, mateEquiv_conjugateEquiv_vcomp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def edgeComplexCounit {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) :
    DerivedCategory.Q ⋙ e.left ⟶
      e.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv e.left ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) e.epsilon ≫
    Functor.whiskerRight (e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (e.pullback.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The sheaf functors in the Hom normalization need additional elaboration fuel.
private theorem ringed_edge_mate {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) [d : RingedPathRightDerived e] :
    (mateEquiv (e.moduleAdjunction.mapHomologicalComplex (.up ℤ)) e.derivedAdjunction
      (TwoSquare.mk DerivedCategory.Q (e.pullback.mapHomologicalComplex (.up ℤ)) e.left
        DerivedCategory.Q
        (edgeComplexCounit e))).natTrans = d.eta := by
  ext I
  apply (e.derivedAdjunction.homEquiv _ _).symm.injective
  have h := d.canonicalAdjunction
    ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj I) I
    ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I)
  have hi : (e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv
      ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj I) I
      ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I) = 𝟙 _ := by
    rw [← (e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv_symm_id I]
    exact Equiv.apply_symm_apply _ _
  rw [hi, DerivedCategory.Q.map_id, Category.id_comp] at h
  rw [← h]
  dsimp only [Functor.comp_obj]
  rw [Equiv.symm_apply_apply]
  exact mateEquiv_counit _ _ _ I

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def pathComplexSquare {W X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge X W) (g : RingedTensorEdge Y X) :
    TwoSquare DerivedCategory.Q
      (g.pullback.mapHomologicalComplex (.up ℤ) ⋙ f.pullback.mapHomologicalComplex (.up ℤ))
      (g.left ⋙ f.left) DerivedCategory.Q :=
  (TwoSquare.mk DerivedCategory.Q (g.pullback.mapHomologicalComplex (.up ℤ)) g.left
    DerivedCategory.Q (edgeComplexCounit g)).vComp
      (TwoSquare.mk DerivedCategory.Q (f.pullback.mapHomologicalComplex (.up ℤ)) f.left
        DerivedCategory.Q (edgeComplexCounit f))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pathComplexSquare_app {W X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge X W) (g : RingedTensorEdge Y X)
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring)) ℤ) :
    (pathComplexSquare f g).natTrans.app P =
      f.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
        derivedPullbackComplexComparison f.pullback f.left f.epsilon
          ((g.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  simp only [pathComplexSquare, TwoSquare.vComp, edgeComplexCounit,
    derivedPullbackComplexComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, Functor.map_comp,
    Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Pasting mates elaborates the two module adjunctions and their complex transports.
private theorem pathComplexSquare_mate {W X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge X W) (g : RingedTensorEdge Y X)
    [df : RingedPathRightDerived f] [dg : RingedPathRightDerived g] :
    (mateEquiv ((g.moduleAdjunction.mapHomologicalComplex (.up ℤ)).comp
        (f.moduleAdjunction.mapHomologicalComplex (.up ℤ)))
      (g.derivedAdjunction.comp f.derivedAdjunction) (pathComplexSquare f g)).natTrans =
      ringedPathRightUnit f g := by
  have hm := mateEquiv_hcomp
    (g.moduleAdjunction.mapHomologicalComplex (.up ℤ)) g.derivedAdjunction
    (f.moduleAdjunction.mapHomologicalComplex (.up ℤ)) f.derivedAdjunction
    (TwoSquare.mk DerivedCategory.Q (g.pullback.mapHomologicalComplex (.up ℤ)) g.left
      DerivedCategory.Q (edgeComplexCounit g))
    (TwoSquare.mk DerivedCategory.Q (f.pullback.mapHomologicalComplex (.up ℤ)) f.left
      DerivedCategory.Q (edgeComplexCounit f))
  have he := congrArg TwoSquare.natTrans hm
  simp only [TwoSquare.hComp] at he
  rw [show (mateEquiv (g.moduleAdjunction.mapHomologicalComplex (.up ℤ))
      g.derivedAdjunction _).natTrans = dg.eta from ringed_edge_mate g,
    show (mateEquiv (f.moduleAdjunction.mapHomologicalComplex (.up ℤ))
      f.derivedAdjunction _).natTrans = df.eta from ringed_edge_mate f] at he
  rw [show (mateEquiv _ _ (pathComplexSquare f g)).natTrans = _ from he]
  ext I
  have hi : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (f.pushforward ⋙ g.pushforward)) (.up ℤ)).inv.app I = 𝟙 _ := by
    ext n
    rfl
  simp only [ringedPathRightUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, hi, Functor.map_id, Category.id_comp, Category.comp_id]
  exact (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringedPathLeftCounit_complex {W X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge X W) (g : RingedTensorEdge Y X)
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring)) ℤ) :
    f.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
      derivedPullbackComplexComparison f.pullback f.left f.epsilon
        ((g.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
    (g.left ⋙ f.left).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
      (ringedPathLeftCounit f g).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((g.pullback ⋙ f.pullback).mapHomologicalComplex (.up ℤ)).obj P) := by
  have factors {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
      (K : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose A.topology (forget₂ CommRingCat RingCat)).obj A.ring)) ℤ) :
      DerivedCategory.Qh.map ((e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) =
        𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((e.pullback.mapHomologicalComplex (.up ℤ)).obj K))) := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  dsimp only [Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift,
    Functor.comp_obj, HomotopyCategory.quotient, CategoryTheory.Quotient.functor]
  simp only [derivedPullbackComplexComparison, factors, Functor.map_comp,
    ringedPathLeftCounit, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.map_id, Category.id_comp, Category.assoc]
  simp only [← f.left.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift,
    Functor.comp_obj, HomotopyCategory.quotient, CategoryTheory.Quotient.functor]
  simp only [Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Nested derived comparisons require elaborating quotient functors.
/-- Tensor and adjunction compatibility of the specified canonical two-path comparisons.
Source: Stacks 0D6D, 07A4, 07A6 and 0D6E; Remark 07A7
(blueprint: lem-sfb-ringed-comparison-tensor-adjunction).

Proof: The left-derived factorization equation fixes theta on complexes. Transport
it from Qh to Q and apply lem-weil-pbc-ringed-square-tensor-compatibility on pairs
of flat K-flat representatives. Injectivity of the two-variable restriction of
lem-weil-pbc-site-derived-tensor-descent extends this equation to all derived objects.
For adjunction compatibility, the canonical Hom normalization identifies each edge
right-derived unit with the mate of its complex comparison. Mathlib's horizontal
mate-pasting equation identifies the path unit with the mate of the path comparison.
Conjugating the representative equation for theta therefore gives the right-derived
unit equation for its conjugate. Right-derived uniqueness identifies that conjugate
with the independently specified direct-image comparison. The conjugate counit
identity gives the second conclusion. No comparison unit is cancelled on arbitrary
complexes, so nonflat structural ring maps and unbounded complexes are included. -/
theorem ringedComparisonTensorAdjunction {W X₁ X₂ Y : RingedTensorCorner.{u, w}}
    (f₁ : RingedTensorEdge X₁ W) (f₂ : RingedTensorEdge X₂ W)
    (g₁ : RingedTensorEdge Y X₁) (g₂ : RingedTensorEdge Y X₂)
    (s : RingedTensorSquare Y X₁ X₂ W g₁ g₂ f₁ f₂)
    (aW : RingedTensorModel W) (aX₁ : RingedTensorModel X₁)
    (aX₂ : RingedTensorModel X₂) (aY : RingedTensorModel Y)
    [df₁ : RingedPathRightDerived f₁] [df₂ : RingedPathRightDerived f₂]
    [dg₁ : RingedPathRightDerived g₁] [dg₂ : RingedPathRightDerived g₂]
    [l₁ : (g₁.left ⋙ f₁.left).IsLeftDerivedFunctor (ringedPathLeftCounit f₁ g₁)
      (HomotopyCategory.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring))
        (ComplexShape.up ℤ))]
    [l₂ : (g₂.left ⋙ f₂.left).IsLeftDerivedFunctor (ringedPathLeftCounit f₂ g₂)
      (HomotopyCategory.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring))
        (ComplexShape.up ℤ))]
    [h₁ : (f₁.right ⋙ g₁.right).IsRightDerivedFunctor (ringedPathRightUnit f₁ g₁)
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose W.topology (forget₂ CommRingCat RingCat)).obj W.ring))
        (ComplexShape.up ℤ))]
    [h₂ : (f₂.right ⋙ g₂.right).IsRightDerivedFunctor (ringedPathRightUnit f₂ g₂)
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose W.topology (forget₂ CommRingCat RingCat)).obj W.ring))
        (ComplexShape.up ℤ))] :
    (∀ K H : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring)),
      (canonicalRingedPullbackComparison s).hom.app (Y.tensor.obj (K, H)) ≫
          ringedPathTensorMap f₁ g₁ aW aX₁ aY K H =
        ringedPathTensorMap f₂ g₂ aW aX₂ aY K H ≫
          W.tensor.map (Prod.mkHom ((canonicalRingedPullbackComparison s).hom.app K)
            ((canonicalRingedPullbackComparison s).hom.app H))) ∧
    (∀ Z : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose W.topology (forget₂ CommRingCat RingCat)).obj W.ring)),
      (g₂.left ⋙ f₂.left).map
          ((canonicalRingedDirectImageComparison s).hom.app Z) ≫
        (g₂.derivedAdjunction.comp f₂.derivedAdjunction).counit.app Z =
      (canonicalRingedPullbackComparison s).hom.app ((f₁.right ⋙ g₁.right).obj Z) ≫
        (g₁.derivedAdjunction.comp f₁.derivedAdjunction).counit.app Z) := by
  have htheta (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring)) ℤ) :
      (canonicalRingedPullbackComparison s).hom.app (DerivedCategory.Q.obj P) ≫
        f₁.left.map (derivedPullbackComplexComparison g₁.pullback g₁.left g₁.epsilon P) ≫
        derivedPullbackComplexComparison f₁.pullback f₁.left f₁.epsilon
          ((g₁.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
      f₂.left.map (derivedPullbackComplexComparison g₂.pullback g₂.left g₂.epsilon P) ≫
        derivedPullbackComplexComparison f₂.pullback f₂.left f₂.epsilon
          ((g₂.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P) := by
    rw [ringedPathLeftCounit_complex f₁ g₁ P,
      reassoc_of% (ringedPathLeftCounit_complex f₂ g₂ P)]
    rw [← (canonicalRingedPullbackComparison s).hom.naturality_assoc]
    have hh := Functor.leftDerivedNatTrans_app (g₂.left ⋙ f₂.left) (g₁.left ⋙ f₁.left)
      (ringedPathLeftCounit f₂ g₂) (ringedPathLeftCounit f₁ g₁)
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (Functor.isoWhiskerRight
        ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (g₂.pullback ⋙ f₂.pullback)) (.up ℤ)).symm ≪≫
          Functor.mapHomotopyCategoryCompIso s.modules (.up ℤ)) DerivedCategory.Qh).hom
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    have hh' : (canonicalRingedPullbackComparison s).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (ringedPathLeftCounit f₁ g₁).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      (ringedPathLeftCounit f₂ g₂).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P)) := by
      have hi : (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (g₂.pullback ⋙ f₂.pullback)) (.up ℤ)).inv.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) = 𝟙 _ := by
        rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (g₂.pullback ⋙ f₂.pullback)) (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)), Iso.hom_inv_id_app,
          Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
      have hm : (Functor.mapHomotopyCategoryCompIso s.modules (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        (HomotopyCategory.quotient _ (.up ℤ)).map
          ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P) := rfl
      simpa only [canonicalRingedPullbackComparison, Functor.leftDerivedNatIso_hom,
        Functor.isoWhiskerRight_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.map_comp, hi, hm,
        Functor.map_id, Category.id_comp] using hh
    dsimp only [Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift,
      Functor.comp_obj, HomotopyCategory.quotient, CategoryTheory.Quotient.functor] at hh' ⊢
    rw [reassoc_of% hh']
    erw [DerivedCategory.quotientCompQhIso_hom_naturality]
    rfl
  constructor
  · intro K H
    let l : Y.tensor ⋙ g₂.left ⋙ f₂.left ⟶
        ((g₁.left ⋙ f₁.left).prod (g₁.left ⋙ f₁.left)) ⋙ W.tensor :=
      Functor.whiskerLeft Y.tensor (canonicalRingedPullbackComparison s).hom ≫
        Functor.whiskerRight (g₁.tensorComparison aY aX₁).hom f₁.left ≫
          Functor.whiskerLeft (g₁.left.prod g₁.left) (f₁.tensorComparison aX₁ aW).hom
    let r : Y.tensor ⋙ g₂.left ⋙ f₂.left ⟶
        ((g₁.left ⋙ f₁.left).prod (g₁.left ⋙ f₁.left)) ⋙ W.tensor :=
      Functor.whiskerRight (g₂.tensorComparison aY aX₂).hom f₂.left ≫
        Functor.whiskerLeft (g₂.left.prod g₂.left) (f₂.tensorComparison aX₂ aW).hom ≫
          Functor.whiskerRight
            (NatTrans.prod (canonicalRingedPullbackComparison s).hom
              (canonicalRingedPullbackComparison s).hom) W.tensor
    have hlr : l = r := by
      obtain ⟨P, hP, _, _, hd⟩ := site_derived_tensor_descent.{u, w, u + 1, w}
        Y.topology Y.ring
      apply (hd _ inferInstance _ _).injective
      ext Z
      obtain ⟨hp, hpf⟩ := (hP Z.1.obj).1 Z.1.property
      obtain ⟨hq, hqf⟩ := (hP Z.2.obj).1 Z.2.property
      have he : l.app (DerivedCategory.Q.obj Z.1.obj.as,
          DerivedCategory.Q.obj Z.2.obj.as) = r.app
          (DerivedCategory.Q.obj Z.1.obj.as, DerivedCategory.Q.obj Z.2.obj.as) :=
        ringedSquareTensorCompatibility s aY aX₁ aX₂ aW
          (canonicalRingedPullbackComparison s) (fun P _ _ ↦ htheta P)
          Z.1.obj.as Z.2.obj.as hp hpf hq hqf
      exact natTrans_transport_iso l r
        (((DerivedCategory.quotientCompQhIso _).app Z.1.obj.as).symm.prod
          ((DerivedCategory.quotientCompQhIso _).app Z.2.obj.as).symm) he
    simpa only [l, r, ringedPathTensorMap, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.prod_obj,
      Functor.comp_obj, NatTrans.prod, Category.assoc] using congr_app hlr (K, H)
  · intro Z
    let a₁ := (g₁.moduleAdjunction.mapHomologicalComplex (.up ℤ)).comp
      (f₁.moduleAdjunction.mapHomologicalComplex (.up ℤ))
    let a₂ := (g₂.moduleAdjunction.mapHomologicalComplex (.up ℤ)).comp
      (f₂.moduleAdjunction.mapHomologicalComplex (.up ℤ))
    let b₁ := g₁.derivedAdjunction.comp f₁.derivedAdjunction
    let b₂ := g₂.derivedAdjunction.comp f₂.derivedAdjunction
    let σ := (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom
    let θ := (canonicalRingedPullbackComparison s).hom
    have fac : (pathComplexSquare f₂ g₂).whiskerLeft σ =
        (pathComplexSquare f₁ g₁).whiskerRight θ := by
      ext P
      simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        pathComplexSquare_app, σ, θ, Category.assoc] using (htheta P).symm
    have hm := mate_comparison_naturality a₁ a₂ b₁ b₂
      (pathComplexSquare f₁ g₁) (pathComplexSquare f₂ g₂) σ θ fac
    have hm' := congrArg TwoSquare.natTrans hm
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, a₁, a₂, b₁, b₂] at hm'
    rw [pathComplexSquare_mate, pathComplexSquare_mate] at hm'
    have hc : conjugateEquiv a₁ a₂ σ =
        (NatIso.mapHomologicalComplex
          (conjugateIsoEquiv (g₁.moduleAdjunction.comp f₁.moduleAdjunction)
            (g₂.moduleAdjunction.comp f₂.moduleAdjunction) s.modules) (.up ℤ)).hom := by
      ext I n
      simp only [a₁, a₂, σ, conjugateEquiv_apply_app, Adjunction.comp_unit_app,
        Adjunction.comp_counit_app, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f,
        Adjunction.mapHomologicalComplex_unit_app_f,
        Adjunction.mapHomologicalComplex_counit_app_f,
        Functor.comp_map, Functor.comp_obj]
      rfl
    have heq : (canonicalRingedDirectImageComparison s).hom =
        conjugateEquiv b₁ b₂ θ := by
      apply (f₁.right ⋙ g₁.right).rightDerived_ext (ringedPathRightUnit f₁ g₁)
        (HomologicalComplex.quasiIso _ (.up ℤ))
      ext I
      have hmi := congr_app hm' I
      change DerivedCategory.Q.map ((conjugateEquiv a₁ a₂ σ).app I) ≫
        (ringedPathRightUnit f₂ g₂).app I =
        (ringedPathRightUnit f₁ g₁).app I ≫
          (conjugateEquiv b₁ b₂ θ).app (DerivedCategory.Q.obj I) at hmi
      rw [hc] at hmi
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
        canonicalRingedDirectImageComparison, Functor.rightDerivedNatIso_hom]
      rw [Functor.rightDerivedNatTrans_app]
      exact hmi
    rw [heq]
    exact conjugateEquiv_counit b₁ b₂ θ Z

end CategoryTheory
