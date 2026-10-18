/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RingedTensorSquarePresentation
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

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
set_option warn.sorry false
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

/-- Tensor and adjunction compatibility of the specified canonical two-path comparisons.
Source: Stacks 0D6D, 07A4, 07A6 and 0D6E; Remark 07A7
(blueprint: lem-sfb-ringed-comparison-tensor-adjunction).

Proof: Apply lem-sfb-ringed-derived-monoidal-comparisons to both paths and their ringed
2-isomorphism. The K-flat composition comparisons give
`theta = a₂.symm ≪≫ s ≪≫ a₁`. The definition here is the equivalent unique normalization
on flat K-flat representatives. On these representatives the insertion identity of the
ringed square and the pure-tensor normalizations show that theta is monoidal. Descend
in both variables. Expanding the two composite tensor maps gives the first identity
by associativity and tensor bifunctoriality. For the second, the 0D6E normalization
identifies c with kappa₁.symm followed by the derived right path map and kappa₂.
The canonical derived Hom normalizations identify this with the conjugate of theta
for the two composite adjunctions. The defining transpose formula for that conjugate
is precisely the displayed counit equation. The comparison units are not required to
be isomorphisms on arbitrary complexes, so nonflat structural ring maps are included. -/
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
  sorry

end CategoryTheory
