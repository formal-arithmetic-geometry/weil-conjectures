/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SixFunctors.ScalarSixCtf
import WeilConjectures.SixFunctors.ScalarSixPullback
import WeilConjectures.SixFunctors.ScalarSixDirectImage
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.SixFunctors.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.SixFunctors.ListedCoefficientCtf
public import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis

/-! # The six operations and change of coefficients

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/_section.md and sk-prop-scalar-six.proof.md, the six displayed
comparisons and their coefficient-composition and adjunction compatibility.
(blueprint: sk-prop-scalar-six).

The finite base cohomological-dimension hypothesis follows the corrected DAG contract.
The four helper constructions restrict the prescribed compact-support comparison,
its adjunction mate, the scalar associator and scalar unitor to Dctf. The four
statements give preservation and all six isomorphisms, coefficient-tower coherence,
adjunction/evaluation coherence, and identity-coefficient coherence, respectively.
All scalar extensions are ordinary and uncompleted; no flatness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified compact-support comparison restricted to Dctf for the chosen
six-operation adjunctions. Its components are the existing compactification comparison,
not chosen isomorphisms between its endpoints.
Source: latest blueprint scalar-six, compact-support comparison and exceptional transpose
(blueprint: sk-prop-scalar-six). -/
def scalarSixCtfShriekComparison (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    ctfLowerShriek Λ.X ell k hcd f (listedCoefficientCtf ell a ha).1 ⋙
        scalarExceptionalChange ell k a ha Y ≅
      scalarExceptionalChange ell k a ha X ⋙
        ctfLowerShriek Λ'.X ell k hcd f (listedCoefficientCtf ell a ha).2.1 :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      (@asIso _ _ _ _
        ((scalarCompactSupportMap a (compactificationOverField f).i
          (compactificationOverField f).g).app K.obj)
        ((scalarSixCompactSupport ell k hcd a ha f).1 (compactificationOverField f) K).1))
    (fun b ↦ ObjectProperty.hom_ext _
      ((scalarCompactSupportMap a (compactificationOverField f).i
        (compactificationOverField f).g).naturality b.hom))

/-- The exceptional scalar comparison for the prescribed localizing right adjoints.
It is exactly the adjunction mate of the inverse compact-support comparison, so its
counit transpose is inverse gamma followed by scalar extension of the counit.
Source: latest blueprint scalar-six, exceptional-inverse-image displayed transpose
(blueprint: sk-prop-scalar-six). -/
def scalarSixCtfExceptionalComparison (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    ctfExceptionalInverseImage Λ.X ell k hcd f (listedCoefficientCtf ell a ha).1 ⋙
        scalarExceptionalChange ell k a ha X ⟶
      scalarExceptionalChange ell k a ha Y ⋙
        ctfExceptionalInverseImage Λ'.X ell k hcd f
          (listedCoefficientCtf ell a ha).2.1 :=
  (mateEquiv
    (ctfExceptionalAdjunction Λ.X ell k hcd f (listedCoefficientCtf ell a ha).1)
    (ctfExceptionalAdjunction Λ'.X ell k hcd f (listedCoefficientCtf ell a ha).2.1)
    (TwoSquare.mk _ _ _ _ (scalarSixCtfShriekComparison ell k hcd a ha f).inv)).natTrans

/-- The ordinary tensor associator on the full finite-Tor subcategories.
Source: latest blueprint scalar-six, coefficient composition
(blueprint: sk-prop-scalar-six). -/
def scalarSixCtfTower (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    (ha : ListedCoefficientMap ell a) (hb : ListedCoefficientMap ell b)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    scalarExceptionalChange ell k a ha X ⋙ scalarExceptionalChange ell k b hb X ≅
      scalarExceptionalChange ell k (a ≫ b) (.comp a b ha hb) X :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((scalarSixTower a b X.left).app K.obj))
    (fun h ↦ ObjectProperty.hom_ext _ ((scalarSixTower a b X.left).hom.naturality h.hom))

/-- Restriction of the canonical scalar unitor to Dctf, with unchanged components.
Source: latest blueprint scalar-six, identity coefficient maps
(blueprint: sk-prop-scalar-six). -/
def scalarSixCtfUnit (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (Λ : ScalarSixRing.{u}) (ha : ListedCoefficientMap ell (𝟙 Λ))
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    scalarExceptionalChange ell k (𝟙 Λ) ha X ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((scalarChangeUnit Λ X.left).app K.obj))
    (fun h ↦ ObjectProperty.hom_ext _ ((scalarChangeUnit Λ X.left).hom.naturality h.hom))

/-- All six canonical ordinary uncompleted scalar comparisons are invertible on Dctf,
and ordinary derived scalar extension preserves Dctf. The listed-map predicate includes
arbitrary finite ell-power ring maps, continuous integral reductions and their composites;
no flatness hypothesis is imposed. The exceptional functor is the prescribed restriction
of the Brown right adjoint to the localizing closure.
Source: latest blueprint scalar-six, all six displayed comparisons
(blueprint: sk-prop-scalar-six).

Proof: Apply listedCoefficientCtf for preservation and scalarSixPullback for the canonical
pullback identification. Apply scalarSixDirectImage and scalarSixCompactSupport to the
specified mates, using hcd. Restrict the latter comparison to Dctf; uniqueness of right
adjoints identifies the chosen six-operations adjunction with ScalarExceptionalAdjoint,
so scalarSixExceptional gives invertibility of its specified mate. Finally apply the
strong monoidal scalarSixTensorIso and scalarSixTensorHom to the tensor and evaluation
comparisons. All functors and comparison maps are the existing ordinary module-derived
ones; finite Tor amplitude, rather than flatness of the coefficient map, is used. -/
theorem scalarSixCoefficientComparison (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a) :
    (∀ (X : Over (Spec (.of k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
      (constantModelBoundedConstructible Λ'.X X.left ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((scalarSixChange a X.left).obj K.obj)) ∧
    (∀ (X Y : Over (Spec (.of k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (f : X ⟶ Y),
      (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
        IsIso ((scalarSixPullHom a f.left).app K.obj)) ∧
      (∀ L : ConstantModelConstructibleFiniteTor Λ.X X.left,
        IsIso ((scalarDirectImageMate a f.left).app L.obj) ∧
        IsIso ((scalarCompactSupportMap a (compactificationOverField f).i
          (compactificationOverField f).g).app L.obj)) ∧
      (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
        IsIso ((scalarSixCtfExceptionalComparison ell k hcd a ha f).app K))) ∧
    (∀ (X : Over (Spec (.of k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (K L : ConstantModelConstructibleFiniteTor Λ.X X.left),
      IsIso (scalarSixTensorIso a X.left K.obj L.obj).hom ∧
        IsIso (scalarSixHomComparison a X.left K.obj L.obj)) := by
  sorry

/-- Coefficient composition for the canonical comparisons, including the exceptional
mate and the evaluation mate. The tensor clause is monoidality of the specified scalar
tower, so it includes both tensor and tensor-unit coherence.
Source: latest blueprint scalar-six, final coefficient-composition paragraph
(blueprint: sk-prop-scalar-six).

Proof: The pullback tower is ScalarSixPullbackData.tower. Paste its inverse squares
and take mates to obtain the direct-image tower (scalarDirectImageMateCoherence).
Substitute this into the proper/open definition to obtain the compact-support tower.
The tensor tower is the K-flat tensor associator on pure tensors. For exceptional
inverse image paste the inverse compact-support squares and take their counit
transposes; pasted_mates_counit_normalization and injectivity of mateEquiv give the
displayed equation. The same argument for the tensor square gives the Hom tower,
using ihomComparison_comp_app and naturality along the monoidal scalar associator. -/
theorem scalarSixCoefficientTowerCoherence (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    (ha : ListedCoefficientMap ell a) (hb : ListedCoefficientMap ell b)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    let c := compactificationOverField f
    let TaY := scalarExceptionalChange ell k a ha Y
    let TbX := scalarExceptionalChange ell k b hb X
    let E := ctfExceptionalInverseImage Λ.X ell k hcd f (listedCoefficientCtf ell a ha).1
    let E'' := ctfExceptionalInverseImage Λ''.X ell k hcd f
      (listedCoefficientCtf ell b hb).2.1
    (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
      (scalarSixTower a b X.left).hom.app ((scalarSixPull Λ f.left).obj K.obj) ≫
          (scalarSixPullHom (a ≫ b) f.left).app K.obj =
        (scalarSixChange b X.left).map ((scalarSixPullHom a f.left).app K.obj) ≫
          (scalarSixPullHom b f.left).app ((scalarSixChange a Y.left).obj K.obj) ≫
          (scalarSixPull Λ'' f.left).map ((scalarSixTower a b Y.left).hom.app K.obj)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ.X X.left,
      (scalarSixTower a b Y.left).hom.app
          ((RootCoordinateFace.lower Λ.X f.left).obj L.obj) ≫
          (scalarDirectImageMate (a ≫ b) f.left).app L.obj =
        (scalarSixChange b Y.left).map ((scalarDirectImageMate a f.left).app L.obj) ≫
          (scalarDirectImageMate b f.left).app ((scalarSixChange a X.left).obj L.obj) ≫
          (RootCoordinateFace.lower Λ''.X f.left).map
            ((scalarSixTower a b X.left).hom.app L.obj)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ.X X.left,
      (scalarSixTower a b Y.left).hom.app
          ((rightDerivedLowerShriekOfCompactification Λ.X c).obj L.obj) ≫
          (scalarCompactSupportMap (a ≫ b) c.i c.g).app L.obj =
        (scalarSixChange b Y.left).map ((scalarCompactSupportMap a c.i c.g).app L.obj) ≫
          (scalarCompactSupportMap b c.i c.g).app ((scalarSixChange a X.left).obj L.obj) ≫
          (rightDerivedLowerShriekOfCompactification Λ''.X c).map
            ((scalarSixTower a b X.left).hom.app L.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
      (scalarSixCtfTower ell k a b ha hb X).hom.app (E.obj K) ≫
          (scalarSixCtfExceptionalComparison ell k hcd (a ≫ b) (.comp a b ha hb) f).app K =
        TbX.map ((scalarSixCtfExceptionalComparison ell k hcd a ha f).app K) ≫
          (scalarSixCtfExceptionalComparison ell k hcd b hb f).app (TaY.obj K) ≫
          E''.map ((scalarSixCtfTower ell k a b ha hb Y).hom.app K)) ∧
    (∀ (Z : Over (Spec (.of k)))
      [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom],
      NatTrans.IsMonoidal (scalarSixTower a b Z.left).hom ∧
      ∀ K L : ConstantModelConstructibleFiniteTor Λ.X Z.left,
        (scalarSixTower a b Z.left).hom.app
            (((derivedHom Λ.X Z.left).obj (.op K.obj)).obj L.obj) ≫
            scalarSixHomComparison (a ≫ b) Z.left K.obj L.obj =
          (scalarSixChange b Z.left).map (scalarSixHomComparison a Z.left K.obj L.obj) ≫
            scalarSixHomComparison b Z.left ((scalarSixChange a Z.left).obj K.obj)
              ((scalarSixChange a Z.left).obj L.obj) ≫
            (ihom ((scalarSixChange b Z.left).obj
              ((scalarSixChange a Z.left).obj K.obj))).map
                ((scalarSixTower a b Z.left).hom.app L.obj) ≫
            (MonoidalClosed.pre ((scalarSixTower a b Z.left).inv.app K.obj)).app
              ((scalarSixChange (a ≫ b) Z.left).obj L.obj)) := by
  sorry

/-- Unit and counit compatibility is expressed by the actual adjunction transpose
identities, including evaluation and coevaluation for tensor--Hom.
Source: latest blueprint scalar-six, final adjunction/evaluation paragraph
(blueprint: sk-prop-scalar-six).

Proof: Apply unit_mateEquiv and mateEquiv_counit to the inverse pullback square,
respectively the inverse compact-support square. For internal Hom apply the same
two identities to the tensorator; these are ihomComparison_ev and coev_ihomComparison.
Thus all equations retain the prescribed units and counits, with no arbitrary
isomorphism replacing a comparison. -/
theorem scalarSixCoefficientAdjunctionCoherence (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    let A := ctfExceptionalAdjunction Λ.X ell k hcd f (listedCoefficientCtf ell a ha).1
    let B := ctfExceptionalAdjunction Λ'.X ell k hcd f (listedCoefficientCtf ell a ha).2.1
    let T_X := scalarExceptionalChange ell k a ha X
    let T_Y := scalarExceptionalChange ell k a ha Y
    let F' := ctfLowerShriek Λ'.X ell k hcd f (listedCoefficientCtf ell a ha).2.1
    let E' := ctfExceptionalInverseImage Λ'.X ell k hcd f
      (listedCoefficientCtf ell a ha).2.1
    let beta := scalarSixCtfExceptionalComparison ell k hcd a ha f
    let gamma := scalarSixCtfShriekComparison ell k hcd a ha f
    (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
      (scalarSixChange a Y.left).map ((RootCoordinateFace.adjunction Λ.X f.left).unit.app
          K.obj) ≫ (scalarDirectImageMate a f.left).app
            ((scalarSixPull Λ f.left).obj K.obj) =
        (RootCoordinateFace.adjunction Λ'.X f.left).unit.app
            ((scalarSixChange a Y.left).obj K.obj) ≫
          (RootCoordinateFace.lower Λ'.X f.left).map
            ((scalarDirectImagePullbackData.theta a f.left).inv.app K.obj)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ.X X.left,
      (scalarSixPull Λ' f.left).map ((scalarDirectImageMate a f.left).app L.obj) ≫
          (RootCoordinateFace.adjunction Λ'.X f.left).counit.app
            ((scalarSixChange a X.left).obj L.obj) =
        (scalarDirectImagePullbackData.theta a f.left).inv.app
            ((RootCoordinateFace.lower Λ.X f.left).obj L.obj) ≫
          (scalarSixChange a X.left).map
            ((RootCoordinateFace.adjunction Λ.X f.left).counit.app L.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
      F'.map (beta.app K) ≫ B.counit.app (T_Y.obj K) =
        gamma.inv.app _ ≫ T_Y.map (A.counit.app K)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ.X X.left,
      T_X.map (A.unit.app L) ≫ beta.app _ =
        B.unit.app (T_X.obj L) ≫ E'.map (gamma.inv.app L)) ∧
    (∀ (Z : Over (Spec (.of k)))
      [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
      (K L : ConstantModelConstructibleFiniteTor Λ.X Z.left),
      let T := scalarSixChange a Z.left
      (T.obj K.obj ◁ scalarSixHomComparison a Z.left K.obj L.obj ≫
          (ihom.ev (T.obj K.obj)).app (T.obj L.obj) =
        Functor.LaxMonoidal.μ T K.obj _ ≫ T.map ((ihom.ev K.obj).app L.obj)) ∧
      (T.map ((ihom.coev K.obj).app L.obj) ≫
          scalarSixHomComparison a Z.left K.obj (K.obj ⊗ L.obj) =
        (ihom.coev (T.obj K.obj)).app (T.obj L.obj) ≫
          (ihom (T.obj K.obj)).map (Functor.LaxMonoidal.μ T K.obj L.obj))) := by
  sorry

/-- Identity coefficient changes induce the identity comparisons after the canonical
scalar-unit identifications. Monoidality of this unitor also includes tensor units.
Source: latest blueprint scalar-six, identity maps and adjunction compatibility
(blueprint: sk-prop-scalar-six).

Proof: Identity restriction has the identity coefficient square. The canonical scalar
unitor is its adjunction conjugate, so normalization gives the pullback equation.
Taking its mate gives the direct-image equation; insert it in the proper/open formula
for compact support. Taking the latter inverse square's mate gives the exceptional
equation. The K-flat scalar unitor is monoidal on pure tensors; its evaluation mate
is the identity Hom comparison after this same unitor. -/
theorem scalarSixCoefficientIdentityCoherence (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) (Λ : ScalarSixRing.{u})
    (ha : ListedCoefficientMap ell (𝟙 Λ))
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    let c := compactificationOverField f
    let E := ctfExceptionalInverseImage Λ.X ell k hcd f
      (listedCoefficientCtf ell (𝟙 Λ) ha).1
    (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
      (scalarSixPullHom (𝟙 Λ) f.left).app K.obj ≫
          (scalarSixPull Λ f.left).map ((scalarChangeUnit Λ Y.left).hom.app K.obj) =
        (scalarChangeUnit Λ X.left).hom.app ((scalarSixPull Λ f.left).obj K.obj)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ.X X.left,
      (scalarDirectImageMate (𝟙 Λ) f.left).app L.obj ≫
          (RootCoordinateFace.lower Λ.X f.left).map
            ((scalarChangeUnit Λ X.left).hom.app L.obj) =
        (scalarChangeUnit Λ Y.left).hom.app
          ((RootCoordinateFace.lower Λ.X f.left).obj L.obj)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ.X X.left,
      (scalarCompactSupportMap (𝟙 Λ) c.i c.g).app L.obj ≫
          (rightDerivedLowerShriekOfCompactification Λ.X c).map
            ((scalarChangeUnit Λ X.left).hom.app L.obj) =
        (scalarChangeUnit Λ Y.left).hom.app
          ((rightDerivedLowerShriekOfCompactification Λ.X c).obj L.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
      (scalarSixCtfExceptionalComparison ell k hcd (𝟙 Λ) ha f).app K ≫
          E.map ((scalarSixCtfUnit ell k Λ ha Y).hom.app K) =
        (scalarSixCtfUnit ell k Λ ha X).hom.app (E.obj K)) ∧
    (∀ (Z : Over (Spec (.of k)))
      [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom],
      NatTrans.IsMonoidal (scalarChangeUnit Λ Z.left).hom ∧
      ∀ K L : ConstantModelConstructibleFiniteTor Λ.X Z.left,
        scalarSixHomComparison (𝟙 Λ) Z.left K.obj L.obj ≫
            (ihom ((scalarSixChange (𝟙 Λ) Z.left).obj K.obj)).map
              ((scalarChangeUnit Λ Z.left).hom.app L.obj) ≫
            (MonoidalClosed.pre ((scalarChangeUnit Λ Z.left).inv.app K.obj)).app L.obj =
          (scalarChangeUnit Λ Z.left).hom.app
            (((derivedHom Λ.X Z.left).obj (.op K.obj)).obj L.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
