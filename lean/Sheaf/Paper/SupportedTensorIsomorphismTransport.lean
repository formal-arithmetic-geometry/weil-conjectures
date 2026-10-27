/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteOpenProductSwap
public import Sheaf.SixFunctors.OpenTensorNormalization

import Sheaf.Paper.SupportedTensorCartesianUnit
import Sheaf.Paper.SupportedTensorSignedUnit
import Sheaf.Paper.SupportedTensorIdentityUnitor
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry

/-! # Cartesian transport of supported tensor comparisons

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry reduction for open extensions.
(blueprint: lem-pur-supported-tensor-isomorphism-transport).

The helpers spell out the actual composites and unit equations in the ordinary
unbounded fixed-scalar category. They introduce no replacement operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization

namespace WeilConjectures.FiniteOpenProduct
namespace SupportedTensor

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The actual restriction/unit equation, retaining the canonical tensor comparison.
Source: the displayed unit equations in the node; Stacks 07A4 and 0GL1
(blueprint: lem-pur-supported-tensor-isomorphism-transport). -/
def UnitEquation {W Y : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (R H : FiniteD A Y) (P Q : FiniteD A W)
    (a : (pull A i).obj R ≅ P) (b : (pull A i).obj H ≅ Q)
    (f : tensor A Y R H ⟶ (finiteShriek A i).obj (tensor A W P Q)) : Prop :=
  (pull A i).map f = (tensorPullIso A i R H).hom ≫
    tensorMap A W a.hom b.hom ≫ (adj A i).unit.app (tensor A W P Q)

/-- Pull an interior identification through the specified Cartesian pullback comparison.
Source: the node's definitions of a and b by canonical composition comparison
(blueprint: lem-pur-supported-tensor-isomorphism-transport). -/
def identification {W Y W' Y' : Scheme.{u}} (i : W ⟶ Y) (i' : W' ⟶ Y')
    (g : Y ≅ Y') (h : W ≅ W') (s : IsPullback h.hom i i' g.hom)
    (R' : FiniteD A Y') (P' : FiniteD A W')
    (a' : (pull A i').obj R' ≅ P') :
    (pull A i).obj ((pull A g.hom).obj R') ≅ (pull A h.hom).obj P' :=
  (square A i g.hom h.hom i' s.w.symm).app R' ≪≫ (pull A h.hom).mapIso a'

/-- The specified transport: inverse tensor comparison, pullback of f', normalized
open base change, and extension of the interior tensor comparison, in that order.
Source: the node's formula for f; Stacks 03S6 and 07A4
(blueprint: lem-pur-supported-tensor-isomorphism-transport). -/
def transport {W Y W' Y' : Scheme.{u}} (i : W ⟶ Y) (i' : W' ⟶ Y')
    [IsOpenImmersion i] [IsOpenImmersion i']
    (g : Y ≅ Y') (h : W ≅ W') (s : IsPullback h.hom i i' g.hom)
    (R' H' : FiniteD A Y') (P' Q' : FiniteD A W')
    (f' : tensor A Y' R' H' ⟶ (finiteShriek A i').obj (tensor A W' P' Q')) :
    tensor A Y ((pull A g.hom).obj R') ((pull A g.hom).obj H') ⟶
      (finiteShriek A i).obj
        (tensor A W ((pull A h.hom).obj P') ((pull A h.hom).obj Q')) :=
  (tensorPullIso A g.hom R' H').inv ≫ (pull A g.hom).map f' ≫
    (beta A h.hom i i' g.hom s).hom.app (tensor A W' P' Q') ≫
    (finiteShriek A i).map (tensorPullIso A h.hom P' Q').hom

/-- The actual signed conjugate, using both Koszul symmetries.
Source: the node's formula for f-rev
(blueprint: lem-pur-supported-tensor-isomorphism-transport). -/
def reverse {W Y : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (R H : FiniteD A Y) (P Q : FiniteD A W)
    (f : tensor A Y R H ⟶ (finiteShriek A i).obj (tensor A W P Q)) :
    tensor A Y H R ⟶ (finiteShriek A i).obj (tensor A W Q P) :=
  sigma A Y H R ≫ f ≫ (finiteShriek A i).map (sigma A W P Q)

/-- The identity-pullback comparison on the exact, termwise derived presentation.
Source: inverse-image identity and its degreewise localization; node proof Step 7
(blueprint: lem-pur-supported-tensor-isomorphism-transport). -/
def identityPull (Y : Scheme.{u}) : pull A (𝟙 Y) ≅ 𝟭 (FiniteD A Y) :=
  Functor.mapDerivedCategoryNatIso (ProEtale.upperStarId (ModuleCat.{u + 1} A) Y) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The identity-square assertion as an equality of arrows after the actual identity
pullback unitors on all four inputs. No object equalities are silently substituted.
Source: the final identity-square clause and proof Step 7
(blueprint: lem-pur-supported-tensor-isomorphism-transport). -/
def IdentityEquation {W Y : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (R H : FiniteD A Y) (P Q : FiniteD A W)
    (f : tensor A Y R H ⟶ (finiteShriek A i).obj (tensor A W P Q)) : Prop :=
  transport A i i (Iso.refl Y) (Iso.refl W) (IsPullback.of_id_fst (f := i)) R H P Q f ≫
    (finiteShriek A i).map (tensorMap A W
      ((identityPull A W).hom.app P) ((identityPull A W).hom.app Q)) =
    tensorMap A Y ((identityPull A Y).hom.app R) ((identityPull A Y).hom.app H) ≫ f

end SupportedTensor

private theorem restriction_injective_of_iso
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {U : D ⥤ C} (a : J ⊣ U)
    {E : D} {P : C} (e : E ≅ J.obj P) (Q : C) :
    Function.Injective (fun f : E ⟶ J.obj Q => U.map f) := by
  intro x y hxy
  apply (cancel_epi e.inv).1
  apply (a.homEquiv P (J.obj Q)).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, hxy]

/-- Cartesian transport, supported-source uniqueness, and signed reversal for arbitrary
unbounded finite-coefficient complexes, including the identity square.

Source: blueprint main-20261015, lem-sf-kunneth-coherence.proof.md, symmetry paragraph;
agent-formulated consequence with the seven-step proof of this DAG node.
(blueprint: lem-pur-supported-tensor-isomorphism-transport).

Proof: each factor of transport is invertible. The Cartesian unit calculation
`supportedTensor_cartesian_unit` supplies its actual restriction equation.
For a source E isomorphic to J(P), precompose two arrows by the inverse
isomorphism and apply the adjunction Hom bijection: its formula is eta followed
by restriction, so equality after restriction implies equality. This gives both
injectivity claims, using the packaged derived braiding for the reversed source.
The signed calculation `supportedTensor_signed_unit` gives the equation for the
specified reverse. Injectivity gives its uniqueness and the first uniqueness
claim. Finally `supportedTensor_identity_unitor` identifies the identity-square
transport using the actual identity-pullback unitors. The three calculations are
separate named steps of this proof. All objects remain arbitrary unbounded
complexes; no faithfulness on arbitrary ambient sources is used. -/
theorem supportedTensorIsomorphismTransport (S : PurityFiniteSetting.{u})
    {W Y W' Y' : Scheme.{u}}
    [W.Over (Spec (.of S.field.k))] [Y.Over (Spec (.of S.field.k))]
    [W'.Over (Spec (.of S.field.k))] [Y'.Over (Spec (.of S.field.k))]
    [IsSeparated (W ↘ Spec (.of S.field.k))]
    [IsSeparated (Y ↘ Spec (.of S.field.k))]
    [IsSeparated (W' ↘ Spec (.of S.field.k))]
    [IsSeparated (Y' ↘ Spec (.of S.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of S.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of S.field.k))]
    [LocallyOfFiniteType (W' ↘ Spec (.of S.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of S.field.k))]
    [QuasiCompact (W ↘ Spec (.of S.field.k))]
    [QuasiCompact (Y ↘ Spec (.of S.field.k))]
    [QuasiCompact (W' ↘ Spec (.of S.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of S.field.k))]
    (i : W ⟶ Y) (i' : W' ⟶ Y') [IsOpenImmersion i] [IsOpenImmersion i']
    (g : Y ≅ Y') (h : W ≅ W')
    (s : IsPullback h.hom i i' g.hom)
    (R' H' : FiniteD S.Coefficient Y') (P' Q' : FiniteD S.Coefficient W')
    (a' : (pull S.Coefficient i').obj R' ≅ P')
    (b' : (pull S.Coefficient i').obj H' ≅ Q')
    (f' : tensor S.Coefficient Y' R' H' ≅
      (finiteShriek S.Coefficient i').obj (tensor S.Coefficient W' P' Q'))
    (hf' : SupportedTensor.UnitEquation S.Coefficient i' R' H' P' Q' a' b' f'.hom) :
    IsIso (SupportedTensor.transport S.Coefficient i i' g h s R' H' P' Q' f'.hom) ∧
    SupportedTensor.UnitEquation S.Coefficient i
      ((pull S.Coefficient g.hom).obj R') ((pull S.Coefficient g.hom).obj H')
      ((pull S.Coefficient h.hom).obj P') ((pull S.Coefficient h.hom).obj Q')
      (SupportedTensor.identification S.Coefficient i i' g h s R' P' a')
      (SupportedTensor.identification S.Coefficient i i' g h s H' Q' b')
      (SupportedTensor.transport S.Coefficient i i' g h s R' H' P' Q' f'.hom) ∧
    (∀ D0 : FiniteD S.Coefficient W,
      Function.Injective (fun x : tensor S.Coefficient Y
        ((pull S.Coefficient g.hom).obj R') ((pull S.Coefficient g.hom).obj H') ⟶
          (finiteShriek S.Coefficient i).obj D0 => (pull S.Coefficient i).map x)) ∧
    (∀ D0 : FiniteD S.Coefficient W,
      Function.Injective (fun x : tensor S.Coefficient Y
        ((pull S.Coefficient g.hom).obj H') ((pull S.Coefficient g.hom).obj R') ⟶
          (finiteShriek S.Coefficient i).obj D0 => (pull S.Coefficient i).map x)) ∧
    (∀ x : tensor S.Coefficient Y
      ((pull S.Coefficient g.hom).obj R') ((pull S.Coefficient g.hom).obj H') ⟶
        (finiteShriek S.Coefficient i).obj (tensor S.Coefficient W
          ((pull S.Coefficient h.hom).obj P') ((pull S.Coefficient h.hom).obj Q')),
      (pull S.Coefficient i).map x = (pull S.Coefficient i).map
        (SupportedTensor.transport S.Coefficient i i' g h s R' H' P' Q' f'.hom) →
      x = SupportedTensor.transport S.Coefficient i i' g h s R' H' P' Q' f'.hom) ∧
    SupportedTensor.UnitEquation S.Coefficient i
      ((pull S.Coefficient g.hom).obj H') ((pull S.Coefficient g.hom).obj R')
      ((pull S.Coefficient h.hom).obj Q') ((pull S.Coefficient h.hom).obj P')
      (SupportedTensor.identification S.Coefficient i i' g h s H' Q' b')
      (SupportedTensor.identification S.Coefficient i i' g h s R' P' a')
      (SupportedTensor.reverse S.Coefficient i
        ((pull S.Coefficient g.hom).obj R') ((pull S.Coefficient g.hom).obj H')
        ((pull S.Coefficient h.hom).obj P') ((pull S.Coefficient h.hom).obj Q')
        (SupportedTensor.transport S.Coefficient i i' g h s R' H' P' Q' f'.hom)) ∧
    (∀ x : tensor S.Coefficient Y
      ((pull S.Coefficient g.hom).obj H') ((pull S.Coefficient g.hom).obj R') ⟶
        (finiteShriek S.Coefficient i).obj (tensor S.Coefficient W
          ((pull S.Coefficient h.hom).obj Q') ((pull S.Coefficient h.hom).obj P')),
      SupportedTensor.UnitEquation S.Coefficient i
        ((pull S.Coefficient g.hom).obj H') ((pull S.Coefficient g.hom).obj R')
        ((pull S.Coefficient h.hom).obj Q') ((pull S.Coefficient h.hom).obj P')
        (SupportedTensor.identification S.Coefficient i i' g h s H' Q' b')
        (SupportedTensor.identification S.Coefficient i i' g h s R' P' a') x →
      x = SupportedTensor.reverse S.Coefficient i
        ((pull S.Coefficient g.hom).obj R') ((pull S.Coefficient g.hom).obj H')
        ((pull S.Coefficient h.hom).obj P') ((pull S.Coefficient h.hom).obj Q')
        (SupportedTensor.transport S.Coefficient i i' g h s R' H' P' Q' f'.hom)) ∧
    SupportedTensor.IdentityEquation S.Coefficient i' R' H' P' Q' f'.hom := by
  let f := SupportedTensor.transport S.Coefficient i i' g h s R' H' P' Q' f'.hom
  have hi : IsIso f := by
    dsimp only [f, SupportedTensor.transport]
    infer_instance
  have hunit := supportedTensor_cartesian_unit S.Coefficient i i' g h s
    R' H' P' Q' a' b' f'.hom hf'
  have hinj (D0 : FiniteD S.Coefficient W) :=
    restriction_injective_of_iso (adj S.Coefficient i) (asIso f) D0
  have hinjrev (D0 : FiniteD S.Coefficient W) :=
    restriction_injective_of_iso (adj S.Coefficient i)
      ((((DerivedCategory.canonicalTensorSymmetry (FiniteModules S.Coefficient Y)).app
        ((pull S.Coefficient g.hom).obj H')).app
          ((pull S.Coefficient g.hom).obj R')) ≪≫ asIso f) D0
  have hrev := supportedTensor_signed_unit S.Coefficient i _ _ _ _
    (SupportedTensor.identification S.Coefficient i i' g h s R' P' a')
    (SupportedTensor.identification S.Coefficient i i' g h s H' Q' b') f hunit
  refine ⟨hi, hunit, hinj, hinjrev, ?_, hrev, ?_, ?_⟩
  · intro x hx
    exact hinj _ hx
  · intro x hx
    exact hinjrev _ (hx.trans hrev.symm)
  · exact supportedTensor_identity_unitor S.Coefficient i' R' H' P' Q' f'.hom

end WeilConjectures.FiniteOpenProduct
