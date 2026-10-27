/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R6
-/
module

public import Sheaf.Paper.FiniteOpenProductSwap

/-! # Identity-square tensor transport

Source: the symmetry paragraph of the latest blueprint proof of
`lem-sf-kunneth-coherence`, and Stacks Project Tags 03S6, 07A4, 0GL1.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization
namespace WeilConjectures.FiniteOpenProduct

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The identity-square base-change/tensor composite is natural under the canonical
identity-pullback unitors, for every arrow to the open extension.

Source: proof Step 7 of `lem-pur-supported-tensor-isomorphism-transport`,
expanding blueprint `lem-sf-kunneth-coherence`, identity paragraph; Stacks 03S6, 07A4.
(blueprint: lem-pur-supported-tensor-identity-unitor).

Proof: let e_T be the derived identity-pullback unitor displayed below.
The identity-square clause for normalized open base change says that beta followed
by J(e_W) equals e_Y at J. Tensor compatibility of the identity unitor says that
mu_id followed by tensor(e_T,e_T) equals e_T at the tensor product. Insert
these two equations into the left side and use preservation of composition by J.
Naturality of e_Y moves pull_id(f) across e_Y at the target. The remaining
mu_id inverse cancels mu_id, leaving tensor(e_Y,e_Y) followed by f.
The identity clauses here use the actual inverse-image identity and composition
comparisons: ordinary inverse-image pseudofunctor unit coherence gives the beta
clause by uniqueness of adjunction mates, and its monoidal unit coherence gives
the tensor clause. Apply these ordinary equations to the total tensor of K-flat
representatives and descend through localization. No normalization or invertibility
of f is needed. -/
theorem supportedTensor_identity_unitor
    {W Y : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (R H : FiniteD A Y) (P Q : FiniteD A W)
    (f : tensor A Y R H ⟶ (finiteShriek A i).obj (tensor A W P Q)) :
    let eW := Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarId (ModuleCat.{u + 1} A) W) ≪≫
        Functor.mapDerivedCategoryIdIso _
    let eY := Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarId (ModuleCat.{u + 1} A) Y) ≪≫
        Functor.mapDerivedCategoryIdIso _
    ((tensorPullIso A (𝟙 Y) R H).inv ≫ (pull A (𝟙 Y)).map f ≫
      (beta A (𝟙 W) i i (𝟙 Y) (IsPullback.of_id_fst (f := i))).hom.app
        (tensor A W P Q) ≫ (finiteShriek A i).map (tensorPullIso A (𝟙 W) P Q).hom) ≫
      (finiteShriek A i).map (tensorMap A W (eW.hom.app P) (eW.hom.app Q)) =
      tensorMap A Y (eY.hom.app R) (eY.hom.app H) ≫ f := by sorry

end WeilConjectures.FiniteOpenProduct
