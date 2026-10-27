/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison

/-! # Closed-stalk base change for the small strict-henselization model

Transport the adopted closed-stalk theorem through the canonical comparison of the small
and full pointed-affine-neighbourhood colimits.
Source: Stacks Project, Tags 03Q9 and 03QO.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the closed geometric stalk of an affine presentation of the small strict
henselization, homology of the derived base-change mate is invertible.
Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: lem-weil-pbc-strict-local-base-change-closed-stalk).

Proof: compose the given affine presentation with Spec of the inverse canonical
small-to-full colimit isomorphism. The equation
`smallStrictHenselizationColimitIso_toBase` identifies its composite to the base with
the original structural map. Apply the adopted closed-stalk theorem to this presentation
and the same cartesian square. Transport along the equality of bottom morphisms; proof
irrelevance identifies the commutativity witnesses in the derived base-change map.
The field k, its residue-field map a, G, and q are unchanged. Thus q = 0, zero sheaves,
empty total spaces, and arbitrary separably closed point-field extensions are included. -/
theorem smallModel_isIso_strictHenselization_baseChange_closedStalk
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s))
    {k : Type u} [Field k] [IsSepClosed k]
    (a : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso ((pointSmallEtale
      (a ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) := by
  let e : Spec (.of A) ≅ strictLocalization s :=
    eA ≪≫ Scheme.Spec.mapIso (smallStrictHenselizationColimitIso s).symm.op
  have he : e.hom ≫ strictLocalizationToBase s =
      eA.hom ≫ strictHenselizationStructuralMap s := by
    change (eA.hom ≫ Spec.map (smallStrictHenselizationColimitIso s).inv) ≫ _ = _
    rw [Category.assoc, smallStrictHenselizationColimitIso_toBase]
  have transfer (j : Spec (.of A) ⟶ S)
      (hj : e.hom ≫ strictLocalizationToBase s = j)
      (sq : IsPullback p₀ f₀ f j) :
      IsIso ((pointSmallEtale
        (a ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
            ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) := by
    subst j
    exact isIso_strictHenselization_baseChange_closedStalk f s e p₀ f₀ sq a G q
  exact transfer _ he sq₀

end AlgebraicGeometry.Etale
