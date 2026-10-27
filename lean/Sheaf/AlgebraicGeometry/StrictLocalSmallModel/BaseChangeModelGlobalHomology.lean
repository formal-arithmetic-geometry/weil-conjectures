/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison

/-! # Global homology of base change to a small strict-local model

Transport the adopted strict-localization theorem through the canonical colimit comparison.
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
/-- Global homology of base change to the original small strict-henselization model is
invertible, with the same hypotheses and conclusion as the original model theorem.
Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: lem-weil-pbc-strict-local-base-change-model-global-homology).

Proof: compose the given affine presentation with Spec of the inverse of the canonical
small-to-full colimit isomorphism. Its compatibility with the structural morphisms identifies
the bottom map of the given cartesian square with the map to strictLocalization. Apply the
adopted model-global-homology theorem to this same square. The derived base-change map
depends on the bottom morphism and its commutativity proof, so rewriting the bottom map
returns precisely the original conclusion. This also covers the zero complex, all integer
degrees, and empty total spaces; no additional torsion or point-field condition is used. -/
theorem smallModel_isIso_strictHenselization_baseChange_modelGlobalHomology
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    IsIso ((Sheaf.Γ (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app K))) := by
  let e : Spec (.of A) ≅ strictLocalization s :=
    eA ≪≫ Scheme.Spec.mapIso (smallStrictHenselizationColimitIso s).symm.op
  have he : e.hom ≫ strictLocalizationToBase s =
      eA.hom ≫ strictHenselizationStructuralMap s := by
    change (eA.hom ≫ Spec.map (smallStrictHenselizationColimitIso s).inv) ≫ _ = _
    rw [Category.assoc, smallStrictHenselizationColimitIso_toBase]
  have transfer (j : Spec (.of A) ⟶ S)
      (hj : e.hom ≫ strictLocalizationToBase s = j)
      (sq : IsPullback p₀ f₀ f j) :
      IsIso ((Sheaf.Γ (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K))) := by
    subst j
    exact isIso_strictHenselization_baseChange_modelGlobalHomology f s e p₀ f₀ sq K n
  exact transfer _ he sq₀

end AlgebraicGeometry.Etale
