/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses

/-! # Open pro-etale pullback preserves K-injective complexes

Source: Stacks Project, Tags 08FI and 09A5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
attribute [local irreducible] proEtaleRingModulePullback

/-- Open pullback preserves K-injectives, including transported coefficient rings.
Source: Stacks Project, Tags 08FI and 09A5
(blueprint: lem-sf-proetale-open-pullback-preserves-kinjective).
Proof: identify inverse image with module-sheaf restriction to the open slice.
Restriction preserves K-injectives because exact extension by zero is its left
adjoint. Transport this property through the open-site equivalence and the scalar
restriction equivalence induced by c. The scalar-extension comparison identifies
the resulting functor with the specified module pullback. Preservation of
K-injectives is invariant under natural isomorphism and composition, giving the
asserted functor-level preservation instance. -/
@[instance] theorem open_pullback_preservesKInjectiveComplexes {S Z : Scheme.{u}}
    (j : S ⟶ Z) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ R') :
    (proEtaleRingModulePullback j R R' c).PreservesKInjectiveComplexes := by
  let U : Z.ProEt := ProEt.mk j
  have : IsOpenImmersion U.hom := ‹IsOpenImmersion j›
  obtain ⟨q, ⟨hq⟩⟩ := proEtale_ringed_open_comparison U R
  let A := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let F := SheafOfModules.overFunctor.{u + 1} A U
  have : F.Additive := (ringedOverFunctor_exactGeneral A U).1
  have : F.PreservesKInjectiveComplexes := ⟨fun K _ ↦
    isKInjective_restrict_localizedOfUniverses.{u + 1, u, 0} A U inferInstance K⟩
  let e := proEtaleScalarEquivalence S ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  obtain ⟨theta, _, _, htheta⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let p : proEtaleRingModulePullback j R R' c ≅
      proEtaleModuleInverseImage j R ⋙ e.inverse := by
    unfold proEtaleRingModulePullback
    exact NatIso.ofComponents (fun M ↦ theta ((proEtaleModuleInverseImage j R).obj M))
      (fun a ↦ htheta _ _ ((proEtaleModuleInverseImage j R).map a))
  let rq : F ⋙ q.inverse ≅ proEtaleModuleInverseImage j R :=
    Functor.isoWhiskerRight hq.symm q.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ q.unitIso.symm ≪≫ Functor.rightUnitor _
  have : q.inverse.Additive := q.inverse.additive_of_preserves_binary_products
  have : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  have : (proEtaleModuleInverseImage j R).Additive := Functor.additive_of_iso rq
  have : (proEtaleModuleInverseImage j R).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso rq
  have : (proEtaleRingModulePullback j R R' c).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso p.symm
  infer_instance

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
