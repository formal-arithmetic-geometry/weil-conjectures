/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
import WeilConjectures.SixFunctors.Integral.IntegralOrdinaryTensorPullbackNormalization
import all WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import WeilConjectures.CategoryTheory.Adjunction.MatesCounit
import Mathlib.CategoryTheory.Adjunction.Restrict

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

/-! # Proper counit projection on the integral operation domain

Source: def-exchange-projection, proper projection mate; the integral reconstruction
in fix-prop-projection-formula.proof.md.
(blueprint: lem-sf-integral-proper-operation-projection-isomorphism).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem mateIsoOfRestriction
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {F' : A' ⥤ B'} {G' : B' ⥤ A'} (adj' : F' ⊣ G')
    {I : A ⥤ A'} {J : B ⥤ B'} (hI : I.FullyFaithful) (hJ : J.FullyFaithful)
    (a : I ⋙ F' ≅ F ⋙ J) (b : J ⋙ G' ≅ G ⋙ I) (M : B) :
    IsIso ((mateEquiv adj adj' a.hom).app M) := by
  let r := adj'.restrictFullyFaithful hI hJ a b
  apply isIso_mateEquiv_app_of_counit adj adj' r adj' a.hom M (b.inv.app M)
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [Iso.hom_inv_id_app_assoc]

private theorem projectionIsoOfRestriction
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {F' : A' ⥤ B'} {G' : B' ⥤ A'} (adj' : F' ⊣ G')
    {I : A ⥤ A'} {J : B ⥤ B'} (hI : I.FullyFaithful) (hJ : J.FullyFaithful)
    (a : I ⋙ F' ≅ F ⋙ J) (b : J ⋙ G' ≅ G ⋙ I)
    {T : A ⥤ A ⥤ A} {U : B ⥤ B ⥤ B}
    {T' : A' ⥤ A' ⥤ A'} {U' : B' ⥤ B' ⥤ B'}
    (t : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj U)
    (t' : (Functor.postcompose₂.obj F').obj T' ⟶
      (((Functor.whiskeringLeft₂ B').obj F').obj F').obj U')
    (m : (Functor.postcompose₂.obj J).obj U ≅
      (((Functor.whiskeringLeft₂ B').obj J).obj J).obj U')
    (n : (Functor.postcompose₂.obj I).obj T ≅
      (((Functor.whiskeringLeft₂ A').obj I).obj I).obj T')
    (h : Adjunction.ComparisonCompatible a t t' m n) (M : B) (N : A)
    (hp : IsIso (((adj'.rightAdjointProjectionMap t').app (J.obj M)).app (I.obj N))) :
    IsIso (((adj.rightAdjointProjectionMap t).app M).app N) := by
  let := hp
  have (K : B) : IsIso ((mateEquiv adj adj' a.hom).app K) :=
    mateIsoOfRestriction adj adj' hI hJ a b K
  have hs := Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv adj adj' h M N
  have : IsIso (I.map (((adj.rightAdjointProjectionMap t).app M).app N) ≫
      (mateEquiv adj adj' a.hom).app ((U.obj M).obj (F.obj N)) ≫
      G'.map ((m.hom.app M).app (F.obj N) ≫
        (U'.obj (J.obj M)).map (a.inv.app N))) := by
    rw [hs]
    infer_instance
  have : IsIso (I.map (((adj.rightAdjointProjectionMap t).app M).app N)) :=
    IsIso.of_isIso_comp_right _
      ((mateEquiv adj adj' a.hom).app ((U.obj M).obj (F.obj N)) ≫
        G'.map ((m.hom.app M).app (F.obj N) ≫
          (U'.obj (J.obj M)).map (a.inv.app N)))
  let := hI.full
  let := hI.faithful
  exact isIso_of_reflects_iso _ I

private theorem identityOpenEquivalence
    (W : Scheme.{u}) (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage (𝟙 W) CommRingCat.{u + 1}).obj R ≅ R) :
    (proEtaleRingOpenExtension (𝟙 W) R R c).mapDerivedCategory.IsEquivalence := by
  let a := proEtaleSheafAdjunction (𝟙 W) CommRingCat.{u + 1}
  let : IsIso a.unit :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0}
      (𝟙 W) CommRingCat.{u + 1}).2.1
  let : IsIso (proEtaleRingDirectImageMap (𝟙 W) R R c) := by
    unfold proEtaleRingDirectImageMap
    infer_instance
  let ρ := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap (𝟙 W) R R c)
  have hρ : IsIso ρ := by
    dsimp only [ρ]
    infer_instance
  let e := @isoModulePushforwardEquivalence W W (𝟙 W) (inferInstance)
    ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ρ hρ
  let : (proEtaleRingModuleDirectImage (𝟙 W) R R c).IsEquivalence :=
    inferInstanceAs e.functor.IsEquivalence
  let : (proEtaleRingModulePullback (𝟙 W) R R c).IsEquivalence :=
    (proEtaleRingModuleAdjunction (𝟙 W) R R c).isEquivalence_left_of_isEquivalence_right
  let : (proEtaleRingOpenExtension (𝟙 W) R R c).IsEquivalence :=
    (Adjunction.ofIsRightAdjoint
      (proEtaleRingModulePullback (𝟙 W) R R c)).isEquivalence_left_of_isEquivalence_right
  infer_instance

end WeilConjectures
