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

private theorem completedPushIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (sfCompletedDerivedDirectImage l E f ≅
      PurCompactSupport.push (PurCompactSupport.completed l E) f) := by
  have hm : proEtaleRingDirectImageMap f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedCoefficientMap l E f :=
    (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)
  have he : sfCompletedModuleDirectImage l E f =
      proEtaleRingModuleDirectImage f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f) := by
    unfold proEtaleRingModuleDirectImage
    rw [hm]
    rfl
  have hF : (sfCompletedModuleDirectImage l E f).Additive :=
    sfCompletedModuleDirectImage_additive l E f
  have hG : (proEtaleRingModuleDirectImage f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).Additive := he ▸ hF
  exact ⟨@Functor.rightDerivedFunctorNatIso _ _ _ _ _ _ _ _ _ _ _ hF hG (eqToIso he)⟩

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

private theorem ordinaryCompactProjectionIsIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (aX : SfProEtaleProjection.TensorModel l E X)
    (aZ : SfProEtaleProjection.TensorModel l E c.Z)
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) :
    IsIso (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E)
      c aX aZ aY (PurCompactSupport.completedPull_comp l E c.i c.g)).app K.obj).app L.obj) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  let (x : X) : Invertible (l : X.residueField x) :=
    (SfProEtaleProjection.residue_unit l D hl X x).invertible
  let (y : Y) : Invertible (l : Y.residueField y) :=
    (SfProEtaleProjection.residue_unit l D hl Y y).invertible
  have hp := SfProEtaleProjection.pull_domains l E f
    (SfProEtaleProjection.finite_dimension D X) (SfProEtaleProjection.finite_dimension D Y)
    (SfProEtaleProjection.scheme_unit l D hl X)
    (SfProEtaleProjection.scheme_unit l D hl Y) L.obj L.property
  have hi := SfProEtaleProjection.tensor_domains l E X
    (SfProEtaleProjection.scheme_unit l D hl X) aX K.obj _ K.property hp
  have support (A : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj A.obj) :=
    (sfIntegralConstructible l E Y).prop_of_iso
      ((sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c).app A).symm
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj A).property
  have hs := SfProEtaleProjection.tensor_domains l E Y
    (SfProEtaleProjection.scheme_unit l D hl Y) aY _ _ (support K) L.property
  exact sfIntegralReduction_conservative l E Y _ hs.1 (support ⟨_, hi.1⟩)
    (integralOrdinaryProjection_finiteReductions D l hl E f c aX aZ aY K L)

private theorem ordinaryProperProjectionIsIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of D.k))] [IsProper p]
    (aX : SfProEtaleProjection.TensorModel l E X)
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (M : sfIntegralConstructibleCategory l E X)
    (N : sfIntegralConstructibleCategory l E Y) :
    IsIso ((((proEtaleRingDerivedAdjunction p
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull p)).rightAdjointProjectionMap
        (ordinaryCurriedTensorPullback (PurCompactSupport.completed l E) p aX aY).hom
      ).app M.obj).app N.obj) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  let : IsNoetherian X := ⟨⟩
  let R := PurCompactSupport.completed l E
  let c := Compactification.ofIsProper p
  let J := (PurCompactSupport.openExtension R (𝟙 X)).mapDerivedCategory
  let F := PurCompactSupport.pull R (𝟙 X)
  let adjJ := PurCompactSupport.openDerivedAdjunction R (𝟙 X)
  let : J.IsEquivalence := identityOpenEquivalence X (R.ring X) (R.pull (𝟙 X))
  let e : J.obj (F.obj M.obj) ≅ M.obj :=
    J.mapIso ((adjJ.rightAdjointUniq (Functor.adjunction J)).app M.obj) ≪≫
      J.asEquivalence.counitIso.app M.obj
  have hK : sfIntegralConstructible l E X (F.obj M.obj) :=
    SfProEtaleProjection.pull_domains l E (𝟙 X)
      (SfProEtaleProjection.finite_dimension D X) (SfProEtaleProjection.finite_dimension D X)
      (SfProEtaleProjection.scheme_unit l D hl X)
      (SfProEtaleProjection.scheme_unit l D hl X) M.obj M.property
  let K : sfIntegralConstructibleCategory l E X := ⟨_, hK⟩
  have hc := ordinaryCompactProjectionIsIso l E D hl p c aX aX aY K N
  let d := (PurCompactSupport.projectionComparisons_existsUnique R c aX aX aY
    (PurCompactSupport.completedPull_comp l E c.i c.g)).exists.choose
  let adj := proEtaleRingDerivedAdjunction p (R.ring Y) (R.ring X) (R.pull p)
  let phi := (ordinaryCurriedTensorPullback R p aX aY).hom
  have hd : d.tensorPullback.hom = phi := by
    ext A B
    exact d.tensorPullback_eq A B
  have hp : IsIso (((adj.rightAdjointProjectionMap d.tensorPullback.hom).app
      (J.obj K.obj)).app N.obj) := by
    let g := (PurCompactSupport.push R p).mapIso ((d.openProjection.app K.obj).app N.obj)
    change IsIso ((((adj.rightAdjointProjectionMap d.tensorPullback.hom).app
      (J.obj K.obj)).app N.obj) ≫ g.hom) at hc
    let := hc
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ g.hom g.isIso_hom hc
  rw [hd] at hp
  exact (NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerRight (adj.rightAdjointProjectionMap phi)
      ((CategoryTheory.evaluation _ _).obj N.obj)) e).mp hp

/-- The proper counit factor of the integral operation projection is invertible.
There is no compact-support projection or open factor in this assertion.

Source: def-exchange-projection, proper counit projection, and
fix-prop-projection-formula.proof.md, integral reconstruction.
(blueprint: lem-sf-integral-proper-operation-projection-isomorphism).

Proof: realize the normalized integral pullback and tensor on flat-term K-flat
representatives over the completed coefficient sheaves. The specified tensor
pullback comparison becomes the completed ordinary tensor comparison. Uniqueness
of the right adjoint transports the supplied proper direct image and its counit
to the ordinary proper direct image on complete objects. Under these comparisons
the displayed mate is the completion of the ordinary proper counit projection.
The proper projection formula for integral bounded constructible inputs makes
the latter invertible: reduce to each positive coefficient quotient, apply finite
proper projection, and reconstruct using the canonical quotient Roos unit.
Constructible tensor completion and ordinary/completed pullback ensure that the
endpoint units are invertible. Conjugating by the adjoint comparisons proves the
claim, independently of the choice of adjunction. This needs no separatedness
of the structure morphisms and no Tor hypothesis beyond integral bounded
constructibility; the integral residue Tor theorem supplies a uniform interval.
Zero inputs and empty schemes are covered by the same comparisons. -/
theorem integralProperOperationProjection_isIso
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E)
    (Q : SixFunctorCompactifiedSquare D)
    (M : sfIntegralConstructibleCategory C.l E Q.Z.obj.left)
    (N : sfIntegralConstructibleCategory C.l E Q.Y.obj.left) :
    IsIso ((((H.integralExchange Q).stage.properAdjunction.rightAdjointProjectionMap
      (H.integralExchange Q).stage.tensorPullback.hom).app M).app N) := by
  obtain ⟨aZ, aY, a, m, n, h⟩ := integralOrdinaryTensorPullbackNormalization H Q
  obtain ⟨e⟩ := completedPushIso C.l E Q.p.hom.left
  let I := (sfIntegralConstructible C.l E Q.Y.obj.left).ι
  let J := (sfIntegralConstructible C.l E Q.Z.obj.left).ι
  let R := PurCompactSupport.completed C.l E
  let b : J ⋙ PurCompactSupport.push R Q.p.hom.left ≅
      (H.integralExchange Q).stage.properPush ⋙ I :=
    (eqToIso (congrArg (fun F ↦ F ⋙ I) (H.integralExchange Q).properPush) ≪≫
      H.integralDirectImage Q.p ≪≫ Functor.isoWhiskerLeft J e).symm
  let adj := proEtaleRingDerivedAdjunction Q.p.hom.left
    (R.ring Q.Y.obj.left) (R.ring Q.Z.obj.left) (R.pull Q.p.hom.left)
  let := Q.proper_p
  have hp := ordinaryProperProjectionIsIso C.l E D C.different Q.p.hom.left aZ aY M N
  exact projectionIsoOfRestriction (H.integralExchange Q).stage.properAdjunction adj
    (sfIntegralConstructible C.l E Q.Y.obj.left).fullyFaithfulι
    (sfIntegralConstructible C.l E Q.Z.obj.left).fullyFaithfulι
    a b _ _ m n h M N hp

end WeilConjectures
