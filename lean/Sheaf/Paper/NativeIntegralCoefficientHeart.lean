/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.LocallyFiniteAdicRealizationData
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.Paper.IntegralCompletedCoefficientTransport
import Sheaf.Paper.IntegralSectionLocalModels
import all Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.AlgebraicGeometry.NativeAdicConstructibilityEncoding
import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Native constructibility of an ordinary integral local model

Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.10, Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-heart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj TensorProduct

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local instance 100000] Sheaf.monoidalCategory Sheaf.braidedCategory

open MonoidalCategory MonObj
open CategoryTheory.InternalAbelianSheafModule
open AlgebraicGeometry.ProEtale

private def liftSectionMap (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) R ⟶
      sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) S) : R ⟶ S :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map a

private theorem liftSectionMap_mon (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) R ⟶
      sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) S) : IsMonHom (liftSectionMap X a) := by
  let : MonObj R.obj := (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).monObjObj R
  let : MonObj S.obj := (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).monObjObj S
  have : IsMonHom ((sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).map
      (liftSectionMap X a)) := by
    constructor
    · apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro n
      change ULift.{u + 1} ℤ at n
      let f : ULift.{u + 1} ℤ →+ S.obj.obj U :=
        ((η[R.obj] ≫ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).map
          (liftSectionMap X a)).app U).hom
      let g : ULift.{u + 1} ℤ →+ S.obj.obj U := (η[S.obj].app U).hom
      change f n = g n
      have hn : n = n.down • (ULift.up 1 : ULift.{u + 1} ℤ) := by
        apply ULift.ext
        simp
      rw [hn, map_zsmul, map_zsmul]
      congr 1
      exact (a.hom.app U).hom.map_one
    · apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.toIntLinearMap_injective
      apply TensorProduct.ext'
      intro x y
      exact (a.hom.app U).hom.map_mul x y
  exact Sheaf.isMonHom_of_isMonHom_map _

private theorem stratifiedModels_of_iso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {M N : pbcModules X (pbcAdicCompletion X d)} (e : M ≅ N)
    (hM : IsIntegralStratifiedFinitelyPresented X d M) :
    IsIntegralStratifiedFinitelyPresented X d N := by
  obtain ⟨s, hs⟩ := hM
  refine ⟨s, fun j ↦ ?_⟩
  obtain ⟨V, hV, h⟩ := hs j
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h U f hf
  exact ⟨P, hP, ⟨(SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (s.immersion j) _).mapIso e.symm) ≪≫ eP⟩⟩

/-- A stratified finitely presented integral module becomes a native constructible
sheaf under ordinary tensor extension. No assertion about derived objects occurs here.

Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.10, Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-heart).

Proof in words: take the finite stratification and the covering sieves in hN.
Restriction along the normalized completed coefficient isomorphism identifies the
local models with completed constant realizations of finitely presented valuation-ring
modules. Tensoring with C.integralMap commutes with the actual-ring inverse images and
slice restrictions, by the scalar-extension adjunction and its balanced tensor
associator. On each covering member this gives the native coefficient tensored with the
scalar module localized to E and then extended along i. A finitely presented module over
the valuation DVR becomes a finite-dimensional E-vector space after localization;
torsion becomes zero. Choose a finite basis and extend it to identify the displayed
tensor with a finite direct sum of native units. The section-module equivalence and
scalar-forgetting equivalence identify those units and commute with inverse image;
full faithfulness lifts the trivializations through e. Replace each covering sieve by
a small pro-etale covering family. Hence the native restriction is lisse on each of the
same finitely many strata, and is therefore constructible. Empty strata, the empty
scheme, zero modules and torsion local models all use the permitted rank zero.
-/
theorem nativeIntegralCoefficient_heart
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (C : CoefficientPresentation l X E i)
    (N : scalarReductionSource.{u, u} l E X)
    (hN : IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l E)
      ((SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison X l E).hom).obj N))
    (F : ProEtale.AdicSheaf l X)
    (e : (sections l X).obj F ≅ (pbcExtend (C.integralMap l X)).obj N) :
    ProEtale.IsAdicConstructibleSheaf F := by
  classical
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let A := ProEtale.AdicCompletion.ring l E X
  let H := ProEtale.integralSectionFunctor l E X
  let B := sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology X) (abRing l X)
  let : B.functor.IsEquivalence := B.isEquivalence_functor
  let : H.IsEquivalence := by dsimp only [H]; infer_instance
  let c := ProEtale.integralSectionRingIso l E X
  let t := c.hom ≫ C.integralMap l X
  let a := liftSectionMap X t
  have : IsMonHom a := liftSectionMap_mon X t
  have ha : CondensedRing.sectionRingMap X a = t := by
    ext U x
    rfl
  -- The restriction square determines the extension square by taking mates.
  let β : Mod.comap a ⋙ H ≅ B.functor ⋙ pbcRestrict (C.integralMap l X) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.sectionModuleComapIso X a)
        (pbcRestrict c.inv) ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft B.functor
        (pbcRestrictComp c.inv (CondensedRing.sectionRingMap X a) (C.integralMap l X)
          (by rw [ha]; exact c.inv_hom_id_assoc (C.integralMap l X)))
  let α := ((mateEquiv (Mod.extendRestrictAdjunction a)
    (pbcScalarAdjunction (C.integralMap l X))).symm β.hom).natTrans
  have : IsIso α := isIso_inverseMate_of_equivalences (G := H) (H := B.functor)
    (Mod.extendRestrictAdjunction a) (pbcScalarAdjunction (C.integralMap l X)) β
  let δ := (asIso α).symm
  -- Transport the given integral models through the section equivalence.
  let M := H.inv.obj N
  let counit : H.obj M ≅ N := H.asEquivalence.counitIso.app N
  have hm := stratifiedModels_of_iso X (pbcIntegralDatum l E)
    ((SheafOfModules.restrictScalars
      (integralDetailedCoefficientComparison X l E).hom).mapIso counit.symm) hN
  have hconst := (ProEtale.integralSectionLocalModels l E X M).mpr hm
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [ProEtale.IsConstantModelConstructible, if_pos hqc] at hconst
  have hM := ProEtale.constructible_of_finiteConstantStratified _ X M hconst
  -- Scalar extension preserves constructibility; the native encoding reflects it.
  have hext := ProEtale.constructible_extend A (abRing l X) a hM
  let q : (ProEtale.AdicSheaf.forgetAb l X).obj F ≅ (Mod.extendScalars a).obj M :=
    B.functor.preimageIso
      (e ≪≫ (pbcExtend (C.integralMap l X)).mapIso counit.symm ≪≫ (δ.app M).symm)
  exact (ProEtale.encoding_constructible_iff F).mpr
    (_root_.constructible_comap (ProEtale.NativeEncoding.coefficientIso l X).hom
      (ProEtale.IsConstructibleModuleObject.of_iso q.symm hext))

end WeilConjectures.LocallyFiniteAdicRealization
