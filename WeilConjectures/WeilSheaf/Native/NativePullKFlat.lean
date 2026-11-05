/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealization
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTensor
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality

public import WeilConjectures.WeilSheaf.Native.NativeForgetTotalTensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-!
# The pullback of pro-étale Weil sheaves preserves K-flat complexes

For a morphism `g : Z ⟶ Y` of `k₀`-schemes, the pullback `g^*` of pro-étale Weil sheaves sends
complexes which are K-flat for the native tensor product to K-flat complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar`).

Forgetting the Weil structure, a native K-flat complex becomes a K-flat complex of `ℓ`-adic
sheaves on the geometric fibre
(`AlgebraicGeometry.ProEtaleWeilSheaf.kFlat_forget_of_nativeIsKFlat`),
hence, through the monoidal equivalence with module objects over the condensed coefficient ring, a
K-flat complex of condensed modules. The pullback of condensed modules preserves K-flat complexes
(`AlgebraicGeometry.ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj`) and commutes
with the equivalence (`AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`), and a complex
of pro-étale Weil sheaves with K-flat underlying complex is K-flat for the native tensor product
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_of_kFlat_forget`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The comparison of the two models of `ℓ`-adic sheaves is a strong monoidal functor. -/
theorem nonempty_monoidal_adicSheafEquivCondensedMod (X : Scheme.{u}) :
    Nonempty (adicSheafEquivCondensedMod l X).functor.Monoidal := by
  obtain ⟨m⟩ := nativeScalarForgetting_monoidal l X
  let : (AdicSheaf.forgetAb l X).Monoidal := m
  exact ⟨inferInstanceAs (AdicSheaf.forgetAb l X ⋙
    Mod.comap (condensedRingObjIsoForgetAb l X).hom).Monoidal⟩

/-- The comparison of the two models of `ℓ`-adic sheaves preserves K-flat complexes. -/
theorem kFlat_adicSheafEquivCondensedMod_mapHomologicalComplex_obj {X : Scheme.{u}}
    {K : CochainComplex (AdicSheaf l X) ℤ}
    (hK : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((adicSheafEquivCondensedMod l X).functor.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨m⟩ := nonempty_monoidal_adicSheafEquivCondensedMod l X
  let : (adicSheafEquivCondensedMod l X).functor.Monoidal := m
  exact Functor.kFlat_mapHomologicalComplex_obj_of_isEquivalence _ hK

/-- The comparison of the two models of `ℓ`-adic sheaves reflects K-flat complexes. -/
theorem kFlat_of_adicSheafEquivCondensedMod_mapHomologicalComplex_obj {X : Scheme.{u}}
    {K : CochainComplex (AdicSheaf l X) ℤ}
    (hK : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((adicSheafEquivCondensedMod l X).functor.mapHomologicalComplex (.up ℤ)).obj K)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K := by
  obtain ⟨m⟩ := nonempty_monoidal_adicSheafEquivCondensedMod l X
  let E := adicSheafEquivCondensedMod l X
  let : E.functor.Monoidal := m
  let : E.inverse.Monoidal := E.inverseMonoidal
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have h := Functor.kFlat_mapHomologicalComplex_obj_of_isEquivalence E.inverse hK
  exact (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_of_iso
    ((E.mapHomologicalComplex (.up ℤ)).unitIso.app K).symm h

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- **The pullback of pro-étale Weil sheaves preserves K-flat complexes**: for a morphism
`g : Z ⟶ Y` of `k₀`-schemes, `g^*` sends complexes of pro-étale Weil sheaves on `Y` which are
K-flat for the native tensor product to K-flat complexes on `Z`. -/
theorem nativeIsKFlat_upperStar (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hP : NativeIsKFlat k₀ l Y P) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply nativeIsKFlat_of_kFlat_forget
  let gf := Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))
  let K := ((Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback k₀ l Y)).mapHomologicalComplex
    (.up ℤ)).obj P
  have h₁ := ProEtale.kFlat_adicSheafEquivCondensedMod_mapHomologicalComplex_obj l
    (kFlat_forget_of_nativeIsKFlat k₀ l Y P hP)
  have h₂ := ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj
    (Profinite.padicAlgClRingObj l) gf h₁
  have h₃ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((ProEtale.adicSheafEquivCondensedMod l _).functor.mapHomologicalComplex (.up ℤ)).obj
        (((ProEtale.adicUpperStar l gf).mapHomologicalComplex (.up ℤ)).obj K)) :=
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_of_iso
      ((NatIso.mapHomologicalComplex (ProEtale.adicUpperStarCompCondensedModIso l gf)
        (.up ℤ)).app K).symm h₂
  exact ProEtale.kFlat_of_adicSheafEquivCondensedMod_mapHomologicalComplex_obj l h₃

/-- Pullback of pro-étale Weil sheaves along any morphism `g : Z ⟶ Y` of `k₀`-schemes preserves
native K-flat complexes (Stacks 06YW). -/
theorem nativeIsKFlat_upperStar_obj {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hP : NativeIsKFlat k₀ l Y P) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj P) :=
  nativeIsKFlat_mapHomologicalComplex_obj_of_iso k₀ l (upperStar k₀ l g) _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
        (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l g _)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtale.adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g _))) ≪≫
      (Functor.associator _ _ _).symm) P
    (ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj
      (Profinite.padicAlgClRingObj l) (Scheme.Hom.geometricFiberMap g (comp_over g _))
      (kFlat_condensedRealization_mapHomologicalComplex k₀ l Y P hP))

/-- The condensed realization of a native K-flat complex of pro-étale Weil sheaves is K-flat. -/
theorem kFlat_condensedRealization (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (hP : NativeIsKFlat k₀ l X P) :
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (HomotopyCategory.kFlat_quotient_obj_iff _).2
    (kFlat_condensedRealization_mapHomologicalComplex k₀ l X P hP)


end AlgebraicGeometry.ProEtaleWeilSheaf
