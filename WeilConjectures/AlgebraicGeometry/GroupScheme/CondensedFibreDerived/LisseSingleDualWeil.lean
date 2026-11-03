/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.CategoryTheory.DerivedCategory.CondensedDualSingle

/-! # Derived dual of a lisse module with its Weil datum -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open WeilConjectures.NativeCondensedModule
namespace WeilConjectures.CondensedFibreDerived

/-- The degree-zero embedding identifies the ordinary lisse dual with its derived
internal dual and respects the contragredient Weil datum.
Source: latest blueprint, realified-kernel proof Step 1; the exactness of internal
Hom out of a finite locally free module
(blueprint: lem-fd-lisse-single-dual-weil).

Proof: trivialize L on a pro-etale cover. Internal Hom out of L is then a finite
product of the identity, hence exact; these exactness assertions descend since
restriction to the cover is exact and jointly conservative. Compute the derived
internal Hom into the unit by a K-injective resolution. Applying ordinary Hom
out of L preserves its quasi-isomorphism from the unit, so the natural
augmentation from the degree-zero ordinary dual is a quasi-isomorphism. Invert
it in the derived category to obtain e. Its evaluation is the image of ordinary
evaluation, since the augmentation was defined by that evaluation. Exact
pullback commutes with the degree-zero embedding and its tensorators on the
flat object L. Apply evaluation to both proposed Weil composites: the closed
comparison turns evaluation into pulled-back evaluation, the unit comparison
identifies coefficient units, and the inverse input datum is exactly the
contragredient action. Both composites therefore evaluate to the same map.
The tensor--internal-Hom adjunction makes evaluation jointly faithful on these
maps, giving the stated equality. The construction also applies in rank zero. -/
theorem lisse_single_dual_weil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (g : T ≅ T)
    (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
    (hL : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier)
    (hLis : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier) :
    let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom
    let Ld := IsoAlgebra.mk ((ihom L.carrier).obj (𝟙_ (Modules l T)))
      (Functor.Monoidal.ihomObjIso P L.carrier (𝟙_ _) ≪≫
        (ihom _).mapIso (Functor.Monoidal.εIso P).symm ≪≫
        (MonoidalClosed.internalHom.mapIso L.str.symm.op).app (𝟙_ _))
    let S := DerivedCategory.singleFunctor (Modules l T) 0
    letI : P.mapDerivedCategory.Monoidal := Functor.Monoidal.transport
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj l) g.hom)
    let K := S.obj L.carrier
    let phi := (P.mapDerivedCategorySingleFunctor 0).app L.carrier ≪≫ S.mapIso L.str
    ∃ e : S.obj Ld.carrier ≅ (ihom K).obj (𝟙_ _),
      (P.mapDerivedCategorySingleFunctor 0).app Ld.carrier ≪≫
          S.mapIso Ld.str ≪≫ e =
        P.mapDerivedCategory.mapIso e ≪≫
          Functor.Monoidal.ihomObjIso P.mapDerivedCategory K (𝟙_ _) ≪≫
          (ihom (P.mapDerivedCategory.obj K)).mapIso
            (Functor.Monoidal.εIso P.mapDerivedCategory).symm ≪≫
          (MonoidalClosed.internalHom.mapIso phi.symm.op).app (𝟙_ _) := by sorry

end WeilConjectures.CondensedFibreDerived
