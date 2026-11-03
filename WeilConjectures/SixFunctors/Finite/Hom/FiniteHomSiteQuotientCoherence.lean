/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import all WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteScalarArrow
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomOrdinaryRestrictionChain

/-! # Successive quotient coherence of the fixed finite site mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private def ordinaryIntrinsicComp {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :
    normalizedDVRModuleRes l E X k ⋙ normalizedDVRModuleRes l E X h ≅
      normalizedDVRModuleRes l E X (k.trans h) :=
  normalizedDVRRestrictionComp (normalizedDVRQuotient l E X h)
    (normalizedDVRQuotient l E X k) (normalizedDVRQuotient l E X (k.trans h))
    ((integralCoefficientSheafSystem l E X).map_comp (homOfLE h).op (homOfLE k).op).symm

private def ordinaryEtaleComp {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :=
  Sheaf.restrictScalarsCompIso X.smallEtaleTopology (finiteHomQuotient l E h)
    (finiteHomQuotient l E k) (finiteHomQuotient l E (k.trans h))
    (finiteHomQuotient_comp l E h k)

private theorem derivedRestriction_chain {n m r : ℕ} (h : m ≤ n) (k : r ≤ m)
    (M : finiteHomEtale l E X r) :
    (finiteHomNu l E X n).map
        ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
          (finiteHomQuotient_comp l E h k)).inv.app M) ≫
      (finiteHomNuDerivedRestriction l E X h).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E k)).obj M) ≫
      (normalizedDVRRes l E X h).map ((finiteHomNuDerivedRestriction l E X k).inv.app M) =
    (finiteHomNuDerivedRestriction l E X (k.trans h)).inv.app M ≫
      (normalizedDVRResComp l E X h k).inv.app ((finiteHomNu l E X r).obj M) := by
  have hd := Functor.exactSquare_comp_forward
    (Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E k))
    (Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h))
    (Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E (k.trans h)))
    (normalizedDVRModuleRes l E X k) (normalizedDVRModuleRes l E X h)
    (normalizedDVRModuleRes l E X (k.trans h))
    (finiteHomNuOrdinary l E X r) (finiteHomNuOrdinary l E X m)
    (finiteHomNuOrdinary l E X n)
    (finiteHomNuRestriction l E X k).symm (finiteHomNuRestriction l E X h).symm
    (finiteHomNuRestriction l E X (k.trans h)).symm
    (ordinaryEtaleComp l E X h k).symm (ordinaryIntrinsicComp l E X h k).symm
    (finiteHomOrdinaryRestriction_chain X l E h k) M
  dsimp only [finiteHomNu, normalizedDVRRes, Sheaf.derivedRestrictScalars,
    Functor.mapDerivedCategorySquareIso, Sheaf.derivedRestrictScalarsCompIso,
    normalizedDVRResComp, ordinaryIntrinsicComp, ordinaryEtaleComp,
    finiteHomNuDerivedRestriction, normalizedDVRRestrictionComp] at hd ⊢
  simpa only [Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc] using hd

private theorem beta_chain {n m r : ℕ} (h : m ≤ n) (k : r ≤ m)
    (T : finiteHomEtale l E X n) :
    (finiteHomSiteBeta l E X (k.trans h)).app T =
      (finiteHomIntrinsicAssoc l E X h k).inv.app ((finiteHomNu l E X n).obj T) ≫
        (coefficientFiniteQuotientDerived l E X k).map
          ((finiteHomSiteBeta l E X h).app T) ≫
        (finiteHomSiteBeta l E X k).app ((finiteHomEtaleReduction l E X h).obj T) ≫
        (finiteHomNu l E X r).map ((finiteHomEtaleAssoc l E X h k).hom.app T) := by
  apply reverse_chain
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E h)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E k)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (finiteHomQuotient l E (k.trans h))))
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction k)
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (k.trans h))
    (finiteHomNu l E X n) (finiteHomNu l E X m) (finiteHomNu l E X r)
    (finiteHomNuDerivedRestriction l E X h).inv
    (finiteHomNuDerivedRestriction l E X k).inv
    (finiteHomNuDerivedRestriction l E X (k.trans h)).inv
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
      (finiteHomQuotient_comp l E h k)) (normalizedDVRResComp l E X h k)
  intro M
  have hd := derivedRestriction_chain l E X h k M
  have he := congrArg (fun t ↦ t ≫ (normalizedDVRResComp l E X h k).hom.app
    ((finiteHomNu l E X r).obj M)) hd
  simp only [Category.assoc, Iso.inv_hom_id_app] at he
  erw [Category.comp_id] at he
  exact he.symm

private theorem invert_fourfold {C : Type*} [Category C]
    {A B D E F : C} (a : A ≅ B) (b : B ≅ D) (c : D ≅ E)
    (d : E ≅ F) (e : A ≅ F) (h : e.hom = a.hom ≫ b.hom ≫ c.hom ≫ d.hom) :
    d.hom ≫ e.inv = c.inv ≫ b.inv ≫ a.inv := by
  have hi : e = a ≪≫ b ≪≫ c ≪≫ d := Iso.ext h
  rw [hi]
  simp only [Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- Successive quotient compatibility of the fixed inverse restriction mate.
Source: blueprint finite Hom proof, final successive-quotient paragraph
(blueprint: lem-coef-finite-hom-site-quotient-coherence).
Proof: normalized ordinary restriction comparisons compose because both composites fix the
same local generators. Exact derived-square composition descends this equality. The
adjunction mate composition formula identifies the three scalar-extension mates. Invert
this identity and cancel the etale associator to obtain the required equation. -/
theorem finiteHomSiteQuotientCoherence {n m : ℕ} (h : m ≤ n) :
    CoefFiniteHomQuotientCoherence l E X h := by
  intro r k T
  exact invert_fourfold
    ((finiteHomIntrinsicAssoc l E X h k).app ((finiteHomNu l E X n).obj T)).symm
    ((coefficientFiniteQuotientDerived l E X k).mapIso
      ((asIso (finiteHomSiteBeta l E X h)).app T))
    ((asIso (finiteHomSiteBeta l E X k)).app ((finiteHomEtaleReduction l E X h).obj T))
    ((finiteHomNu l E X r).mapIso ((finiteHomEtaleAssoc l E X h k).app T))
    ((asIso (finiteHomSiteBeta l E X (k.trans h))).app T)
    (beta_chain l E X h k T)

end WeilConjectures
