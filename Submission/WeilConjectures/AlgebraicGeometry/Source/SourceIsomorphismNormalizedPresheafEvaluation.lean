/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Submission.WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
import Submission.WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedHomEvaluationFunctoriality
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleNormalizationSquareTransport
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Evaluation of a specified normalized Isom presheaf map

Source: Stacks Project, Tags 09BV and 0F63; functoriality of comparison and evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Pull a coefficient-normalization arrow to an etale object, using the canonical mate.
Source: Stacks Tags 03DA and 03ED.
(blueprint: def-weil-pbc-etale-isomorphism-normalization-arrow). -/
def etaleIsomorphismNormalizationArrow (Y : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} R))}
    {D : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S))}
    (d : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj D) (U : Y.Etale) :
    (localIsomorphismRestriction Y R U).obj C ⟶
      (normalizationRestrict U.left.smallEtaleTopology q).obj
        ((localIsomorphismRestriction Y S U).obj D) := by
  letI : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      Y.smallEtaleTopology U.left.smallEtaleTopology := by
    exact AlgebraicGeometry.Etale.isContinuous_overPullback U.hom
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology U.left.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{t + 1} R) U.hom).Additive
    infer_instance
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology U.left.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{t + 1} S) U.hom).Additive
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{t + 1} R) U.hom)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{t + 1} R) U.hom)
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{t + 1} S) U.hom)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{t + 1} S) U.hom)
    infer_instance
  exact (localIsomorphismRestriction Y R U).map d ≫
    (Functor.mapDerivedCategorySquareIso
      (normalizationPullbackIso Y.smallEtaleTopology
        (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
        U.left.smallEtaleTopology q)).hom.app D

end AlgebraicGeometry.Scheme
universe u
section EvaluationHelpers

-- Cache the existence of sheafification in the private calculations. Repeatedly
-- searching for it reconstructs the same essentially-small-site instance.
private theorem etaleWeakSheafifyCache
    (X : AlgebraicGeometry.Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} B) := inferInstance

private theorem proetWeakSheafifyCache
    (X : AlgebraicGeometry.Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} B) := inferInstance

private theorem etaleOverWeakSheafifyCache
    (X : AlgebraicGeometry.Scheme.{u}) (V : X.Etale)
    (B : Type (u + 1)) [CommRing B] :
    HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} B) := inferInstance

private theorem proetOverWeakSheafifyCache
    (X : AlgebraicGeometry.Scheme.{u}) (V : X.ProEt)
    (B : Type (u + 1)) [CommRing B] :
    HasWeakSheafify ((AlgebraicGeometry.Scheme.ProEt.topology X).over V)
      (ModuleCat.{u + 1} B) := inferInstance

attribute [local instance] etaleWeakSheafifyCache proetWeakSheafifyCache
  etaleOverWeakSheafifyCache proetOverWeakSheafifyCache

namespace CategoryTheory
section TransportSquare
variable {H S P Q : Type*} [Category H] [Category S] [Category P] [Category Q]
    (ER : H ⥤ P) (ES : S ⥤ Q) (RS : S ⥤ H) (RP : Q ⥤ P)
    (c : RS ⋙ ER ≅ ES ⋙ RP)
    {A D : H} {A' D' : S} {A₀ D₀ : P} {A₁ D₁ : Q}
    (δA : ER.obj A ≅ A₀) (δD : ER.obj D ≅ D₀)
    (εA : ES.obj A' ≅ A₁) (εD : ES.obj D' ≅ D₁)
    (dA : A ⟶ RS.obj A') (dD : D ⟶ RS.obj D')
    (dA₀ : A₀ ⟶ RP.obj A₁) (dD₀ : D₀ ⟶ RP.obj D₁)
    (hA : δA.hom ≫ dA₀ = ER.map dA ≫ c.hom.app A' ≫ RP.map εA.hom)
    (hD : δD.hom ≫ dD₀ = ER.map dD ≫ c.hom.app D' ≫ RP.map εD.hom)
end TransportSquare
end CategoryTheory

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (U : X.Etale)

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
end EvaluationHelpers

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
