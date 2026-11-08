/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import Mathlib.CategoryTheory.Adjunction.Comma

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Universal normalization arrows on etale source sites

Source: Stacks Project, Tags 06YY, 03ED and 09BV.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite
-- The following elementary helpers reproduce the universal-factorization and square
-- transport proofs of NormalizedDerivedIsomorphismTransport, without importing its
-- downstream scalar-extension and proper-base-change applications.
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

namespace CategoryTheory.StructuredArrow
variable {C : Type u} [Category.{v} C] {D : Type t} [Category.{w} D]
  {R : C ⥤ D} {A A' : D} {K K' : C}
  {d : A ⟶ R.obj K} {d' : A' ⟶ R.obj K'}
end CategoryTheory.StructuredArrow

namespace AlgebraicGeometry.Scheme

/-- The canonical coefficient mate for etale inverse image, localized exactly.
Source: Stacks Tags 03DA and 03ED.
(blueprint: def-weil-pbc-etale-universal-normalization). -/
def etaleNormalizationCoefficients {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    normalizationRestrict Y.smallEtaleTopology q ⋙
        (Etale.upperStar (ModuleCat.{t + 1} R) f).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{t + 1} S) f).mapDerivedCategory ⋙
        normalizationRestrict Z.smallEtaleTopology q := by
  letI : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback f
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology Z.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{t + 1} R) f).Additive
    infer_instance
  letI : (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology Z.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{t + 1} S) f).Additive
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology Z.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{t + 1} R) f)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} R) Y.smallEtaleTopology Z.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{t + 1} R) f)
    infer_instance
  letI : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology Z.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{t + 1} S) f)
    infer_instance
  letI : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      (ModuleCat.{t + 1} S) Y.smallEtaleTopology Z.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{t + 1} S) f)
    infer_instance
  exact Functor.mapDerivedCategorySquareIso
    (normalizationPullbackIso Y.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      Z.smallEtaleTopology q)

/-- A specified coefficient arrow is universal on source sites and has the canonical
restriction coherence. This contains no isomorphism-presheaf map.
Source: Stacks Tags 06YY and 03ED.
(blueprint: def-weil-pbc-etale-universal-normalization). -/
structure EtaleUniversalNormalization (Y : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} R))}
    {C' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S))}
    (d : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj C') : Prop where
  universal : ∀ U : Y.Etale, Nonempty (StructuredArrow.IsUniversal
    (StructuredArrow.mk (etaleIsomorphismNormalizationArrow Y q d U)))
  coherence : ∀ {U V : Y.Etale} (f : U ⟶ V),
    (localIsomorphismRestrictionComp Y R f).inv.app C ≫
        etaleIsomorphismNormalizationArrow Y q d U =
      (Etale.upperStar (ModuleCat.{t + 1} R) f.left).mapDerivedCategory.map
          (etaleIsomorphismNormalizationArrow Y q d V) ≫
        (etaleNormalizationCoefficients f.left q).hom.app
          ((localIsomorphismRestriction Y S V).obj C') ≫
        (normalizationRestrict U.left.smallEtaleTopology q).map
          ((localIsomorphismRestrictionComp Y S f).inv.app C')

end AlgebraicGeometry.Scheme
