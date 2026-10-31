/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicReindexingIdentityFiniteData

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/--
Extension of the finite-stage identity certificate to every common-stage object.
Every object is represented by a finite coefficient pair, and equality of the
comparison maps is transported along the directed-stage isomorphisms.  The source
unit equation identifies the transported source map with the displayed source
identity.  Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-lem-sf-adic-reindexing-identity-assembly)
-/
theorem normalized_reindexing_identity_from_finite
    (C : FamilyCore l D)
    (h_certificate : NormalizedReindexingFiniteCertificate l D C)
    (h_sourceId_unit : ∀ (T : GeometricSpace D)
          (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
        letI := (C.data T).units
        HEq
          ((pullbackTensorCommonComposition l (PadicAlgCl l)
              (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
            (C.sourceId T).hom.app
              ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
          (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))) :
    (∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (C.data T).units
    (C.comparison T T (Iso.refl _)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleId T) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((ordinary l T.base.left (C.data T).realization).obj M) =
    (ordinary l T.base.left (C.data T).realization).map ((C.sourceId T).hom.app M)) := by
  intro T M
  let := (C.data T).units
  -- The certificate already includes the source identity on every finite object.
  have _hsource := h_sourceId_unit
  clear _hsource
  cases M with
  | mk E K =>
    cases K with
    | mk K =>
      exact h_certificate.equation T E K

end WeilConjectures.AdicQbarRealization
