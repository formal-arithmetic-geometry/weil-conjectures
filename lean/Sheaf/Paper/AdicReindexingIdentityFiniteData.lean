/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

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
Finite-stage certificate for the identity normalization.  It records the identity
calculation only on the finite coefficient representatives occurring in
`integralRealizationAgreement`; the passage to arbitrary common-stage objects is a
separate theorem.  Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-lem-sf-adic-reindexing-identity-finite-certificate)
-/
structure NormalizedReindexingFiniteCertificate (C : FamilyCore l D) where
  equation : ∀ (T : GeometricSpace D)
      (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (K : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) T.base.left),
    letI := (C.data T).units
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := T.base.left) E
    let Q₀ := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) T.base.left
    let M := I.obj (Q₀.obj K)
    (C.comparison T T (Iso.refl _)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleId T) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((ordinary l T.base.left (C.data T).realization).obj M) =
    (ordinary l T.base.left (C.data T).realization).map ((C.sourceId T).hom.app M)


end WeilConjectures.AdicQbarRealization
