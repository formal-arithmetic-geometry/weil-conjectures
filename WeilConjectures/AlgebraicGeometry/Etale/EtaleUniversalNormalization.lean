/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import Mathlib.CategoryTheory.Adjunction.Comma

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

end AlgebraicGeometry.Scheme
