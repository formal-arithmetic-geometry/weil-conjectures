/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSourceEvaluation
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Localization transports pro-etale coefficient-normalization squares

Source: Stacks Tags 03DA and 098K. All coefficient and localization comparisons
are the canonical derived mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) (B B' : Type (u + 1)) [CommRing B] [CommRing B']
end AlgebraicGeometry.Scheme

section TransportHelpers

-- Cache the existence of sheafification in the private calculations. Repeatedly
-- searching for it reconstructs the same essentially-small-site instance.

attribute [local instance] etaleWeakSheafifyCache proetWeakSheafifyCache
  etaleOverWeakSheafifyCache proetOverWeakSheafifyCache

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

variable (U : X.ProEt)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

end AlgebraicGeometry.Scheme

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
end AlgebraicGeometry.Scheme
end TransportHelpers

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
