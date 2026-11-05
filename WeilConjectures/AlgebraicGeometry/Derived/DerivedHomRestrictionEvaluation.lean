/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedRestrictionHomPresheaf
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Evaluation commutes with restriction of derived Hom coefficients

Source: Stacks Project, Tags 03DA, 098K and 0F63.
(blueprint: lem-weil-pbc-derived-hom-restriction-evaluation).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
section Conjugation
variable {P Q R S : Type*} [Category P] [Category Q] [Category R] [Category S]
    (SV : P ⥤ Q) (SW : R ⥤ S) (M : R ⥤ P) (L : S ⥤ Q)
    {Av Dv : P} {Aw Dw : R} {Aq Dq : Q} {As Ds : S}
    (δA : SV.obj Av ≅ Aq) (δD : SV.obj Dv ≅ Dq)
    (εA : SW.obj Aw ≅ As) (εD : SW.obj Dw ≅ Ds)
    (σA : Av ≅ M.obj Aw) (σD : Dv ≅ M.obj Dw)
    (cA : Aq ≅ L.obj As) (cD : Dq ≅ L.obj Ds)
    (α : M ⋙ SV ≅ SW ⋙ L)
    (hA : δA.hom ≫ cA.hom = SV.map σA.hom ≫ α.hom.app Aw ≫ L.map εA.hom)
    (hD : δD.hom ≫ cD.hom = SV.map σD.hom ≫ α.hom.app Dw ≫ L.map εD.hom)
end Conjugation

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
