/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.Terms

/-! # The chain-level equation of the finite restriction square, as a structure -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization.RestrictionSquare

variable (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)

/-- The chain-level equation `h_total` at `P`, `Q`, as a proposition with syntactically
fixed statement. (blueprint: lem-sf-finite-restriction-representative-square) -/
structure TotalEq (P Q : CochainComplex (FiniteModules A X) ℤ) : Prop where
  /-- The equation. -/
  eq :
    let R := (finiteInput A gU j' j g sq).R
    letI : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
    let fc := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)
    let h := (restrict .ordinary j R).mapHomologicalComplex (.up ℤ)
    let v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)
    (finiteComplexRealization e.realizeU).map
          (inv (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
            (ProEtale.upperStar (ModuleCat.{u + 1} A) j)).app P).app Q)) ≫
        v.app (finiteTotal A X P Q) ≫
        h.map (e.tensorX_pin.totalIso P Q).hom =
      (e.tensorU_pin.totalIso (fc.obj P) (fc.obj Q)).hom ≫
        (total (restrictRing .ordinary j R)).map
          (Prod.mkHom (v.app P) (v.app Q)) ≫
        totalMap o.tensorX o.tensorU (restrict .ordinary j R) o.restrictionTensor
          o.tensorComparison.comm ((finiteComplexRealization e.realizeX).obj P)
            ((finiteComplexRealization e.realizeX).obj Q)

end SheafOfModules.OpenTensorNormalization.RestrictionSquare
