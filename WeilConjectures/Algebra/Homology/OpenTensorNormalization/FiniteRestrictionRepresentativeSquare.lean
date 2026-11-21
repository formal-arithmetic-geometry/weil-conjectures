/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.Assemble
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.Left
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.Right

/-! # Representative cancellation for the finite restriction square

## References

* Stacks Project, Tags 07A4 and 0GL1
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- Cancellation of the cochain model equations on resolving finite pairs. -/
theorem finite_restriction_representative_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)
    (h_total :
    let R := (finiteInput A gU j' j g sq).R
    letI : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
    let fc := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)
    let h := (restrict .ordinary j R).mapHomologicalComplex (.up ℤ)
    let v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)
    ∀ P Q : CochainComplex (FiniteModules A X) ℤ,
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
            ((finiteComplexRealization e.realizeX).obj Q))
    (P Q : CochainComplex (FiniteModules A X) ℤ)
    (hp : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hq : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj Q)) :
    let r := Functor.isoWhiskerRight
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
      e.realizeU.derived ≪≫ e.openPull
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    e.realizeU.derived.map
          (((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
            (ModuleCat.{u + 1} A) j).hom.app M).app N) ≫
        r.hom.app ((finiteTensor A X).obj (M, N)) ≫
        o.opens.jStar.map (e.tensorX.hom.app (M, N)) =
      e.tensorU.hom.app ((finitePull A j).obj M,
          (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj N) ≫
        o.tensorU.functor.map
          (CategoryTheory.Prod.mkHom (r.hom.app M) (e.openPull.hom.app N)) ≫
        o.tensorComparison.comparison.inv.app
          (e.realizeX.derived.obj M, e.realizeX.derived.obj N) :=
  (RestrictionSquare.squareEq_of_halves A gU j' j g sq o e P Q hp hq
    (RestrictionSquare.leftEq A gU j' j g sq o e P Q hp hq)
    (RestrictionSquare.rightEq A gU j' j g sq o e P Q hp hq) h_total).eq

end SheafOfModules.OpenTensorNormalization
