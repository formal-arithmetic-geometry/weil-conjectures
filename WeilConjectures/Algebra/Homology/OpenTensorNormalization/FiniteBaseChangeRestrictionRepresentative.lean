/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteBaseChangeRestrictionLocalizationStep

/-! A resolving-complex specialization of the finite restriction square.

This is the representative calculation in the proof of the finite restriction
coherence theorem.  It is separated from the localization step so that the
ordinary pin and model equations can be checked independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- The displayed restriction square on objects represented by resolving
complexes. -/
theorem finite_base_change_restriction_representative
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)
    (P : CochainComplex (FiniteModules A X) ℤ)
    (hP : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P)) :
    let r := Functor.isoWhiskerRight
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
      e.realizeU.derived ≪≫ e.openPull
    let M := DerivedCategory.Q.obj P
    e.pullU.hom.app ((finitePull A j).obj M) ≫
        o.gUPull.derived.map (r.hom.app M) ≫
        o.theta.inv.app (e.realizeX.derived.obj M) =
      e.realizeU'.derived.map
          ((Functor.mapDerivedCategorySquareIso
            (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)).hom.app M) ≫
        e.openPull'.hom.app ((finitePull A g).obj M) ≫
        o.opens.jStar'.map (e.pull.hom.app M)  := by
  let P₀ := (finiteComplexRealization e.realizeX).obj P
  let B := o.gPull.derived.map
      (e.realizeX.equivalence.functor.mapDerivedCategoryFactors.hom.app P) ≫
    derivedPullbackComplexComparison o.gPull.ordinary o.gPull.derived o.gPull.epsilon P₀
  have : IsIso (derivedPullbackComplexComparison o.gPull.ordinary o.gPull.derived
      o.gPull.epsilon P₀) := o.gPull.flat P₀ hP
  have : IsIso B := inferInstance
  apply (cancel_mono (o.opens.jStar'.map B)).1
  exact finite_base_change_restriction_localization_step A gU j' j g sq o e P hP

end SheafOfModules.OpenTensorNormalization
