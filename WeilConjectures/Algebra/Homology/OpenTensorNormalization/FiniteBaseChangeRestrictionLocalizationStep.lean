/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Localization of the finite restriction representative.
(blueprint: lem-sf-finite-base-change-restriction-localization-step)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- Localize the ordinary θ₀/pin/mate identity to the derived representative.

Source: the localization and model-equation part of
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md`.
Proof: expand the two finite pull pins and the two finite open pins on `P` and on
its fixed-scalar pullback along `g`. Use naturality of the realization factors to
transport the complex pin identity through the three square compositors. Finally
apply `Operations.theta_model` to the resolving complex. In detail, map the
ordinary square degreewise to complexes, then through `DerivedCategory.Q`.
Use the two pull pin model equations and the restriction parts of the two open
pin model equations. Naturality moves the realization factor through the
localized ordinary square. The exact-functor compositor factorization identifies
the localized fixed-scalar square with the three derived compositors. The
conclusion is the resulting identity after postcomposition with the model map;
its invertibility and cancellation are proved by the caller.
First apply complex-morphism extensionality to `hOrd` in every degree, using
the definition of `NatTrans.mapHomologicalComplex`. This gives equality of the
complete two pin-square cochain maps. More explicitly, write `F_j,F_h` for the
ordinary finite pullbacks along `j,gU`,
`E` for the U'-realization, `φ` for exact localization factors, and `a` for the
pullback complex comparison. Append the invertible factor `φ_{I'}(G(P₀))` to
both sides of the conclusion, where `P₀` is the X-realization of `P`. Naturality
of `theta.inv` at `φ_{E_X}(P)` and the inverse form of `theta_model P₀ hP`
replace the left theta tail by `D(H)(φ_I(P₀))`, then `a_H(I(P₀))`, then
`Q(θ₀⁻¹(P₀))`. The open-pin model at `P`, the pullU-pin model at `F_j(P)`,
and naturality of `a_H` then turn the entire left route into `C ≫ Q(α_P)`,
where `α_P` is the complex map whose components are the left side of `hOrd`, and
`C = D(E)(D(F_h)(φ_{F_j}(P)) ≫ φ_{F_h}(F_j(P))) ≫ φ_E(F_h(F_j(P)))`.
For the right route, the pull-pin model at `P` followed by factor naturality
moves `I'` through its ordinary comparison; the open'-pin model at `F_g(P)`
then leaves the exact square compositor. Expand its definition and use
`mapDerivedCategoryNatIso_fac` and
`mapDerivedCategoryCompIso_hom_app_factors` on its two routes. They give the
same prefix `C` followed by `Q(β_P)`, where `β_P` is the right complex map
in the degreewise hypothesis. Applying `Q.map` to the cochain equality equates
these tails. Finally cancel
only the appended exact restriction factor. No flatness cancellation of `B`
is performed in this lemma.
(blueprint: lem-sf-finite-base-change-restriction-localization-step) -/
theorem finite_base_change_restriction_localization_step
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)
    (P : CochainComplex (FiniteModules A X) ℤ)
    (hP : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hOrd : ∀ n : ℤ,
      e.pullU_pin.ordinary.hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj (P.X n)) ≫
        o.gUPull.ordinary.map (e.open_pin.star.hom.app (P.X n)) ≫
        o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj (P.X n)) =
      e.realizeU'.equivalence.functor.map
          ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom.app (P.X n)) ≫
        e.open'_pin.star.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj (P.X n)) ≫
        (restrict .ordinary j' (finiteInput A gU j' j g sq).S).map
          (e.pull_pin.ordinary.hom.app (P.X n))) :
    let r := Functor.isoWhiskerRight
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
      e.realizeU.derived ≪≫ e.openPull
    let M := DerivedCategory.Q.obj P
    let B := o.gPull.derived.map
      (e.realizeX.equivalence.functor.mapDerivedCategoryFactors.hom.app P) ≫
      derivedPullbackComplexComparison o.gPull.ordinary o.gPull.derived
        o.gPull.epsilon ((finiteComplexRealization e.realizeX).obj P)
    (e.pullU.hom.app ((finitePull A j).obj M) ≫
        o.gUPull.derived.map (r.hom.app M) ≫
        o.theta.inv.app (e.realizeX.derived.obj M)) ≫
      o.opens.jStar'.map B =
      (e.realizeU'.derived.map
          ((Functor.mapDerivedCategorySquareIso
            (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)).hom.app M) ≫
        e.openPull'.hom.app ((finitePull A g).obj M) ≫
        o.opens.jStar'.map (e.pull.hom.app M)) ≫
      o.opens.jStar'.map B := by sorry

end SheafOfModules.OpenTensorNormalization
