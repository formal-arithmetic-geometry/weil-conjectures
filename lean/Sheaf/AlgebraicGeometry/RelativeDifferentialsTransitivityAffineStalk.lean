/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineChartUnit
public import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # RelativeDifferentialsTransitivityAffineStalk

Source: Stacks Project, Morphisms, Tags 01UX, 01UV, 01UT and 01US. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Hom

/-- The normalized algebraic transitivity sequence on affine charts is right exact on stalks.
Source: Stacks Project, Morphisms, Tags 01UX, 01UT, 01UV; Algebra, Tag 00CS.

Proof: choose affine triples U, V, W around each source point, shrinking successively
in the inverse images. The differential affine comparisons identify the middle and last
terms with the associated modules Omega(A/R) and Omega(A/B). The affine chart pullback
unit comparison, transported along the differential comparison on V, and the tensor
tilde base-change comparison identify the first term with tilde(A tensor_B Omega(B/R)).
The chart-unit theorem is stated for the ordinary pullback. Compare that pullback
with tensorPullback by uniqueness of their left adjunctions to the same pushforward;
the unit identity sends the explicit tensor unit to the ordinary pullback unit.
The resulting comparison and the tilde unit formula give the displayed normalization
on actual pulled-back db sections.
The universal derivation formulas determine the two arrows on a tensor db and on da;
these generate the source modules. Thus the comparison squares hold as sheaf morphisms.
KaehlerDifferential.exact_mapBaseChange_map and map_surjective give module exactness
and surjectivity. Principal restriction is localization; both arrow formulas commute
with it, including inverses by d(t^-1)=-t^-2 dt. The tilde stalk comparison therefore
identifies the stalk arrows with the localized algebraic arrows. If v(m)/s=0, multiply
by t outside the prime so that v(tm)=0; choose l with u(l)=tm. Then l/(ts) maps to m/s.
Conversely the composite is zero, and surjectivity follows by lifting a numerator.
Every point belongs to such a chart, giving the stalk assertions without finiteness,
flatness or smoothness. Identity arrows, zero modules and empty charts are included.
(blueprint: lem-a1-differential-transitivity-affine-stalk). -/
theorem relativeDifferentials_transitivity_affine_stalk
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a) :
      (∀ x : X,
        Function.Exact
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
            (g.relativeDifferentialsPullbackMap h))
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q) ∧
        Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q)) ∧
      (∀ (U : X.affineOpens) (V : Y.affineOpens) (W : S.affineOpens)
          (hUV : U.1 ≤ h ⁻¹ᵁ V.1) (hVW : V.1 ≤ g ⁻¹ᵁ W.1),
        ∃ θ : ((Modules.tensorPullback h).obj g.relativeDifferentials).restrict U.2.fromSpec ≅
            tilde ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
              (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))),
          (∀ b : Γ(Y, V.1),
            θ.hom.app ⊤
              ((Modules.sectionsRestrictFromSpecLinearEquiv
                ((Modules.tensorPullback h).obj g.relativeDifferentials) U.2).symm
                (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
                  (homOfLE hUV).op (g.relativeDifferentialsPullbackGenerator h V.1 b))) =
              tilde.toOpen ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))) ⊤
                  ((ModuleCat.extendRestrictScalarsAdj (h.appLE V.1 U.1 hUV).hom).unit.app
                    (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
                      (CommRingCat.KaehlerDifferential.d b))) ∧
          ∃ (uA : (ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)) ⟶
              CommRingCat.KaehlerDifferential
                ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))))
            (vA : CommRingCat.KaehlerDifferential
                ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))) ⟶
              CommRingCat.KaehlerDifferential (h.appLE V.1 U.1 hUV)),
            (∀ (a : Γ(X, U.1)) (b : Γ(Y, V.1)),
              uA (a • @id
                ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                  (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)))
                ((ModuleCat.extendRestrictScalarsAdj (h.appLE V.1 U.1 hUV).hom).unit.app
                  (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
                    (CommRingCat.KaehlerDifferential.d b))) =
                a • CommRingCat.KaehlerDifferential.d (h.appLE V.1 U.1 hUV b)) ∧
            (∀ a : Γ(X, U.1), vA (CommRingCat.KaehlerDifferential.d a) =
              CommRingCat.KaehlerDifferential.d a) ∧
            Function.Exact uA vA ∧ Function.Surjective vA ∧
            (Modules.restrictFunctor U.2.fromSpec).map
                (g.relativeDifferentialsPullbackMap h) ≫
              ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
                (fun _ hx ↦ hVW (hUV hx))).hom =
              θ.hom ≫ (tilde.functor Γ(X, U.1)).map uA ∧
            (Modules.restrictFunctor U.2.fromSpec).map q ≫
                (h.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV).hom =
              ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
                (fun _ hx ↦ hVW (hUV hx))).hom ≫ (tilde.functor Γ(X, U.1)).map vA) := by sorry

end AlgebraicGeometry.Scheme.Hom
