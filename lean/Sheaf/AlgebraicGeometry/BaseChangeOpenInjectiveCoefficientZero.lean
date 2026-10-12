/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition

/-! # Open injective coefficient comparison

Source: Stacks Project, Tag 0F07, closed–open part of the proof.
(blueprint: lem-sbc-open-injective-coefficient-zero)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)
/-- A class that is a base-change image on V maps to zero after the open injective
coefficient embedding. This is the Leray part of the closed–open argument.

Source: Stacks Project, Tag 0F07, open summand in condition (3).
(blueprint: lem-sbc-open-injective-coefficient-zero)

Proof: put J = Injective.under (F restricted to V). The degree q source for J
vanishes since J is injective and q is positive. Naturality therefore sends the
assumed base-change image on V to zero in R^q(h composed with j')_* e_V^* J.
Apply the universal lower-degree hypothesis after the preliminary base change to T,
to the quasi-compact separated open immersion j:V -> T. In degree zero it identifies
e^* j_* J with j'_* e_V^* J. In degrees 1 through q-1 it implies that R^a j'_*
e_V^* J vanishes, since R^a j_* J vanishes by injectivity. The Leray edge map
R^q h_* e^* j_* J -> R^q(h composed with j')_* e_V^* J is consequently injective.
Compatibility of the edge map with the coefficient unit and target transition
identifies the image of the class under this injection with the zero just obtained.
Injectivity on stalks proves the asserted vanishing. The empty open causes no exception.
-/
theorem baseChange_open_injective_coefficient_eq_zero [IsAffine S]
    (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, UniversalBaseChangeProperty Λ p q')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    {T' : Scheme.{u}} (f : T' ⟶ T)
    [CompactSpace T'] [QuasiSeparatedSpace T']
    (ζ : baseChangeTargetStalk Λ p g q F x (Over.mk f))
    (V : T'.Opens) (hV : IsCompact (V : Set T'))
    (hζ : (baseChangeTargetStalkMap Λ p g q F x
      (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f)).hom ζ ∈
        Set.range (baseChangeStalkMap Λ p g q F x (Over.mk (V.ι ≫ f))).hom) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
      ((baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p)
        (pullback.snd (f ≫ g) p) q).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.ι).unit.app
          (((f)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
            ((V.ι)_*[ModuleCat.{u + 1} Λ]).map
              (Injective.ι (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj
                (((f)^*[ModuleCat.{u + 1} Λ]).obj F)))))).hom ζ = 0 := by sorry

end AlgebraicGeometry.Etale
