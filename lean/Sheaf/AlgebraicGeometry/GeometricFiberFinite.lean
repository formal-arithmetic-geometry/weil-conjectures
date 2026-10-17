/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.LerayBounded
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Finite-coefficient geometric-fibre formula

Source: Stacks Project, Tag 0DDF; SGA 4, Expose XII, Corollaire 5.2(iii);
blueprint `sec-proper-base-change/sk-thm-properbasechange/`
`cor-weil-pbc-geometric-fiber-finite.md`
(blueprint: cor-weil-pbc-geometric-fiber-finite).

The cohomological formula includes the two endpoint identifications explicitly:
global sections of the source are the geometric stalk, and global sections of the
target are the cohomology of the geometric fibre. The map between these presentations
is the degree-q base-change map, not an unspecified isomorphism between groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Finite-coefficient proper base change at a geometric point, Stacks Tag 0DDF(2).
(blueprint: cor-weil-pbc-geometric-fiber-finite)

Proof: form the pullback square with projections i_y and a_y (def-pc-fibre-product,
def-weil-pbc-cartesian-square). The additive group of the finite coefficient ring is
annihilated by its positive cardinality, hence so is every cohomology sheaf of K.
After forgetting coefficients K therefore has torsion cohomology
(def-weil-pbc-etale-sheaves, def-weil-pbc-derived-categories). Apply
thm-weil-pbc-bounded-below to the underlying abelian complex. Compatibility of the
exchange map with forgetting coefficients and reflection of isomorphisms
(lem-weil-pbc-exchange-forget-coefficients) give the stated module-linear isomorphism. -/
theorem isIso_geometricFiber_finite
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback f y).toCommSq).app K) := by sorry

/-- The geometric-stalk formula, with its endpoint comparisons and its base-change map.
Source: Stacks Tag 0DDF(1); SGA 4 XII, Corollaire 5.2(iii).
(blueprint: cor-weil-pbc-geometric-fiber-finite)

Proof: apply isIso_geometricFiber_finite to F in degree zero. Exactness of y^{-1}
identifies the source homology sheaf with y^{-1} R^q f_* F
(def-weil-pbc-inverse-image, def-weil-pbc-direct-image). Its sections are the stalk
at y (def-weil-pbc-geometric-stalks, lem-weil-pbc-geometric-point-pullback-stalk).
Global sections on Spec Omega are exact, so they commute with cohomology.
Composition of derived direct image and derived global sections (lem-kun-leray-bdd)
identifies the target sections with H^q(X_y, i_y^{-1} F)
(def-weil-pbc-etale-cohomology). These comparisons transport the global sections of
the degree-q exchange map to the displayed stalk-to-fibre map. Functors and transport
by isomorphisms preserve isomorphisms. Finiteness of F is not needed in this argument. -/
theorem geometricFiber_finite_stalk_formula
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsFiniteSheaf F]
    (q : ℕ) :
    ∃ (sourceIso :
        (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          ((baseChangeSourceFunctor Λ y f q).obj F) ≅
        ((Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          (higherDirectImage Λ f q F))
      (targetIso :
        (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          ((baseChangeTargetFunctor Λ (pullback.fst f y) (pullback.snd f y) q).obj F) ≅
        (cohomology (ModuleCat.{u + 1} Λ) (pullback f y) q).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F))),
      IsIso (sourceIso.inv ≫
        (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
          (baseChangeHomologyMap Λ (IsPullback.of_hasPullback f y) q F) ≫ targetIso.hom) := by sorry

end AlgebraicGeometry.Etale
