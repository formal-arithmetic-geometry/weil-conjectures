/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedOpenDerivedCalculus
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Integral open-proper exchange

Source: Stacks Project, more-etale.tex, Sections 63.8--63.9 (Tag 0F7A),
exchange of extension by zero and proper pushforward
(blueprint: def-pur-integral-open-proper-exchange).

The map below is the adjunction transpose of the identity-normalized composite of
the canonical open restriction of derived direct image with the open adjunction unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! The coefficient and geometric hypotheses in the blueprint statement. -/

/-- The integral open-proper exchange map, defined by the specified adjunction mate.

Source: Stacks Project, more-etale.tex, Sections 63.8--63.9 (Tag 0F7A),
exchange of extension by zero and proper pushforward
(blueprint: def-pur-integral-open-proper-exchange).

For the Cartesian square `v ≫ p = pV ≫ u`, the canonical restriction map
`u^* Rp_* → RpV_* v^*` is evaluated on `v_! L` and followed by the image under
`RpV_*` of the open unit `L → v^*v_!L`.  Transposition under `u_! ⊣ u^*`
defines the displayed map.  The construction is natural in `L` by naturality of
the unit, restriction transformation, and adjunction hom-equivalence.
-/
noncomputable def integralOpenProperExchange
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (_hple : p ≠ ell)
    (k : Type u) [Field k] (_hk : ringChar k = p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (_hΛ : IsAdmissibleCoefficient (Profinite.padicIntegersRingObj ell E.1))
    {U V X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (v : V ⟶ X) (u : U ⟶ Y) (f : X ⟶ Y) (fV : V ⟶ U)
    [IsOpenImmersion v.left] [QuasiCompact v.left]
    [IsOpenImmersion u.left] [QuasiCompact u.left]
    [IsProper f.left]
    (sq : IsPullback v.left fV.left f.left u.left)
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) V.left))) :
    (openImmersionLowerShriek
        (Profinite.padicIntegersRingObj ell E.1) u.left).mapDerivedCategory.obj
        ((lowerStar (Profinite.padicIntegersRingObj ell E.1) fV.left).rightDerivedFunctor.obj L) ⟶
      (lowerStar (Profinite.padicIntegersRingObj ell E.1) f.left).rightDerivedFunctor.obj
        ((openImmersionLowerShriek
          (Profinite.padicIntegersRingObj ell E.1) v.left).mapDerivedCategory.obj L) :=
  let Λ := Profinite.padicIntegersRingObj ell E.1
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ u.left
  let ρ := derivedDirectImageOpenRestriction Λ sq.toCommSq
  letI : IsIso ρ := (derivedOpenRestrictionNormalization Λ sq).derived_isIso
  (adj.homEquiv _ _).symm
    ((lowerStar Λ fV.left).rightDerivedFunctor.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v.left).unit.app L) ≫
      (asIso ρ).inv.app
        ((openImmersionLowerShriek Λ v.left).mapDerivedCategory.obj L))

/-- The integral open-proper exchange map is natural in `L`.

Source: Stacks Project, more-etale.tex, Sections 63.8--63.9 (Tag 0F7A),
`lemma-shriek-proper-and-open` ("functorially in `K`")
(blueprint: def-pur-integral-open-proper-exchange).

Proof: Write `η_v` for the unit of the derived adjunction `v_! ⊣ v^*`, `ρ` for the canonical
derived open restriction `u^* Rp_* ⟶ RpV_* v^*` and `adj` for the derived adjunction
`u_! ⊣ u^*`.
1. The map `RpV_*(η_v L) ≫ ρ⁻¹(v_! L) : RpV_* L ⟶ u^* Rp_* v_! L` is natural in `L`:
   `η_v` is a natural transformation, `RpV_*` is a functor, and `ρ⁻¹` is a natural
   transformation (the inverse of the natural isomorphism `ρ`) whiskered by `v_!`.
2. For `φ : L ⟶ L'`, naturality of `adj.homEquiv` in the source (`homEquiv_naturality_left_symm`)
   rewrites `u_!(RpV_* φ) ≫ (adj.homEquiv _ _).symm g'` as
   `(adj.homEquiv _ _).symm (RpV_* φ ≫ g')`, and naturality in the target
   (`homEquiv_naturality_right_symm`) rewrites `(adj.homEquiv _ _).symm g ≫ Rp_*(v_! φ)` as
   `(adj.homEquiv _ _).symm (g ≫ u^*(Rp_*(v_! φ)))`.
3. By step 1 the two arguments of `(adj.homEquiv _ _).symm` agree, which gives the square.
-/
theorem integralOpenProperExchange_naturality
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hple : p ≠ ell)
    (k : Type u) [Field k] (hk : ringChar k = p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hΛ : IsAdmissibleCoefficient (Profinite.padicIntegersRingObj ell E.1))
    {U V X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (v : V ⟶ X) (u : U ⟶ Y) (f : X ⟶ Y) (fV : V ⟶ U)
    [IsOpenImmersion v.left] [QuasiCompact v.left]
    [IsOpenImmersion u.left] [QuasiCompact u.left]
    [IsProper f.left]
    (sq : IsPullback v.left fV.left f.left u.left)
    {L L' : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) V.left))}
    (φ : L ⟶ L') :
    (openImmersionLowerShriek
        (Profinite.padicIntegersRingObj ell E.1) u.left).mapDerivedCategory.map
        ((lowerStar (Profinite.padicIntegersRingObj ell E.1) fV.left).rightDerivedFunctor.map φ) ≫
      integralOpenProperExchange p ell hple k hk E hΛ v u f fV sq L' =
    integralOpenProperExchange p ell hple k hk E hΛ v u f fV sq L ≫
      (lowerStar (Profinite.padicIntegersRingObj ell E.1) f.left).rightDerivedFunctor.map
        ((openImmersionLowerShriek
          (Profinite.padicIntegersRingObj ell E.1) v.left).mapDerivedCategory.map φ) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
