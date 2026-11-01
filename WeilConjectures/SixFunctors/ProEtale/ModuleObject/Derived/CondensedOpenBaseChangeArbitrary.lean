/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-! # Condensed open-extension base change over arbitrary schemes

Source: Stacks Project, Tags 04J0, 03DI, 03DJ and 04VG; the current blueprint,
`sec-six-functors-basics/sk-prop-open-coefficients/thm-sfb-dc-open-base-change-iso.proof.md`.
(blueprint: lem-sp-condensed-open-base-change-arbitrary)

The underived arrow is the existing internal-module mate, specialized to the chosen
fibre product. The derived pullbacks here are exact termwise descents on ordinary
unbounded derived categories. No boundedness, constructibility or base-field condition
is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The fibre-product square used by condensed open-extension base change. Its chosen
identification is the identity of the already chosen scheme fibre product.
Source: Stacks Tag 04J0 (blueprint: lem-sp-condensed-open-base-change-arbitrary). -/
noncomputable def openBaseChangePullbackSquare {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (a : Z' ⟶ Z) :
    ChosenCartesianSquare (pullback.fst j a) (pullback.snd j a) j a where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _

/-- The specified underived arrow `b : j'_! a_U^* ⟶ a^* j_!`, reusing the canonical
internal-module mate. Its adjoint is `a_U^*(η_j)` followed by the square comparison
`a_U^* j^* ≅ j'^* a^*`, built from `upperStarComp`.
Source: Stacks Tags 04J0 and 03DI
(blueprint: lem-sp-condensed-open-base-change-arbitrary). -/
noncomputable abbrev condensedOpenBaseChangeMap
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (a : Z' ⟶ Z) :
    upperStar Λ.X (pullback.fst j a) ⋙ openImmersionLowerShriek Λ.X (pullback.snd j a) ⟶
      openImmersionLowerShriek Λ.X j ⋙ upperStar Λ.X a :=
  InternalModuleOperations.internalBaseChange Λ.X (openBaseChangePullbackSquare j a)

private theorem internalSquare_comparison
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U' U T' T : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} (sq : ChosenCartesianSquare g' j' j g) :
    InternalModuleOperations.internalSquare Λ.X sq =
      upperStarSquareComparison Λ.X sq.toCommSq.flip := by
  rfl

section UnderivedProof

attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  openImmersionLowerShriek openImmersionLowerShriekUpperStarAdjunction
  upperStarComp InternalModuleOperations.internalSquare

set_option maxHeartbeats 2000000 in
-- Concrete adjunction types require additional elaboration heartbeats.
/-- The specified open-extension mate is invertible for any scheme morphism `a` and
any commutative condensed coefficient ring.
Source: Stacks Tags 04J0, 03DI and 03DJ; the current blueprint open base-change proof
(blueprint: lem-sp-condensed-open-base-change-arbitrary).

Proof: (1) The map `b` is `mateEquiv.symm` of the square comparison
`θ : a_U^* j^* ≅ j'^* a^*` (`internalSquare`, built from `upperStarComp`), so its
mate under `j_! ⊣ j^*` and `j'_! ⊣ j'^*` is `θ`; `θ` is `upperStarSquareComparison`
of the transposed square. (2) By `exchangeRight_eq_mateEquiv`, the mate of `θ` under
`a^* ⊣ a_*` and `a_U^* ⊣ a_{U,*}` is `lowerStarBaseChange` `ρ : j^* a_* ⟶ a_{U,*} j'^*`
of the transposed pullback square; `lem-a1-condensed-weakly-etale-exchange` makes it
invertible, since the open immersions `j` and `j'` are weakly etale.
(3) `iterated_mateEquiv_conjugateEquiv` identifies `ρ` with the adjoint conjugate of `b`
under the composite adjunctions; `conjugateEquiv_of_iso` reflects invertibility back to
`b`. Only openness of `j` and the Cartesian square were used. -/
theorem isIso_condensedOpenBaseChangeMap
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (a : Z' ⟶ Z) :
    IsIso (condensedOpenBaseChangeMap Λ j a) := by
  let sq := openBaseChangePullbackSquare j a
  let b := InternalModuleOperations.internalBaseChange Λ.X sq
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ.X j
  let adj' := openImmersionLowerShriekUpperStarAdjunction Λ.X (pullback.snd j a)
  let adjU := upperStarLowerStarAdjunction Λ.X (pullback.fst j a)
  let adjA := upperStarLowerStarAdjunction Λ.X a
  have hθ : (mateEquiv adj adj' (.mk _ _ _ _ b)).natTrans =
      (InternalModuleOperations.internalSquare Λ.X sq).hom := by
    exact congrArg TwoSquare.natTrans ((mateEquiv adj adj').apply_symm_apply _)
  have hρ : (mateEquiv adjA adjU
      (.mk _ _ _ _ (InternalModuleOperations.internalSquare Λ.X sq).hom)).natTrans =
      lowerStarBaseChange Λ.X sq.toCommSq.flip := by
    rw [lowerStarBaseChange, Adjunction.exchangeRight_eq_mateEquiv]
    rw [internalSquare_comparison]
  have h := iterated_mateEquiv_conjugateEquiv adj adj' adjU adjA (.mk _ _ _ _ b)
  change (mateEquiv adjA adjU
    (.mk _ _ _ _ (mateEquiv adj adj' (.mk _ _ _ _ b)).natTrans)).natTrans = _ at h
  rw [hθ, hρ] at h
  have : IsIso (lowerStarBaseChange Λ.X sq.toCommSq.flip) :=
    isIso_lowerStarBaseChange_of_isPullback Λ.X (IsPullback.of_hasPullback j a).flip
  have : IsIso (conjugateEquiv (adj.comp adjA) (adjU.comp adj') b) := h ▸ this
  exact conjugateEquiv_of_iso (adj.comp adjA) (adjU.comp adj') b

end UnderivedProof

/-- The inverse of the specified underived mate. The data are the inverse of the map
just proved invertible, rather than a choice of an unspecified comparison.
Source: Stacks Tag 04J0 (blueprint: lem-sp-condensed-open-base-change-arbitrary). -/
noncomputable def condensedOpenBaseChangeIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (a : Z' ⟶ Z) :
    openImmersionLowerShriek Λ.X j ⋙ upperStar Λ.X a ≅
      upperStar Λ.X (pullback.fst j a) ⋙ openImmersionLowerShriek Λ.X (pullback.snd j a) :=
  (@asIso _ _ _ _ (condensedOpenBaseChangeMap Λ j a)
    (isIso_condensedOpenBaseChangeMap Λ j a)).symm

/-- The natural isomorphism `β : La^* j_! ≅ j'_! La_U^*` on ordinary unbounded derived
categories, obtained by localizing `b⁻¹` termwise and using the normalized exact-derived
composition comparisons at its endpoints. Here `La^*` means the exact termwise descent.
Its inverse therefore localizes `b` with the same composition comparisons.
Source: Stacks Tag 04VG and the current blueprint open base-change proof, first paragraph
(blueprint: lem-sp-condensed-open-base-change-arbitrary). -/
noncomputable def condensedOpenBaseChangeDerivedIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (a : Z' ⟶ Z) :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙
        (upperStar Λ.X a).mapDerivedCategory ≅
      (upperStar Λ.X (pullback.fst j a)).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ.X (pullback.snd j a)).mapDerivedCategory :=
  letI := comp_preservesFiniteLimits (openImmersionLowerShriek Λ.X j) (upperStar Λ.X a)
  letI := comp_preservesFiniteColimits (openImmersionLowerShriek Λ.X j) (upperStar Λ.X a)
  letI := comp_preservesFiniteLimits (upperStar Λ.X (pullback.fst j a))
    (openImmersionLowerShriek Λ.X (pullback.snd j a))
  letI := comp_preservesFiniteColimits (upperStar Λ.X (pullback.fst j a))
    (openImmersionLowerShriek Λ.X (pullback.snd j a))
  (Functor.mapDerivedCategoryCompIso (openImmersionLowerShriek Λ.X j)
    (upperStar Λ.X a)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (condensedOpenBaseChangeIso Λ j a) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ.X (pullback.fst j a))
          (openImmersionLowerShriek Λ.X (pullback.snd j a))

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  condensedOpenBaseChangeDerivedIso condensedOpenBaseChangeIso

set_option maxHeartbeats 2000000 in
-- Specializing abstract exact functors compares the concrete module-category presentations.
end AlgebraicGeometry.ProEtale.CondensedRing
