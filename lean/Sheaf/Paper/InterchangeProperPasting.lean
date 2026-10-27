/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.ProEtaleProperOpenInterchange
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Proper-map pasting of normalized proper-open interchange

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
Canonicity and associativity, first two sentences
(blueprint: lem-sfb-interchange-proper-pasting).

The comparisons below specialize the existing canonical derived-functor comparison,
and build the outer compactification using the existing postcomposition construction.
The statement retains the three normalization equations and both direct-image compositors.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical comparison `R(gf)_* ≅ Rg_* Rf_*` for pulled-back condensed coefficients.
It is the existing universal right-derived comparison, transported along `lowerStarComp`.
Exactness of `upperStar` supplies K-injective preservation through its recorded adjunction.
Thus on a K-injective representative and a resolution `j : f_*I → J`, its component is
`g_*j` under the resolution identifications, as in Stacks Tag 0D6E and
lem-weil-pbc-ringed-topoi-derived-pushforward-composition.
Source: blueprint sk-thm-sf-comp-composition, Canonicity and associativity
(blueprint: lem-sfb-interchange-proper-pasting). -/
noncomputable def interchangeDerivedLowerStarComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStar Λ (f ≫ g)).rightDerivedFunctor ≅
      (lowerStar Λ f).rightDerivedFunctor ⋙ (lowerStar Λ g).rightDerivedFunctor :=
  have : (lowerStar Λ f).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  (Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ g)
    (lowerStarComp Λ f g)).symm

variable {P P' Y B : Scheme.{u}} (p : P ⟶ Y) (h : P' ⟶ P) (i : Y ⟶ B)
  [IsOpenImmersion i] (c : Compactification.BoundaryCompactification (p ≫ i))
  (d : Compactification.BoundaryCompactification (h ≫ c.obj.obj.i))

/-- The outer compactification `P' → W' → B`, with open part `v` and proper part `s ≫ r`.
The commuting triangle is the composite of the two given triangles; quasi-compactness
is the already recorded quasi-compactness of `v`. No new compactification is chosen.
Source: blueprint sk-thm-sf-comp-composition, Canonicity and associativity
(blueprint: lem-sfb-interchange-proper-pasting). -/
def interchangeOuterCompactification :
    Compactification.BoundaryCompactification ((h ≫ p) ≫ i) :=
  ⟨⟨(d.obj.obj.postcomp c.obj.obj.g).copy
      ((Category.assoc h p i).trans
        ((congrArg (fun t => h ≫ t) c.obj.obj.comm).trans
          (Category.assoc h c.obj.obj.i c.obj.obj.g).symm)), d.obj.property⟩⟩

/-- Normalized proper-open interchange respects successive proper maps on the ordinary
unbounded module derived categories. The three input natural transformations are exactly
the normalized maps of det-sf-comp-composition-interchange (2); uniqueness there makes
these families natural. Neither their invertibility nor any restriction on the input
complex is assumed. The coefficient disjunction is precisely finite `E` or finite-valued Qbar.
Source: blueprint main-20261015, sk-thm-sf-comp-composition, Canonicity and associativity,
first two sentences (blueprint: lem-sfb-interchange-proper-pasting).

Proof plan (the seven steps of the node):
1. Apply det-sf-comp-composition-interchange (1) to both compactifications: the two
   squares and their outer rectangle are cartesian. Clause (2) supplies unique normalized
   arrows for all unbounded inputs, including the outer compactification.
2. Module pullback is exact by sk-prop-sfb-cartesian-coefficients. The exact open extension
   adjunction of det-sf-open-closed-sequence-ring-sheaf has invertible unit. Apply
   lem-weil-pbc-right-adjoint-preserves-kinjective to direct images and open restrictions.
3. Apply lem-sfb-proetale-open-restriction-counit to the three squares. Their restriction
   maps are the fiber-product identification on sections, with the same module actions.
4. Apply these identifications termwise on K-injectives using sk-def-sfb-module-derived-
   pushpull and lem-weil-pbc-exact-functor-derived-factorization, obtaining rho_r, rho_s,
   and rho_rs, precisely the canonical identifications in the normalization predicates.
5. The normalization of lem-weil-pbc-ringed-topoi-derived-pushforward-composition gives
   chi composed with i^* kappa_rs equal to kappa_ph composed with rho_rs, where
   chi = Rp_*(rho_s) composed with rho_r. On a K-injective representative the two maps
   are the same iterated fiber-product section identification, before localization.
6. Set F = Rr_*(J_A) composed with I_{Rh_*A}. Compose its restriction with chi and
   Rp_*Rh_* of the inverse v-unit. Naturality of rho_r at J_A and the two given
   normalization equations show that the result, after the i-unit, is the identity.
7. Conjugate F by kappa_rs inverse and i_!(kappa_ph). Step 5 and naturality of kappa_ph
   identify its outer normalization with the identity computed in step 6. Uniqueness
   in det-sf-comp-composition-interchange (2) identifies it with I'_A. Rearranging gives
   the displayed equality. Every factor is natural; no boundedness, finite Tor,
   constructibility, or localizing-closure condition was used.
-/
theorem interchangeProperPasting
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
            (Profinite.padicSubfieldCondensedRing ℓ E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    [P.Over (Spec (.of k))] [P'.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [B.Over (Spec (.of k))]
    [c.obj.obj.Z.Over (Spec (.of k))] [d.obj.obj.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (P ↘ Spec (.of k))] [QuasiCompact (P ↘ Spec (.of k))]
    [IsSeparated (P ↘ Spec (.of k))]
    [LocallyOfFiniteType (P' ↘ Spec (.of k))] [QuasiCompact (P' ↘ Spec (.of k))]
    [IsSeparated (P' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (B ↘ Spec (.of k))] [QuasiCompact (B ↘ Spec (.of k))]
    [IsSeparated (B ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))] [IsSeparated (c.obj.obj.Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (d.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (d.obj.obj.Z ↘ Spec (.of k))] [IsSeparated (d.obj.obj.Z ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [h.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [c.obj.obj.i.IsOver (Spec (.of k))] [c.obj.obj.g.IsOver (Spec (.of k))]
    [d.obj.obj.i.IsOver (Spec (.of k))] [d.obj.obj.g.IsOver (Spec (.of k))]
    [QuasiCompact i] [IsProper p] [IsProper h]
    [IsSchemeTheoreticallyDominant c.obj.obj.i]
    [IsSchemeTheoreticallyDominant d.obj.obj.i]
    (I : (lowerStar Λ p).rightDerivedFunctor ⋙ (openImmersionLowerShriek Λ i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
        (lowerStar Λ c.obj.obj.g).rightDerivedFunctor)
    (J : (lowerStar Λ h).rightDerivedFunctor ⋙
        (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory ⋙
        (lowerStar Λ d.obj.obj.g).rightDerivedFunctor)
    (I' : (lowerStar Λ (h ≫ p)).rightDerivedFunctor ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory ⋙
        (lowerStar Λ (d.obj.obj.g ≫ c.obj.obj.g)).rightDerivedFunctor)
    (hI : ∀ A, compositionInterchangeIsNormalized Λ p i c A (I.app A))
    (hJ : ∀ A, compositionInterchangeIsNormalized Λ h c.obj.obj.i d A (J.app A))
    (hI' : ∀ A, compositionInterchangeIsNormalized Λ (h ≫ p) i
      (interchangeOuterCompactification p h i c d) A (I'.app A)) :
    ∀ A : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology P') Ab.{u + 1})
        (condensedRingObj Λ P')),
      (openImmersionLowerShriek Λ i).mapDerivedCategory.map
          ((interchangeDerivedLowerStarComp Λ h p).inv.app A) ≫ I'.app A ≫
        (interchangeDerivedLowerStarComp Λ d.obj.obj.g c.obj.obj.g).hom.app
          ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj A) =
      I.app ((lowerStar Λ h).rightDerivedFunctor.obj A) ≫
        (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (J.app A) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
