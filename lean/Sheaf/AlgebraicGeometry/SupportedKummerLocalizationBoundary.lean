/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Shift.Adjunction

import Sheaf.AlgebraicGeometry.ClosedSupportHom
import Sheaf.AlgebraicGeometry.PurityRelativeCone
import Sheaf.CategoryTheory.ModuleRestrictionKernelComparison
import Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Sheaf.CategoryTheory.Sites.RelativeTorsorExtension
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # Supported Kummer class and localization boundary

Source: ILO, Expose XVI, Lemme 3.4.8, printed p.247, and its Kummer-torsor proof
(blueprint: lem-per-supported-kummer-class-localization-boundary).

The helpers spell out the canonical morphisms in the statement. The normalized
classes are specified through the existing class maps. The closed transpose uses
the canonical right-adjoint shift comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite Pretriangulated
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

namespace SupportedKummerLocalization

universe vC vZ vU uC uZ uU wC wZ

attribute [local irreducible] ordinaryFiniteRootMap Sheaf.H.map
  Scheme.finiteEtaleTwistScalar

attribute [local irreducible] ModuleCat.extendScalars
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

/-- Exact inverse image of a single object followed by an ordinary comparison.
Source: ILO XVI 3.4.8, constant and Tate restriction identifications
(blueprint: lem-per-supported-kummer-class-localization-boundary). -/
@[irreducible]
def singlePullback {C : Type uC} {E : Type uZ}
    [Category.{vC} C] [Category.{vZ} E] [Abelian C] [Abelian E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wZ} E] (F : C ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : C) (Y : E) (e : F.obj X ≅ Y) :
    F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor E 0).obj Y :=
  (F.mapDerivedCategorySingleFunctor 0).app X ≪≫
    (DerivedCategory.singleFunctor E 0).mapIso e

-- Use the category instances captured by the recorded derived module category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The canonical constant comparison in the exact-derived encoding.
Source: ILO XVI 3.4.8 (blueprint: lem-per-supported-kummer-class-localization-boundary). -/
@[irreducible]
def constantPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (v : X ⟶ Y) :=
  singlePullback (upperStar (ModuleCat.{u + 1} A) v)
    (ordinaryFiniteConstant A Y) (ordinaryFiniteConstant A X)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app (ModuleCat.of A A))

/-- Canonical degree-one Tate restriction, using the normalized pure-root comparison.
Source: ILO XVI 3.4.8; Stacks 03PK and 03Q1
(blueprint: lem-per-supported-kummer-class-localization-boundary). -/
@[irreducible]
def lineRestriction (A : Type (u + 1)) [CommRing A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) {X Y : Scheme.{u}} (v : X ⟶ Y)
    (hY : IsUnit (n : Γ(Y, ⊤))) :=
  (shiftFunctor _ (1 : ℤ)).mapIso
    (singlePullback (upperStar (ModuleCat.{u + 1} A) v)
      (Scheme.finiteEtaleTateLine Y n A hA) (Scheme.finiteEtaleTateLine X n A hA)
      ((Scheme.finiteEtaleTwistPullbackData A n hn hA).c v hY
        (by simpa using hY.map v.appTop.hom) 1))

/-- The localization boundary through two adjunctions, with the canonical shift maps.
Source: ILO XVI 3.4.8, the closed-support localization boundary
(blueprint: lem-per-supported-kummer-class-localization-boundary). -/
@[irreducible]
def boundaryCore {C : Type uC} {Z : Type uZ} {U : Type uU}
    [Category.{vC} C] [Category.{vZ} Z] [Category.{vU} U]
    [HasShift C ℤ] [HasShift Z ℤ] [HasShift U ℤ]
    (F : Z ⥤ C) (I : C ⥤ Z) (J : C ⥤ U) (G : U ⥤ C)
    [F.CommShift ℤ] [G.CommShift ℤ]
    (adjI : I ⊣ F) (adjJ : J ⊣ G)
    (AT : C) (AZ : Z) (AU : U) (K : C) (P : Z)
    (eI : I.obj AT ≅ AZ) (eJ : J.obj AT ≅ AU)
    (a : AU ⟶ (J.obj K)⟦(1 : ℤ)⟧)
    (δ : G.obj (J.obj K) ⟶ (F.obj P)⟦(1 : ℤ)⟧) : AZ ⟶ P⟦(2 : ℤ)⟧ :=
  eI.inv ≫ (adjI.homEquiv _ _).symm
    ((adjJ.homEquiv _ _ (eJ.hom ≫ a)) ≫
      (G.commShiftIso (1 : ℤ)).hom.app _ ≫ δ⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd C (1 : ℤ) (1 : ℤ)).inv.app _ ≫
      (F.commShiftIso (2 : ℤ)).inv.app P)

/-- Canonical shift-corrected transpose under a closed-support right adjunction.
Source: ILO XVI 3.4.8, transpose of the Gysin map
(blueprint: lem-per-supported-kummer-class-localization-boundary). -/
@[irreducible]
def transposeCore {C : Type uC} {Z : Type uZ} [Category.{vC} C] [Category.{vZ} Z]
    [HasShift C ℤ] [HasShift Z ℤ] (F : Z ⥤ C) (R : C ⥤ Z)
    [F.CommShift ℤ] (adj : F ⊣ R) (AZ : Z) (K : C)
    (c : F.obj AZ ⟶ K⟦(2 : ℤ)⟧) : AZ ⟶ (R.obj K)⟦(2 : ℤ)⟧ :=
  adj.homEquiv _ _ c ≫ (Adjunction.RightAdjointCommShift.iso adj (2 : ℤ)).hom.app K

/-- The prime coefficient field, lifted to the coefficient universe of the small site.
Source: ILO XVI 3.4.8, coefficients F_l
(blueprint: lem-per-supported-kummer-class-localization-boundary). -/
abbrev Coeff (l : ℕ) := ULift.{u + 1} (ZMod l)


/-- The lifted residue coefficients are killed by l.
Source: ILO XVI 3.4.8, coefficients F_l
(blueprint: lem-per-supported-kummer-class-localization-boundary). -/
abbrev killed (l : ℕ) :=
  congrArg (ULift.up : ZMod l → Coeff.{u} l) (ZMod.natCast_self l)


/-- The class and boundary of a principal Cartier divisor agree up to an unspecified sign.
The assumption on the kernel ideal says that the canonical V(f) is an effective
Cartier divisor; since f generates that ideal, this is equivalent to injectivity
of multiplication by f on the structure sheaf. The displayed triangle has precisely
the closed counit and open unit, and its supplied third arrow is the localization map.

Source: ILO, Expose XVI, Lemme 3.4.8 and proof, printed p.247
(blueprint: lem-per-supported-kummer-class-localization-boundary).

Proof (the five DAG steps):
1. Multiplication by f identifies O_T with the Cartier ideal. Dualizing gives a
   global frame e of O_T(D), with canonical section f e. Its restriction is the
   unit f on U, so the framed torsor is G_m with that specified section.
2. Push out the open-closed integral sequence along f. The relative torsor
   extension normalized to send its specified section to zero is the pushout
   along -f (in additive notation). Negation on G_m and identity on the supported
   quotient identify its extension class with minus the pushout along f, by Ext
   naturality and the extension-by-zero adjunction.
3. SupportedKummerBoundary identifies the integral realization of the supported
   class with the splice of that extension and the exact Kummer extension.
   The signed Yoneda-localization lemma identifies the positive splice with
   the localization boundary of the ordinary Kummer class of f.
4. The supported integral DerivedUnit detects equality of module-derived arrows.
   The module/abelian restriction-kernel comparison commutes with the relative
   differential (da,res(a)-db) and boundary (0,-b). Thus the integral comparison
   gives the supported module equality, with one overall sign.
5. The supported-Hom comparison identifies the third arrow of the counit/unit
   triangle with this localization boundary. The two closed adjunctions and
   their triangle identities identify its transpose with the displayed boundary.
   Transpose the supported equality and absorb the cone convention into the sign.
   None of these steps requires Noetherianity, regularity or excellence. -/
theorem supported_kummer_localization_boundary
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (hl : IsUnit (l : Γ(T, ⊤))) (f : Γ(T, ⊤))
    (hf : (T.zeroLocusSubschemeι {f}).ker.IsInvertible)
    (c : Ext
      ((lowerStar (ModuleCat.{u + 1} (Coeff.{u} l)) (T.zeroLocusSubschemeι {f})).obj
        (ordinaryFiniteConstant (Coeff.{u} l) (T.zeroLocusSubscheme {f})))
      (Scheme.finiteEtaleTateLine T l (Coeff.{u} l) (killed l)) 2)
    (hc : SupportedKummerBoundary (Coeff.{u} l) l (killed l)
      (T.zeroLocusSubschemeι {f}) hf hl c)
    (κ : ordinaryFiniteUnit (Coeff.{u} l) (T.basicOpen f).toScheme ⟶
      (D(upperStar (ModuleCat.{u + 1} (Coeff.{u} l)) (T.basicOpen f).ι).obj
        (ordinaryFiniteLine (Coeff.{u} l) l (killed l) T))⟦(1 : ℤ)⟧)
    (hκ : ordinaryFiniteClass (Coeff.{u} l) (T.basicOpen f).toScheme
      (Scheme.finiteEtaleTateLine (T.basicOpen f).toScheme l (Coeff.{u} l) (killed l)) 1
      (κ ≫ (lineRestriction (Coeff.{u} l) l (Fact.out : l.Prime).pos (killed l)
        (T.basicOpen f).ι hl).hom) =
      Sheaf.H.map (ordinaryFiniteRootMap (Coeff.{u} l) l (killed l)
        (T.basicOpen f).toScheme) 1
        ((T.basicOpen f).toScheme.kummerδ₀ l
          (by simpa using hl.map (T.basicOpen f).ι.appTop.hom)
          (Additive.ofMul (T.basicOpenUnit f))))
    (δ : R(lowerStar (ModuleCat.{u + 1} (Coeff.{u} l)) (T.basicOpen f).ι).obj
        (D(upperStar (ModuleCat.{u + 1} (Coeff.{u} l)) (T.basicOpen f).ι).obj
          (ordinaryFiniteLine (Coeff.{u} l) l (killed l) T)) ⟶
      (R(lowerStar (ModuleCat.{u + 1} (Coeff.{u} l)) (T.zeroLocusSubschemeι {f}))).obj
        ((R(lowerStar (ModuleCat.{u + 1} (Coeff.{u} l))
          (T.zeroLocusSubschemeι {f}))).rightAdjoint.obj
            (ordinaryFiniteLine (Coeff.{u} l) l (killed l) T))⟦(1 : ℤ)⟧)
    (hδ : Triangle.mk
      ((Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} (Coeff.{u} l))
        (T.zeroLocusSubschemeι {f})))).counit.app
          (ordinaryFiniteLine (Coeff.{u} l) l (killed l) T))
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (Coeff.{u} l))
        (T.basicOpen f).ι).unit.app (ordinaryFiniteLine (Coeff.{u} l) l (killed l) T)) δ
      ∈ distTriang _) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      transposeCore _ _
        (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} (Coeff.{u} l))
          (T.zeroLocusSubschemeι {f}))))
        (ordinaryFiniteUnit (Coeff.{u} l) (T.zeroLocusSubscheme {f}))
        (ordinaryFiniteLine (Coeff.{u} l) l (killed l) T)
        (supportedExactDerivedMap
          (lowerStar (ModuleCat.{u + 1} (Coeff.{u} l)) (T.zeroLocusSubschemeι {f}))
          (ordinaryFiniteConstant (Coeff.{u} l) (T.zeroLocusSubscheme {f}))
          (Scheme.finiteEtaleTateLine T l (Coeff.{u} l) (killed l)) c) =
      ε • boundaryCore _ _ _ _
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (Coeff.{u} l))
          (T.zeroLocusSubschemeι {f}))
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (Coeff.{u} l))
          (T.basicOpen f).ι)
        (ordinaryFiniteUnit (Coeff.{u} l) T)
        (ordinaryFiniteUnit (Coeff.{u} l) (T.zeroLocusSubscheme {f}))
        (ordinaryFiniteUnit (Coeff.{u} l) (T.basicOpen f).toScheme)
        (ordinaryFiniteLine (Coeff.{u} l) l (killed l) T)
        _ (constantPullback (Coeff.{u} l) (T.zeroLocusSubschemeι {f}))
        (constantPullback (Coeff.{u} l) (T.basicOpen f).ι) κ δ := by
  sorry

end SupportedKummerLocalization
end AlgebraicGeometry.Etale
