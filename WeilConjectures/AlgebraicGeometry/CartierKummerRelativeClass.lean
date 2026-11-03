/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
public import WeilConjectures.AlgebraicGeometry.CartierComplementFrame
public import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.CartierPoleBoundary
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.SupportedCartierBoundaryExistence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerDescent
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.RelativeExtensionBoundaryComparison

/-! # The Cartier Kummer arrow and its relative line class

Source: current blueprint, lem-amb-cartier-kummer-map.proof.md, relative cone,
Kummer boundary, supported-Hom identification and scalar-extension paragraphs;
lem-pur-divisor-class.proof.md, (b), The relative class.
(blueprint: lem-pur-cartier-kummer-relative-class)

The equality is written in relative cohomology of underlying abelian sheaves,
using the integral supported-Hom comparison and evaluation at supported one.
These are canonical isomorphisms, so the formula retains the full supported
class. The last equation realizes its module arrow as the specified pro-etale map.
Positive coefficient and Kummer levels are indexed by their predecessors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

/-- The actual frame torsor of the dual Cartier ideal, with the canonical section
on the open complement. The section is constructed from the dual ideal inclusion;
no frame or extension class is selected from an existence theorem.
Source: current blueprint, lem-amb-cartier-kummer-map.proof.md, first two paragraphs
(blueprint: lem-pur-cartier-kummer-relative-class). -/
def cartierRelativeFrame {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :
    Sheaf.Torsor.WithSection T.gmSheaf (Scheme.Etale.mk i.openComplement.ι) :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  ⟨Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules),
    Scheme.Modules.etaleIsoTorsorMk (Scheme.Modules.dual i.ker.toModules)
      (supportedDivisorSectionPullback i i.openComplement)
      (cartierDivisorSectionPullback_isIso i i.openComplement i.coe_openComplement)⟩

/-- The supported Cartier arrow is the relative Kummer boundary of its framed line.
The resolution parameters are arbitrary computational models: `a,b` augment the
actual Kummer sequence, their rows split, and `f` lifts the actual root insertion.
The displayed equality uses the canonical integral evaluation of the module class.
The module/abelian relative comparison is an isomorphism; the kernel-to-cone
comparison then gives exactly the equality in supported module cohomology.

Source: current blueprint, lem-amb-cartier-kummer-map.proof.md, relative cone,
connecting-map paragraph, supported-Hom display and final scalar extension;
lem-pur-divisor-class.proof.md, (b), The relative class.
(blueprint: lem-pur-cartier-kummer-relative-class).

Proof, following the eight DAG steps:
1. Local equations f_a give frames f_a^{-1} of the dual ideal; the canonical section
has coordinate f_a. Their transition units f_a/f_b and the complementary section
form the specified relative torsor, unchanged by changing equations or covers.
2. The unique Cartier pole extension is the extension of this framed torsor.
Relative extension/cohomology normalization identifies its integral supported-Hom
class with minus the raw relativeTorsorEquiv, the Ext-normalized relative class.
3. Apply supported-Hom boundary comparison to the actual Kummer sequence, with
integral coefficients and q=1. Its Yoneda composite is the positive relative
connecting map in the signed cone. The kernel-to-cone comparison gives delta_D,r.
4. At R=Z/l^(r+1), uniqueness of the normalized Cartier boundary and integral
evaluation identify its supported class with this relative Kummer boundary.
5. Derived scalar extension R to A carries source one to one and roots u to
u tensor 1. Integral evaluation and naturality identify its supported class with
H_D^2(phi_r)(delta_D,r(rho_D)); forgetting modules is an isomorphism on relative
cohomology. No flatness of A over R is used.
6. The coefficient quotient is finite. The normalized scalar-boundary theorem
identifies this ordinary arrow with the normalized A-boundary. Cartier descent
transports it by comparison inverse image, the source quotient comparison and the
root-normalized finite Tate comparison to the specified pro-etale twist.
7. Uniqueness of normalized ordinary boundaries and descent identifies this pair
with the pair defining cartierKummerMap. This identifies the supported arrow itself.
8. The argument applies to every annihilating exponent. All realizations equal the
same cartierKummerMap; root-power transition comparisons ensure compatibility.
There is no condition on divisibility of the coefficient level by ramification.
-/
theorem cartier_kummer_relative_class
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤)))
    (I : InjectiveResolution (T.rootsOfUnitySheaf (l ^ (r + 1))))
    (J K : InjectiveResolution T.gmSheaf)
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ K.cocomplex)
    (hab : a ≫ b = 0)
    (_ha : I.ι ≫ a = (CochainComplex.single₀ _).map
      (T.kummerSequence (l ^ (r + 1))).f ≫ J.ι)
    (_hb : J.ι ≫ b = (CochainComplex.single₀ _).map
      (T.kummerSequence (l ^ (r + 1))).g ≫ K.ι)
    (hs : ∀ k : ℕ, Nonempty (((ShortComplex.mk a b hab).map
      (HomologicalComplex.eval _ (.up ℕ) k)).Splitting))
    (M : InjectiveResolution ((RawModuleScalarComparison.forget
      (finiteTateCoefficient l E n) T).obj
        (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA)))
    (f : I.Hom M (ordinaryFiniteRootMap (finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA T)) :
    ∃ (κ : Ext ((lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
        (ordinaryFiniteConstant (finiteTateCoefficient l E n) D))
          (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA) 2)
      (α : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          ((lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
            (ordinaryFiniteConstant (finiteTateCoefficient l E n) D)) ≅
              cartierSupported l E n i)
      (q : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA) ≅
            finiteTateProSheaf l E n T 1),
      relativeExtensionComparison i _ M 2
        ((Ext.mk₀ (supportedIntegralGenerator (finiteTateCoefficient l E n) i)).comp
          (κ.mapExactFunctor (RawModuleScalarComparison.forget
            (finiteTateCoefficient l E n) T)) (zero_add 2)) =
        HomologicalComplex.homologyMap
          (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) f.hom) 2
          (relativeConnecting T (Scheme.Etale.mk i.openComplement.ι)
            (ShortComplex.mk a b hab) hs 1
            (-relativeTorsorEquiv T (Scheme.Etale.mk i.openComplement.ι) K
              (Quotient.mk _ (cartierRelativeFrame i hI)))) ∧
      IsFiniteTateSiteComparison l E n T r hA 1 q ∧
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).map
          (supportedConstantUnit (finiteTateCoefficient l E n) i) ≫ α.hom =
        cartierConstantComparison (finiteTateCoefficient l E n) T ≫
          cartierSupportedUnit l E n i ∧
      (DerivedCategory.singleFunctor _ 0).map α.hom ≫ cartierKummerMap l E n i hI hT =
        (((κ.mapExactFunctor (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)).comp
            (Ext.mk₀ q.hom) (add_zero 2)).hom)  := by
  classical
  unfold cartierKummerMap
  have hdata := (cartier_kummer_map l E).2.exists.choose_spec
  generalize (cartier_kummer_map l E).2.exists.choose = data at *
  obtain ⟨κ, c⟩ := data
  dsimp only [CartierEtaleKummerFamily] at κ
  dsimp only [CartierKummerFamily] at c
  have hκ := hdata.1
  unfold CartierEtaleKummerNormalization at hκ
  have hc := hdata.2.2.1
  unfold CartierKummerRealization at hc
  obtain ⟨α, q, hq, hα, he⟩ := hc n r hA i hI hT
  refine ⟨κ n r hA i hI hT, α, q, ?_, hq, hα, ?_⟩
  · let := hI.isInvertible_dual_toModules
    let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
      (Scheme.Modules.dual i.ker.toModules)
    have hbound := hκ n r hA i hI hT
    unfold SupportedKummerBoundary at hbound
    obtain ⟨τ, B, u, v, huv, hB, t, hτ, ht, hv, htzero, hext⟩ :=
      hbound i.openComplement i.coe_openComplement
    have hτframe : τ = (cartierRelativeFrame i hI).2 := by
      apply Scheme.Modules.etaleIsoTorsorVal_injective (Scheme.Modules.dual i.ker.toModules)
      simpa only [cartierRelativeFrame, Scheme.Modules.etaleIsoTorsorVal_mk] using hτ
    have hrep : RelativeExtensionRepresents i (cartierRelativeFrame i hI) hB.extClass := by
      refine ⟨B, u, v, huv, hB, t.hom, ?_, ?_, ?_, rfl⟩
      · intro V g x
        exact (ht V g x).trans (add_comm _ _)
      · intro V x
        have h := integerSectionEquiv_restrict T
          ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
          (supportedIntegralUnit i) V
        rw [integerSectionEquiv_eval] at h
        exact (hv V x).trans h.symm
      · rw [← hτframe]
        exact htzero
    have hβ : hB.extClass = relativeExtension i (cartierRelativeFrame i hI) :=
      (Classical.choose_spec (relativeExtension_existsUnique i (cartierRelativeFrame i hI))).2
        _ hrep
    rw [hext, hβ]
    rw [relativeExtensionBoundaryComparison i
      (T.kummerSequence_shortExact (l ^ (r + 1))
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1))) I J K a b hab _ha _hb hs
      (ordinaryFiniteRootMap (finiteTateCoefficient l E n) (l ^ (r + 1)) hA T)
      M f 1 (relativeExtension i (cartierRelativeFrame i hI)),
      relative_extension_cohomology_normalization]
    rfl
  · change (DerivedCategory.singleFunctor _ 0).map α.hom ≫
      (c n i hI hT).hom = _
    simpa only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp] using
      congrArg Ext.hom he

end AlgebraicGeometry.Etale
