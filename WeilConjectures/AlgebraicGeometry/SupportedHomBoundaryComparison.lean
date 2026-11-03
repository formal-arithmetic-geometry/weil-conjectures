/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import Mathlib.CategoryTheory.Preadditive.Comma
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import WeilConjectures.CategoryTheory.Abelian.ExtResolutionDerivedConnecting
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.AlgebraicGeometry.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import Mathlib.Algebra.Homology.ModelCategory.Injective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.CategoryTheory.ProperBaseChange.ModuleAbelianEvaluationComparison
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.AlgebraicGeometry.Closed.ClosedSupportHomSequence

/-!
# Evaluation-normalized supported Hom and coefficient boundaries

Source: Stacks Project, derived.tex, Tag 05TE, lemma-right-derived-delta-functor;
blueprint lem-pur-divisor-class, proof (b), The relative class, and
lem-amb-cartier-kummer-map, the connecting-map and supported-Hom paragraphs.
(blueprint: lem-pur-supported-hom-boundary-comparison).

Module-valued section complexes are viewed as abelian complexes after taking sections.
Equivalently, evaluate the termwise underlying abelian sheaf complex. This uses the
same section groups and restriction maps, without claiming that forgotten injectives
are injective. Integral comparison uses the already normalized abelian comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

attribute [local instance] hasExt_of_enoughInjectives

/-- Termwise exact coefficient forgetting on a resolution or any nonnegative complex.
Source: Stacks Tag 03FD (blueprint: lem-pur-supported-hom-boundary-comparison). -/
abbrev supportedHomUnderlyingComplex (B : Type (u + 1)) [CommRing B] (T : Scheme.{u})
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) :=
  ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I

/-- The relative module-section complex, with its underlying abelian groups exposed.
It is the dependency's actual shifted cone, in signed coordinates (a,b) with
D(a,b)=(da,res(a)-db). The unsigned open coordinate of the shifted cone is -b.
Source: Stacks Tags 03AJ and 03FD
(blueprint: lem-pur-supported-hom-boundary-comparison). -/
abbrev supportedHomRelativeComplex (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) :=
  relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
    (supportedHomUnderlyingComplex B T I)

/-- The underlying abelian short complex of a coefficient-resolution sequence.
Source: Stacks Tags 013T and 03FD
(blueprint: lem-pur-supported-hom-boundary-comparison). -/
abbrev supportedHomUnderlyingSequence (B : Type (u + 1)) [CommRing B] (T : Scheme.{u})
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)) :=
  S.map ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ))

/-- The specified comparisons, including normalization and both compatibility equations.
All resolution lifts are universally quantified computational models. In particular no
frame, low-degree vanishing, or choice of a connecting map is part of the hypotheses.
The generator in `integral` is the existing supported constant map sending 1 to 1_B.
Source: Stacks Tags 05TE, 06XR and 03FD; blueprint lem-pur-divisor-class, proof (b).
(blueprint: lem-pur-supported-hom-boundary-comparison). -/
structure SupportedHomBoundaryComparisons (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] where
  comparison : ∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (I : InjectiveResolution F) (q : ℕ),
    Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))) F q ≃+
      (supportedHomRelativeComplex B i I.cocomplex).homology (q : ℤ)
  onCocycle : ∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (I : InjectiveResolution F) (q : ℕ)
    (k : ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))) ⟶
      I.cocomplex.X q)
    (hk : k ≫ I.cocomplex.d q (q + 1) = 0),
    ∃ z : (supportedHomRelativeComplex B i I.cocomplex).cycles (q : ℤ),
      (relativeForgetComplex T (Scheme.Etale.mk i.openComplement.ι)
        (supportedHomUnderlyingComplex B T I.cocomplex)).f q
        ((supportedHomRelativeComplex B i I.cocomplex).iCycles q z) =
      (extendXIso
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
          (supportedHomUnderlyingComplex B T I.cocomplex))
        ComplexShape.embeddingUpNat (rfl : (q : ℤ) = q)).inv
          (((supportedConstantUnit B i) ≫ k).hom.app
            (op (Scheme.Etale.mk (𝟙 T)))
            ((toSheafify (D := ModuleCat.{u + 1} B) T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app
              (op (Scheme.Etale.mk (𝟙 T))) (1 : B))) ∧
      (((CochainComplex.mappingCone (relativeSectionRestriction T
          (Scheme.Etale.mk i.openComplement.ι)
          (supportedHomUnderlyingComplex B T I.cocomplex))).shiftFunctorObjXIso
          (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
        homotopyCofiber.sndX (relativeSectionRestriction T
          (Scheme.Etale.mk i.openComplement.ι)
          (supportedHomUnderlyingComplex B T I.cocomplex)) ((q : ℤ) + -1))
        ((supportedHomRelativeComplex B i I.cocomplex).iCycles q z) = 0 ∧
      comparison F I q (InjectiveResolution.extMk.{u + 1, u + 1, u + 2} I k (q + 1) rfl hk) =
        (supportedHomRelativeComplex B i I.cocomplex).homologyπ q z
  connecting : ∀ (S : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₂ : InjectiveResolution S.X₂) (I₃ : InjectiveResolution S.X₃)
    (a : I₁.cocomplex ⟶ I₂.cocomplex) (b : I₂.cocomplex ⟶ I₃.cocomplex)
    (hab : a ≫ b = 0)
    (_ha : I₁.ι ≫ a = (CochainComplex.single₀ _).map S.f ≫ I₂.ι)
    (_hb : I₂.ι ≫ b = (CochainComplex.single₀ _).map S.g ≫ I₃.ι)
    (hs : ∀ n : ℕ, Nonempty
      (((supportedHomUnderlyingSequence B T (ShortComplex.mk a b hab)).map
        (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (q : ℕ) (x : Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))) S.X₃ q),
    comparison S.X₁ I₁ (q + 1)
      (Ext.comp.{u + 1} x (ShortComplex.ShortExact.extClass.{u + 1} hS) rfl) =
      relativeConnecting T (Scheme.Etale.mk i.openComplement.ι)
        (supportedHomUnderlyingSequence B T (ShortComplex.mk a b hab)) hs (q : ℤ)
        (comparison S.X₃ I₃ q x)
  integral : ∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((moduleAbelianForget B T).obj F))
    (t : supportedHomUnderlyingComplex B T I.cocomplex ⟶ J.cocomplex)
    (_ht : (moduleAbelianForget B T).map (I.ι.f 0) ≫ t.f 0 = J.ι.f 0) (q : ℕ),
    IsIso (homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) t)
      (q : ℤ)) ∧
    ∀ y : Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))) F q,
      relativeExtensionComparison i ((moduleAbelianForget B T).obj F) J q
        ((Ext.mk₀.{u + 1} (supportedIntegralGenerator B i)).comp
          (Ext.mapExactFunctor.{u + 1, u + 1} (moduleAbelianForget B T) y) (zero_add q)) =
      homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) t) (q : ℤ)
        (comparison F I q y)

/-- Evaluation-normalized supported Hom preserves the positive Yoneda coefficient
boundary in every nonnegative degree and commutes with integral evaluation by an
isomorphism of abelian groups. This includes B=Z and q=1, with the displayed plus sign.
Source: Stacks derived.tex, Tag 05TE, lemma-right-derived-delta-functor; the
kernel/cone refinement follows blueprint lem-pur-divisor-class, proof (b), The relative
class, and lem-amb-cartier-kummer-map, the connecting-map and supported-Hom paragraphs.
(blueprint: lem-pur-supported-hom-boundary-comparison).

Proof:
1. The open--closed sequence for B_T identifies Hom(i_*B_Z,F) with the kernel of
restriction F(T) -> F(W), by precomposition with constant restriction and evaluation
at 1_B. Constant-sheaf and extension-by-zero adjunctions identify the two arrows.
2. Apply this identification to an injective resolution. Restriction on injectives
is surjective. The kernel-to-shifted-cone quasi-isomorphism, in coordinates (a,b), has
differential (da,res(a)-db) and sends a kernel element to (a,0). Computing Ext by this
resolution gives the additive equivalences with precisely the onCocycle formula.
3. Choose horseshoe resolutions for a coefficient SES. Hom, both section functors,
and the kernels preserve its degreewise splittings. Evaluation and kernel inclusion
therefore form a morphism from its Hom short complex to its relative short complex.
4. Naturality of homology connecting maps and the Ext/derived connecting comparison
identify the two boundaries. Explicitly lift a cocycle f to g with dg=i h. The Hom
boundary is h; its evaluated cone lift has differential (i h evaluated at 1_B,0).
Thus the relative boundary is the image of h with a plus sign, in every degree.
5. Forget a module resolution and lift it to any abelian injective resolution J.
Forgotten module injectives are section-acyclic at every etale object. Leray identifies
the resulting maps on T and W with the canonical ordinary cohomology comparisons.
Their restriction square commutes, inducing the displayed relativeSectionMap.
6. The identity gamma_B p_Z = U(p_B) eta_B holds on constant generators and hence on
sheafification. Evaluating the forgotten resolution cocycle at one consequently gives
the same section as applying t to its B-evaluation; the open coordinate stays zero.
This is exactly the integral equation for the existing normalized abelian comparison.
7. The relative-cone long exact sequence and the ordinary comparison isomorphisms
on T and W give invertibility by the five lemma. Negative groups vanish at q=0.
The support/kernel comparison of relativeConeSupportComparison transports both
identities to supported cohomology. All constructions include empty support, empty
complement, the zero coefficient ring, and split coefficient extensions. -/
theorem supportedHomBoundaryComparison (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    Nonempty (SupportedHomBoundaryComparisons B i) := by
  sorry

end AlgebraicGeometry.Etale
