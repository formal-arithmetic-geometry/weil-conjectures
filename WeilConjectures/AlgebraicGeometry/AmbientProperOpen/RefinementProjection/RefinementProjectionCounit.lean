/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionWords
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionLocalTensor
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionProperComposition

/-! # Proper refinement intertwines the counit projection maps

Source: blueprint sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, composition/refinement sentence, expanded in the DAG;
Stacks Project, Tags 0B56 and 0DV0
(blueprint: lem-sf-refinement-projection-counit).

The comparison is directed from the second compactification to the first. Its proper/open
factor is never inverted. Both coefficient settings retain all unbounded inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2000
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection

/-- The native projection natural transformation, specialized with the generic coefficient
category before the coefficient ring is instantiated. This is definitionally the original
projection map; packaging it shares the categorical instance data at finite coefficients.
Source: `projectionMapOfCompactification`
(blueprint: lem-sf-refinement-projection-counit). -/
noncomputable def finiteProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  projectionMapOfCompactification (ModuleCat.{u + 1} A) c

/-- The specified finite-level refinement comparison: insert the canonical identity direct
image, apply the intrinsic proper/open mate, then the conjugate direct-image compositor.
Source: blueprint composition/refinement sentence; Stacks 0F7B, 07A7
(blueprint: lem-sf-refinement-projection-counit). -/
def finiteComparison (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c₁ c₂ : Compactification f.hom.left} (r : c₁.Refinement c₂)
    (K : ProperOpenDerived A X.obj.left) :
    (ProperOpenPush A c₂.g).obj ((ProperOpenShriek A c₂.i).obj K) ⟶
      (ProperOpenPush A c₁.g).obj ((ProperOpenShriek A c₁.i).obj K) := by
  letI := c₁.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  letI := c₂.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  exact (ProperOpenPush A c₂.g).map
    ((ProperOpenShriek A c₂.i).map (((ordinary F A).sId X).inv.app K) ≫
      (properOpenMate A c₁.i (𝟙 X.obj.left) r.hom c₂.i
        (r.i_hom.trans (Category.id_comp _).symm)).app K) ≫
    (conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c₂.g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r.hom ≫ c₂.g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom c₂.g)).hom.app
        ((ProperOpenShriek A c₁.i).obj K) ≫
    (indexIso (ProperOpenPush A) r.hom_g).hom.app
      ((ProperOpenShriek A c₁.i).obj K)

end AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection

namespace WeilConjectures.IntegralSystemRealization.RefinementProjection

/-- The specified simultaneous-system comparison. The identity direct image is normalized
through the sectionwise canonical bridge. Gamma and the compositor are the recorded intrinsic
system maps, before evaluation or total limit.
Source: blueprint composition/refinement sentence; Stacks 0F7B, 07A7
(blueprint: lem-sf-refinement-projection-counit). -/
def systemComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : FiniteFieldDatum.{u}) (o : Operations l E) (z : Realizations l E F o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (K : System l E X) :
    (Operations.push l E o c₂.g).obj ((Operations.shriek l E o c₂.i).obj K) ⟶
      (Operations.push l E o c₁.g).obj ((Operations.shriek l E o c₁.i).obj K) := by
  letI := c₁.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  letI := c₂.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  exact (Operations.push l E o c₂.g).map
    ((Operations.shriek l E o c₂.i).map
      ((z.canonicalBridge.push l E (𝟙 X) ≪≫
        ProEtale.SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X).inv.app K) ≫
      (z.properOpen.gamma c₁.i (𝟙 X) r.hom c₂.i
        (r.i_hom.trans (Category.id_comp _).symm)).app K) ≫
    (z.compositors.pushComp l E r.hom c₂.g).hom.app
      ((Operations.shriek l E o c₁.i).obj K) ≫
    (eqToIso (congrArg (Operations.push l E o) r.hom_g)).hom.app
      ((Operations.shriek l E o c₁.i).obj K)

end WeilConjectures.IntegralSystemRealization.RefinementProjection

section FiniteProof

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.mapDerivedCategory
  leftDerivedUpperStarComp leftDerivedUpperStarTensorNatIso
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarTensorComparison derivedTensor
  properOpenMate properOpenTensorIso Calculus.sId
  HasDerivedCategory.ofHasKInjectiveResolutions
  DerivedCategory

attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

private theorem finite_intertwines
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (r : c₁.Refinement c₂)
    (hlocal : RefinementProjection.Words.Local (RefinementProjection.finiteWords F A r))
    (hcomp : RefinementProjection.Words.Composition (RefinementProjection.finiteWords F A r)) :
   (∀ (K : ProperOpenDerived
          A X.obj.left)
       (L : ProperOpenDerived
          A Y.obj.left),
      ((RefinementProjection.finiteProjection A
          c₂).app K).app L ≫
        RefinementProjection.finiteComparison F
          A r
          (((ProperOpenTensor
            A X.obj.left).obj K).obj
            ((ProperOpenPull
              A f.hom.left).obj L)) =
      ((ProperOpenTensor
          A Y.obj.left).map
        (RefinementProjection.finiteComparison F
          A r K)).app L ≫
        ((RefinementProjection.finiteProjection A
          c₁).app K).app L) :=
  by
    intro K L
    let w := RefinementProjection.finiteWords F
      A r
    have hn : ∀ {M N} (v : M ⟶ N) L,
        w.first (w.R.map v) L ≫ w.outer N L =
          w.outer M L ≫ w.R.map (w.TC.map (Prod.mkHom v (𝟙 (w.P'.obj L)))) := by
      intro M N v L
      exact RefinementProjection.curriedNaturality
        (ProperOpenPush
          A c₂.g)
        (ProperOpenPull
          A c₂.g)
        (ProperOpenTensor
          A c₂.Z)
        (ProperOpenTensor
          A Y.obj.left)
        (rightDerivedLowerStarProjectionMap
          (ModuleCat.{u + 1} A) c₂.g) v L
    have h := RefinementProjection.Words.pasteNative w hn hlocal hcomp K L
    dsimp only [w, RefinementProjection.finiteWords,
      RefinementProjection.identityNormalize, NatTrans.comp_app, Functor.uncurry_obj_obj] at h
    simp only [RefinementProjection.finiteProjection,
      RefinementProjection.finiteComparison,
      derivedTensorRightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
      ProperOpenTensor, ProperOpenPush, ProperOpenShriek, ProperOpenPull, ProperOpenDerived,
      Functor.comp_obj] at h ⊢
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    exact h

end AlgebraicGeometry.ProEtale.AmbientProperOpen
end FiniteProof

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

private theorem system_intertwines
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (r : c₁.Refinement c₂) :
    (∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
       (z : WeilConjectures.IntegralSystemRealization.Realizations l E F o)
       (K : WeilConjectures.IntegralSystemRealization.System l E X.obj.left)
       (L : WeilConjectures.IntegralSystemRealization.System l E Y.obj.left),
      WeilConjectures.IntegralSystemRealization.compactificationProjection
          l E o z.compositors z.openComparisons c₂ K L ≫
        WeilConjectures.IntegralSystemRealization.RefinementProjection.systemComparison
          l E F o z r
          ((WeilConjectures.IntegralSystemRealization.calculus
              l E X.obj.left).systemClosed.tensor.obj
            (K, (WeilConjectures.IntegralSystemRealization.pull l E f.hom.left).obj L)) =
      (WeilConjectures.IntegralSystemRealization.calculus l E Y.obj.left).systemClosed.tensor.map
        (Prod.mkHom
          (WeilConjectures.IntegralSystemRealization.RefinementProjection.systemComparison
            l E F o z r K) (𝟙 L)) ≫
        WeilConjectures.IntegralSystemRealization.compactificationProjection
          l E o z.compositors z.openComparisons c₁ K L) := by
  let hlocal := RefinementProjection.refinementProjectionLocalTensor F l _hl E n
          (X := X) (Y := Y) (f := f) c₁ c₂ r
  let hcomp := RefinementProjection.refinementProjectionProperComposition F l _hl E n
          (X := X) (Y := Y) (f := f) c₁ c₂ r
  intro o z K L
  let w := WeilConjectures.IntegralSystemRealization.RefinementProjection.systemWords
    l E F o z r
  have hn : ∀ {M N} (v : M ⟶ N) L,
      w.first (w.R.map v) L ≫ w.outer N L =
        w.outer M L ≫ w.R.map (w.TC.map (Prod.mkHom v (𝟙 (w.P'.obj L)))) := by
    intro M N v L
    exact RefinementProjection.tensorNaturality
      (WeilConjectures.IntegralSystemRealization.Operations.push l E o c₂.g)
      (WeilConjectures.IntegralSystemRealization.pull l E c₂.g)
      (WeilConjectures.IntegralSystemRealization.calculus l E c₂.Z).systemClosed.tensor
      (WeilConjectures.IntegralSystemRealization.calculus l E Y.obj.left).systemClosed.tensor
      (WeilConjectures.IntegralSystemRealization.properProjection l E o c₂.g) v L
  have h := RefinementProjection.Words.paste w hn (hlocal.2 o z) (hcomp.2 o z) K L
  dsimp only [w,
    WeilConjectures.IntegralSystemRealization.RefinementProjection.systemWords,
    RefinementProjection.identityNormalize, NatTrans.comp_app, Functor.uncurry_obj_obj] at h
  simpa only [WeilConjectures.IntegralSystemRealization.RefinementProjection.systemComparison,
    WeilConjectures.IntegralSystemRealization.compactificationProjection,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Category.assoc] using h

section FinalProof
/-- Every proper refinement intertwines the specified projection maps, jointly naturally
in arbitrary unbounded K and L, at every positive finite level and on semilinear systems.
Source: blueprint fix-prop-projection-formula.proof.md, composition/refinement sentence;
Stacks 0B56 (equation-projection-formula-map), 0DV0 (lemma-compose-counits)
(blueprint: lem-sf-refinement-projection-counit).

Proof:
1. Use lem-coef-semilinear-derived-sections to work in the actual ringed diagram topos in
   the system case. lem-sf-ambient-proper-open-pasting fixes the conjugate compositors and
   Gamma. Put gamma = Gamma_(j1,j2,id,u), M = J_j1 K, N = P_p2 L, T = K tensor P_f L.
2. Apply lem-sf-proper-open-tensor-compatibility to that square. The identity-edge projection
   is identity by lem-sfb-ringed-projection-tensor-composition. With the open tensor maps
   of lem-sf-open-tensor-normalization this gives gamma_T delta_j2 =
   S_u(delta_j1) pi_u (gamma_K tensor identity_N). Insert the identity and pullback compositors.
3. Expand C_u(T) PF_c2 and apply S_p2 to step 2. First-variable naturality of the counit
   projection (lem-sfb-ringed-projection-tensor-composition) moves gamma_K through pi_p2.
   The word becomes c S_p2 S_u(delta_j1) S_p2(pi_u) pi_p2
   (S_p2(gamma_K) tensor identity_L).
4. Naturality moves c past delta_j1. The projection-composition identity of
   lem-sfb-ringed-projection-tensor-composition replaces c S_p2(pi_u) pi_p2 by
   pi_p1 (c_M tensor identity_L). The result is PF_c1 (C_u(K) tensor identity_L).
   All factors are natural transformations, so this is jointly natural. Repeat the same
   calculation inside the simultaneous system category itself, retaining every transition.
   No inverse of C_u, Tor bound, constructibility, or normalized-system property is used.
-/
theorem refinementProjectionCounit
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (r : c₁.Refinement c₂) :
    (∀ (K : ProperOpenDerived
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) X.obj.left)
       (L : ProperOpenDerived
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) Y.obj.left),
      ((RefinementProjection.finiteProjection
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
          c₂).app K).app L ≫
        RefinementProjection.finiteComparison F
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) r
          (((ProperOpenTensor
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) X.obj.left).obj K).obj
            ((ProperOpenPull
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) f.hom.left).obj L)) =
      ((ProperOpenTensor
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) Y.obj.left).map
        (RefinementProjection.finiteComparison F
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) r K)).app L ≫
        ((RefinementProjection.finiteProjection
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
          c₁).app K).app L) ∧
    (∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
       (z : WeilConjectures.IntegralSystemRealization.Realizations l E F o)
       (K : WeilConjectures.IntegralSystemRealization.System l E X.obj.left)
       (L : WeilConjectures.IntegralSystemRealization.System l E Y.obj.left),
      WeilConjectures.IntegralSystemRealization.compactificationProjection
          l E o z.compositors z.openComparisons c₂ K L ≫
        WeilConjectures.IntegralSystemRealization.RefinementProjection.systemComparison
          l E F o z r
          ((WeilConjectures.IntegralSystemRealization.calculus
              l E X.obj.left).systemClosed.tensor.obj
            (K, (WeilConjectures.IntegralSystemRealization.pull l E f.hom.left).obj L)) =
      (WeilConjectures.IntegralSystemRealization.calculus l E Y.obj.left).systemClosed.tensor.map
        (Prod.mkHom
          (WeilConjectures.IntegralSystemRealization.RefinementProjection.systemComparison
            l E F o z r K) (𝟙 L)) ≫
        WeilConjectures.IntegralSystemRealization.compactificationProjection
          l E o z.compositors z.openComparisons c₁ K L) :=
  by
    constructor
    · intro K L
      have hd := (RefinementProjection.refinementProjectionLocalTensor F l _hl E n
        (X := X) (Y := Y) (f := f) c₁ c₂ r).1
      have hp := (RefinementProjection.refinementProjectionProperComposition F l _hl E n
        (X := X) (Y := Y) (f := f) c₁ c₂ r).1
      have hh := finite_intertwines F
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
        (X := X) (Y := Y) (f := f) c₁ c₂ r hd hp K L
      exact hh
    · exact system_intertwines F l _hl E n (X := X) (Y := Y) (f := f) c₁ c₂ r

end FinalProof

end AlgebraicGeometry.ProEtale.AmbientProperOpen
