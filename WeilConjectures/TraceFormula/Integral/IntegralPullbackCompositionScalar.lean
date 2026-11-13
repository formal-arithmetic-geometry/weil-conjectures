/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackCompositionScalarBase
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence

/-! # Scalar extension carries the integral pullback compositor

Source: Stacks Project, Tags 06YY, 07A4, 0941 and 0D6D; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-composition-scalar).

For a coefficient inclusion E to L, completed scalar extension carries the specified
integral composition comparison at E to the one at L, conjugated by the canonical
scalar/pullback comparisons. Both sides are compared after the fully faithful coherent
reduction at L: the system-level composition clause of integralPullbackComposition at
E and at L, the system scalar comparison, the pullback/scalar square of
scalarExtensionTowerCoherence, and whole-system mixed coherence.
The rationalized statement follows by localization on pure tensors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section SystemScalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategoryFactors integralComparisonSequenceScalarModel
attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar

set_option allowUnsafeReducibility true in
attribute [local reducible] integralSystemReduction

private theorem scalar_comp_naturality {C D D' B : Type*}
    [Category C] [Category D] [Category D'] [Category B]
    (F : C ⥤ D) (G : D ⥤ B) (F' : C ⥤ D') (G' : D' ⥤ B)
    (η : F ⋙ G ⟶ F' ⋙ G') {X Y : C} (f : X ⟶ Y) :
    G.map (F.map f) ≫ η.app Y = η.app X ≫ G'.map (F'.map f) :=
  η.naturality f

private theorem scalar_right_comp_naturality {C D B : Type*}
    [Category C] [Category D] [Category B]
    (F : C ⥤ B) (G : C ⥤ D) (H : D ⥤ B)
    (η : F ⟶ G ⋙ H) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ η.app Y = η.app X ≫ H.map (G.map f) :=
  η.naturality f

/-- Map a composite equation with its factors already expanded.
Source: functoriality. -/
private theorem scalar_map_three_eq_two {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B C' D' E' : C}
    {a : A ⟶ B} {b : B ⟶ C'} {c : C' ⟶ D'} {d : A ⟶ E'} {e : E' ⟶ D'}
    (h : a ≫ b ≫ c = d ≫ e) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e := by
  simpa only [Functor.map_comp] using congrArg F.map h

/-- Pasting of the scalar-composition diagram after mapping all of its edges into
one category. Source: elementary category theory. -/
private theorem scalar_composition_paste_mapped
    {D : Type*} [Category D]
    {O0 O1 O2 O3 O4 F0 F1 M1 M2 M3 N1 N2 N3 E0 E2 E3 E4 E5 : D}
    {x1 : O0 ⟶ O1} {x2 : O1 ⟶ O2} {x3 : O2 ⟶ O3} {t1 : O3 ⟶ M1}
    {bLk : M1 ⟶ M2} {pVk : M2 ⟶ M3} {b1 : O2 ⟶ N1} {sk : N1 ⟶ M1}
    {pW : N1 ⟶ N2} {HWbEk : N2 ⟶ N3} {gk : N3 ⟶ M3}
    {pZ1 : O1 ⟶ E2} {bEh : E2 ⟶ E3} {g1 : E3 ⟶ N2}
    {UEhbEk : E3 ⟶ E4} {g2 : E4 ⟶ N3}
    {pZ0 : O0 ⟶ E0} {cEr : E0 ⟶ E2} {bEhk : E0 ⟶ E5} {aE : E5 ⟶ E4}
    {ghk : E5 ⟶ F1} {aL2 : F1 ⟶ M3}
    {y1 : O0 ⟶ O4} {bLhk : O4 ⟶ F0} {q : F0 ⟶ F1} {aL1 : F0 ⟶ M2}
    {y2 : O4 ⟶ O3}
    (N1 : x3 ≫ t1 = b1 ≫ sk)
    (IIIk : sk ≫ bLk ≫ pVk = pW ≫ HWbEk ≫ gk)
    (IIIh : x2 ≫ b1 ≫ pW = pZ1 ≫ bEh ≫ g1)
    (Ng : UEhbEk ≫ g2 = g1 ≫ HWbEk)
    (Np : x1 ≫ pZ1 = pZ0 ≫ cEr)
    (CE : cEr ≫ bEh ≫ UEhbEk = bEhk ≫ aE)
    {aE' : E5 ⟶ E4} {aL2' : F1 ⟶ M3}
    (mix : aE' ≫ g2 ≫ gk = ghk ≫ aL2') (eE : aE = aE') (eL : aL2 = aL2')
    (IIIhk : y1 ≫ bLhk ≫ q = pZ0 ≫ bEhk ≫ ghk)
    (Na : q ≫ aL2 = aL1 ≫ pVk)
    (CL : y2 ≫ t1 ≫ bLk = bLhk ≫ aL1) :
    x1 ≫ x2 ≫ x3 ≫ t1 ≫ bLk ≫ pVk = y1 ≫ y2 ≫ t1 ≫ bLk ≫ pVk := by
  subst eE eL
  rw [reassoc_of% N1, IIIk, reassoc_of% IIIh, ← reassoc_of% Ng, reassoc_of% Np,
    reassoc_of% CE, mix, ← reassoc_of% IIIhk, Na, ← reassoc_of% CL]

/-- The pasting calculation behind integralPullbackComposition_scalar, with all
morphisms abstract. Source: elementary category theory. -/
private theorem scalar_composition_paste
    {D DE WL : Type*} [Category D] [Category DE] [Category WL]
    (U : WL ⥤ D) (H : DE ⥤ D)
    {O0 O1 O2 O3 O4 F0 F1 : D} {M1 M2 M3 N1 N2 N3 : WL} {E0 E2 E3 E4 E5 : DE}
    {x1 : O0 ⟶ O1} {x2 : O1 ⟶ O2} {x3 : O2 ⟶ O3} {t1 : O3 ⟶ U.obj M1}
    {bLk : M1 ⟶ M2} {pVk : M2 ⟶ M3} {b1 : O2 ⟶ U.obj N1} {sk : N1 ⟶ M1}
    {pW : N1 ⟶ N2} {HWbEk : N2 ⟶ N3} {gk : N3 ⟶ M3}
    {pZ1 : O1 ⟶ H.obj E2} {bEh : E2 ⟶ E3} {g1 : H.obj E3 ⟶ U.obj N2}
    {UEhbEk : E3 ⟶ E4} {g2 : H.obj E4 ⟶ U.obj N3}
    {pZ0 : O0 ⟶ H.obj E0} {cEr : E0 ⟶ E2} {bEhk : E0 ⟶ E5} {aE : E5 ⟶ E4}
    {ghk : H.obj E5 ⟶ F1} {aL2 : F1 ⟶ U.obj M3}
    {y1 : O0 ⟶ O4} {bLhk : O4 ⟶ F0} {q : F0 ⟶ F1} {aL1 : F0 ⟶ U.obj M2}
    {y2 : O4 ⟶ O3}
    (N1 : x3 ≫ t1 = b1 ≫ U.map sk)
    (IIIk : sk ≫ bLk ≫ pVk = pW ≫ HWbEk ≫ gk)
    (IIIh : x2 ≫ b1 ≫ U.map pW = pZ1 ≫ H.map bEh ≫ g1)
    (Ng : H.map UEhbEk ≫ g2 = g1 ≫ U.map HWbEk)
    (Np : x1 ≫ pZ1 = pZ0 ≫ H.map cEr)
    (CE : cEr ≫ bEh ≫ UEhbEk = bEhk ≫ aE)
    {aE' : E5 ⟶ E4} {aL2' : F1 ⟶ U.obj M3}
    (mix : H.map aE' ≫ g2 ≫ U.map gk = ghk ≫ aL2') (eE : aE = aE') (eL : aL2 = aL2')
    (IIIhk : y1 ≫ bLhk ≫ q = pZ0 ≫ H.map bEhk ≫ ghk)
    (Na : q ≫ aL2 = aL1 ≫ U.map pVk)
    (CL : y2 ≫ t1 ≫ U.map bLk = bLhk ≫ aL1) :
    x1 ≫ x2 ≫ x3 ≫ t1 ≫ U.map bLk ≫ U.map pVk =
      y1 ≫ y2 ≫ t1 ≫ U.map bLk ≫ U.map pVk := by
  have IIIk' := congrArg U.map IIIk
  have CE' := congrArg H.map CE
  simp only [Functor.map_comp] at IIIk' CE'
  exact scalar_composition_paste_mapped N1 IIIk' IIIh Ng Np CE' mix
    (congrArg H.map eE) eL IIIhk Na CL

private theorem integralComparisonSystemScalarPullback_finite_naturality
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    {M N : finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) Y}
    (a : M ⟶ N) :
    (integralComparisonDerivedSequenceScalar l E L ι X).map
        ((finiteSystemDerivedPullback (integralSystemRings l E)
          (integralSystemTransition l E) f).map a) ≫
        (integralComparisonSystemScalarPullback l E L ι f).hom.app N =
      (integralComparisonSystemScalarPullback l E L ι f).hom.app M ≫
        (finiteSystemDerivedPullback (integralSystemRings l L)
          (integralSystemTransition l L) f).map
            ((integralComparisonDerivedSequenceScalar l E L ι Y).map a) := by
  exact (integralComparisonSystemScalarPullback l E L ι f).hom.naturality a

private theorem integralComparisonSystemScalarPullback_finite_mixed
    {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V)
    (M : finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) V) :
    (integralComparisonDerivedSequenceScalar l E L ι Z).map
        ((integralComparisonSystemComposition l E h k).hom.app M) ≫
      (integralComparisonSystemScalarPullback l E L ι h).hom.app
        ((finiteSystemDerivedPullback (integralSystemRings l E)
          (integralSystemTransition l E) k).obj M) ≫
      (finiteSystemDerivedPullback (integralSystemRings l L)
        (integralSystemTransition l L) h).map
          ((integralComparisonSystemScalarPullback l E L ι k).hom.app M) =
      (integralComparisonSystemScalarPullback l E L ι (h ≫ k)).hom.app M ≫
        (integralComparisonSystemComposition l L h k).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι V).obj M) := by
  exact NatTrans.congr_app
    ((integralQuotientMixedCoherence.{u, u} l).derived_mixed E L ι h k) M

private theorem finiteSystemDerivedComposition_hom_app_eq_integralComparison
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (M : finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) V) :
    (finiteSystemDerivedComposition (integralSystemRings l E)
      (integralSystemTransition l E) h k).hom.app M =
        (integralComparisonSystemComposition l E h k).hom.app M := by
  exact NatTrans.congr_app (congrArg Iso.hom
    (finiteSystemDerivedComposition_eq_integralComparison l E h k)) M

set_option profiler true in
-- The defeq checks identify two presentations of the same reduction systems.
/-- Scalar extension carries the integral pullback compositor at E to the one at L.
Source: Stacks 06YY, 07A4, 0941, 0D6D; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: apply the faithful coherent reduction at L and cancel the invertible comparison
beta_h (U_h beta_k)(U_h U_k p). Naturality of beta_h, the pullback/scalar square for k and
h, naturality of the whole-system scalar/pullback comparison and of p, the system clause
of integralPullbackComposition at E, whole-system mixed coherence, the pullback/scalar
square for h k, naturality of the finite-system composition and the system clause at L
transform one side into the other. -/
theorem integralPullbackComposition_scalar {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι Z).map (((integralPullbackComposition l E).choose h k).hom.app K) ≫
      (integralPullbackScalarComparison l E L ι h
        ((constructibleIntegralPullback l E k).obj K)).hom ≫
      (constructibleIntegralPullback l L h).map
        (integralPullbackScalarComparison l E L ι k K).hom =
    (integralPullbackScalarComparison l E L ι (h ≫ k) K).hom ≫
      ((integralPullbackComposition l L).choose h k).hom.app
        ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι V).obj K) := by
  have : (integralSystemReduction l L Z).Faithful :=
    (integralSystemReduction_fullyFaithful l L Z).2
  apply (integralSystemReduction l L Z).map_injective
  let SV := sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
    E L ι V
  let UL {A B : Scheme.{u}} (f : A ⟶ B) :=
    finiteSystemDerivedPullback (integralSystemRings l L) (integralSystemTransition l L) f
  let T := (integralPullbackSystemIso l L h).app
      ((constructibleIntegralPullback l L k).obj (SV.obj K)) ≪≫
    (UL h).mapIso ((integralPullbackSystemIso l L k).app (SV.obj K)) ≪≫
    (UL h).mapIso ((UL k).mapIso ((integralSystemScalarIso l E L ι V).app K))
  apply (cancel_mono T.hom).1
  have N1 := scalar_comp_naturality
    (constructibleIntegralPullback l L h) (integralSystemReduction l L Z)
    (integralSystemReduction l L W) (UL h) (integralPullbackSystemIso l L h).hom
    (integralPullbackScalarComparison l E L ι k K).hom
  have IIIk := integralPullbackSystemIso_scalar l E L ι k K
  have IIIh := integralPullbackSystemIso_scalar l E L ι h
    ((constructibleIntegralPullback l E k).obj K)
  have Ng := integralComparisonSystemScalarPullback_finite_naturality l E L ι h
    ((integralPullbackSystemIso l E k).hom.app K)
  have Np := scalar_comp_naturality
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι Z) (integralSystemReduction l L Z)
    (integralSystemReduction l E Z) (integralComparisonDerivedSequenceScalar l E L ι Z)
    (integralSystemScalarIso l E L ι Z).hom
    (((integralPullbackComposition l E).choose h k).hom.app K)
  have CE := (integralPullbackComposition l E).choose_spec.2.2 h k K
  simp only [integralPullbackSystemComparison_choose] at CE
  have mix := integralComparisonSystemScalarPullback_finite_mixed l E L ι h k
    ((integralSystemReduction l E V).obj K)
  have IIIhk := integralPullbackSystemIso_scalar l E L ι (h ≫ k) K
  have Na := scalar_right_comp_naturality (UL (h ≫ k)) (UL k) (UL h)
    (finiteSystemDerivedComposition (integralSystemRings l L)
      (integralSystemTransition l L) h k).hom
    ((integralSystemScalarIso l E L ι V).hom.app K)
  have CL := (integralPullbackComposition l L).choose_spec.2.2 h k (SV.obj K)
  simp only [integralPullbackSystemComparison_choose] at CL
  have eE := finiteSystemDerivedComposition_hom_app_eq_integralComparison l E h k
    ((integralSystemReduction l E V).obj K)
  have eL := finiteSystemDerivedComposition_hom_app_eq_integralComparison l L h k
    ((integralComparisonDerivedSequenceScalar l E L ι V).obj
      ((integralSystemReduction l E V).obj K))
  simp only [T, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  have IIIk' := congrArg (UL h).map IIIk
  have CE' := scalar_map_three_eq_two
    (C := finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) Z)
    (integralComparisonDerivedSequenceScalar l E L ι Z) CE
  have eE' := congrArg (integralComparisonDerivedSequenceScalar l E L ι Z).map eE
  simp only [Functor.map_comp] at IIIk'
  exact scalar_composition_paste_mapped N1 IIIk' IIIh Ng Np CE' mix eE' eL IIIhk Na CL

end SystemScalar

end WeilConjectures
