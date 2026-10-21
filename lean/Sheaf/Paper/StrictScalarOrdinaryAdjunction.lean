/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancing
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.StrictScalarOrdinaryAdjointsExist
import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
import all Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.ExactPullbackDerivedAdjunction
import Sheaf.Paper.ConstantDirectImagePreservesComplete

/-! # Normalized scalar comparisons for ordinary geometric adjunctions

Source: Stacks 099N (proetale.tex, lemma-pushforward-Noetherian-case), part (1).
(blueprint: lem-weil-pbc-strict-scalar-ordinary-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite ConstantCompletion
namespace AlgebraicGeometry.Scheme.StrictScalarBalancing
variable {A : Type (u + 1)} [CommRing A]

private theorem constant_preservation (d : AdicCoefficientDatum A) (B : Balancing d)
    {U V : Scheme.{u}} (f : U ⟶ V)
    (P : PullCompatibility f d (B.ρ V) (B.ρ U))
    (R : D (ring U d false) ⥤ D (ring V d false)) (a : P.constant.ordinary ⊣ R) :
    ∀ N : D (ring U d false), IsComplete (finiteMap (topology U) A d.ideal false 0) N →
      IsComplete (finiteMap (topology V) A d.ideal false 0) (R.obj N) := by
  let := d.noetherian
  let := HasDerivedCategory.standard (Mod (ring V d false))
  let := HasDerivedCategory.standard (Mod (ring U d false))
  let := HasDerivedCategory.standard (Mod (constant (topology V) A))
  let := HasDerivedCategory.standard (Mod (constant (topology U) A))
  let push := (proEtaleModelBaseChange f).sheafPushforwardContinuous (Type (u + 1))
    (topology V) (topology U)
  let adj := (proEtaleModelBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
    (topology V) (topology U)
  obtain ⟨G, _, aM, _⟩ := module_adjunction_exists push adj (inverseData f)
    (constantMap (inverseData f) A)
  have : IsIso (constantMap (inverseData f) A) := by dsimp only [constantMap]; infer_instance
  have := pull_finiteLimits_of_isIso (inverseData f) (constantMap (inverseData f) A)
  have := aM.leftAdjoint_preservesColimits
  have : (Q (constant (topology V) A)).IsLocalization
      (HomologicalComplex.quasiIso (Mod (ring V d false)) (.up ℤ)) := by
    exact inferInstanceAs ((DerivedCategory.Q (C := Mod (ring V d false))).IsLocalization
      (HomologicalComplex.quasiIso (Mod (ring V d false)) (.up ℤ)))
  obtain ⟨RF, η, hRF, hη, aD, _⟩ := exactPullbackDerivedAdjunction push adj
    (inverseData f) (constantMap (inverseData f) A) G aM
  have hpres := constantDirectImage_preservesComplete (topology V) (topology U) A d.ideal
    push adj (inverseData f) G aM RF η hRF hη
  have : Functor.IsLeftDerivedFunctor
      (derivedPull (inverseData f) push adj (constantMap (inverseData f) A)).functor
      (derivedPull (inverseData f) push adj (constantMap (inverseData f) A)).comparison
      (HomologicalComplex.quasiIso (Mod (ring V d false)) (.up ℤ)) :=
    (derivedPull (inverseData f) push adj (constantMap (inverseData f) A)).universal
  have := P.constant.ordinaryUniversal
  let e := Functor.leftDerivedUnique P.constant.ordinary
    (derivedPull (inverseData f) push adj (constantMap (inverseData f) A)).functor
    (derivedPull (inverseData f) push adj (constantMap (inverseData f) A)).comparison
    P.constant.ordinaryFactors.hom
    (HomologicalComplex.quasiIso (Mod (ring V d false)) (.up ℤ))
  let er := (aD.ofNatIsoLeft e).rightAdjointUniq a
  intro N hN
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing d.ideal)
  have hk := (koszul_quotient_reflector (topology V) A d.ideal false r g hg).choose_spec.2.2.2
  apply (hk _).mp
  exact (NatTrans.isIso_app_iff_of_iso (completionUnit (topology V) A d.ideal false)
    (er.app N)).mp ((hk _).mpr (hpres N hN))

private theorem complete_iso (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool)
    {M N : D (ring T d b)} (e : M ≅ N)
    (h : IsComplete (finiteMap (topology T) A d.ideal b 0) M) :
    IsComplete (finiteMap (topology T) A d.ideal b 0) N := by
  let := d.noetherian
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing d.ideal)
  have hk := (koszul_quotient_reflector (topology T) A d.ideal b r a ha).choose_spec.2.2.2
  exact (hk N).mp ((NatTrans.isIso_app_iff_of_iso
    (completionUnit (topology T) A d.ideal b) e).mp ((hk M).mpr h))

private theorem complete_of_restriction (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (N : D (ring T d true))
    (h : IsComplete (finiteMap (topology T) A d.ideal false 0)
      ((dres (scalar T d)).obj N)) :
    IsComplete (finiteMap (topology T) A d.ideal true 0) N := by
  let := d.noetherian
  let : HasDerivedCategory (Mod (ring T d true)) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Mod (ring T d false)) := HasDerivedCategory.standard _
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing d.ideal)
  have hk (b : Bool) :=
    (koszul_quotient_reflector (topology T) A d.ideal b r a ha).choose_spec.2.2.2
  obtain ⟨e, he⟩ := completion_restriction (topology T) A d.ideal
  have : IsIso ((completionUnit (topology T) A d.ideal false).app
      ((dres (scalar T d)).obj N)) := (hk false _).mpr h
  have : IsIso ((dres (scalar T d)).map
      ((completionUnit (topology T) A d.ideal true).app N)) := by rw [← he]; infer_instance
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (siteModuleRings (constant (topology T) A)))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (siteModuleRings (completed (topology T) A d.ideal)))
  have : (dres (scalar T d)).ReflectsIsomorphisms :=
    siteDerivedRestrictScalars_reflectsIsomorphisms (scalar T d)
  exact (hk true N).mp (isIso_of_reflects_iso _ (dres (scalar T d)))

/-- Every stipulated ordinary pullback model has normalized right adjoints, and these
right adjoints preserve derived completeness.

Source: Stacks 07A6 (sites-cohomology.tex, lemma-adjoint) and 099N
(proetale.tex, lemma-pushforward-Noetherian-case), part (1); scalar supplement Step 6.
(blueprint: lem-weil-pbc-strict-scalar-ordinary-adjunction).

Proof: use the geometric adjunction of the transported pro-etale sites and the
constant and completed coefficient identifications to construct the ordinary module
adjunctions. Exact pullback and K-injective resolutions give their unbounded derived
adjunctions. The universal comparison identifies each supplied PullModel with this
exact localization. The ordinary scalar transpose equation gives the mate of a inverse.
Restriction is flat and exact and preserves K-injectives, so that mate is invertible;
this yields chi with the stated normalization. Constant direct image preserves local
completeness by the constant-element criterion and the local direct-image theorem.
Restriction preserves and reflects local ideal completeness, and chi identifies the
two restricted direct images; hence completed direct image preserves completeness as
well. Transport these properties through the unique normalized identifications of
the supplied left-derived functors and their right adjoints. The argument uses every
ambient complex without boundedness or a completeness hypothesis on its pullback. -/
theorem strictScalarOrdinaryAdjunction (d : AdicCoefficientDatum A) (B : Balancing d)
    {U V : Scheme.{u}} (f : U ⟶ V)
    (P : PullCompatibility f d (B.ρ V) (B.ρ U)) :
    ∃ (rightA : D (ring U d true) ⥤ D (ring V d true))
      (right0 : D (ring U d false) ⥤ D (ring V d false))
      (adjA : P.completed.ordinary ⊣ rightA)
      (adj0 : P.constant.ordinary ⊣ right0)
      (χ : rightA ⋙ dres (scalar V d) ≅ dres (scalar U d) ⋙ right0),
      χ.hom = (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ P.a.inv)).natTrans ∧
      (∀ N : D (ring U d true), IsComplete (finiteMap (topology U) A d.ideal true 0) N →
        IsComplete (finiteMap (topology V) A d.ideal true 0) (rightA.obj N)) ∧
      (∀ N : D (ring U d false), IsComplete (finiteMap (topology U) A d.ideal false 0) N →
        IsComplete (finiteMap (topology V) A d.ideal false 0) (right0.obj N)) := by
  obtain ⟨RA, R0, aA, a0, χ, hχ⟩ := strictScalarOrdinaryAdjointsExist d B f P
  have hp0 := constant_preservation d B f P R0 a0
  refine ⟨RA, R0, aA, a0, χ, hχ, ?_, hp0⟩
  intro N hN
  apply complete_of_restriction V d
  apply complete_iso V d false (χ.app N).symm
  apply hp0
  let := d.noetherian
  obtain ⟨e, he⟩ := equivalence (topology U) A d.ideal
  obtain ⟨i⟩ := he
  exact complete_iso U d false (i.app ⟨N, hN⟩) (e.functor.obj ⟨N, hN⟩).property

end AlgebraicGeometry.Scheme.StrictScalarBalancing
