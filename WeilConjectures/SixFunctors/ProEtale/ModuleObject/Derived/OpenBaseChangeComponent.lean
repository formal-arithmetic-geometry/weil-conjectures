/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModuleOpenPasting.ModuleDirectImageOpenPasting

/-! # Open base-change component isomorphism
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-construction/sec-construction-of-rf/sk-thm-sf-comp-composition/
det-sf-comp-composition-base-change.md,
Clause (1); proof (1), first sentence: the common right adjoint
`u_* j'^* ≅ j^* a_*` and its section normalization.
It is the open-pasting comparison of `ModuleOpenPasting.moduleDirectImageOpenPasting_canonical`
(blueprint: lem-sfb-module-direct-image-open-pasting), specialized to the chosen fibre
product `Z' ×_Z X`.
-/
set_option autoImplicit false
@[expose] public section
universe u
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

/-- The canonical mate comparison for open base change of condensed module objects.
Source: blueprint proof (1), first sentence: the common right adjoint and its
section normalization, for the chosen fibre product `Z' ×_Z X`.

The mate is formed from the specified upper-star compositors and the pullback
square; it is the actual natural isomorphism used by the normalized section formula. -/
noncomputable def openBaseChangeCanonical
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z Z' : Scheme.{u}} (j : X ⟶ Z) (a : Z' ⟶ Z)
    [IsOpenImmersion j] :
    (lowerStar Λ a ⋙ upperStar Λ j) ⟶
      (upperStar Λ (pullback.fst a j) ⋙ lowerStar Λ (pullback.snd a j)) :=
  (mateEquiv (upperStarLowerStarAdjunction Λ a)
      (upperStarLowerStarAdjunction Λ (pullback.snd a j))
      (TwoSquare.mk _ _ _ _
        (((upperStarComp Λ (pullback.fst a j) a).symm ≪≫
          upperStarCongr Λ (IsPullback.of_hasPullback a j).w ≪≫
          upperStarComp Λ (pullback.snd a j) j).inv))).natTrans

/-- The open base-change mate has the canonical section normalization.
Source: blueprint proof (1), first sentence: the common right adjoint and its
section normalization, for the chosen fibre product `Z' ×_Z X`.
The coprojections and section arrow are the specified module constructions, so
the displayed equation fixes the mate rather than allowing arbitrary section isos.

Proof: the mate is the comparison `β a j (pullback.snd a j) (pullback.fst a j)` of
`ModuleOpenPasting.moduleDirectImageOpenPasting_canonical` for the cartesian square
`IsPullback.of_hasPullback a j`. That lemma gives its invertibility, the bijectivity of the
coprojections for the open immersions `j` and `j' = pullback.fst a j`, and the section
formula through `ModuleOpenPasting.sectionArrow`. -/
theorem openBaseChangeComponentIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z Z' : Scheme.{u}} (j : X ⟶ Z) (a : Z' ⟶ Z)
    [IsOpenImmersion j]
    (N : Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (condensedRingObj Λ Z')) :
    IsIso (openBaseChangeCanonical Λ j a) ∧
    (∀ E : X.ProEt,
      Function.Bijective
        (ModuleOpenPasting.coprojection Λ j ((lowerStar Λ a).obj N) E)) ∧
    (∀ E : X.ProEt,
      Function.Bijective
        (ModuleOpenPasting.coprojection Λ (pullback.fst a j) N
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
            (pullback.snd a j)).obj E))) ∧
    ∀ (E : X.ProEt)
      (s : N.X.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj
        ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)))),
      ((openBaseChangeCanonical Λ j a).app N).hom.hom.app (op E)
          (ModuleOpenPasting.coprojection Λ j ((lowerStar Λ a).obj N) E s) =
        ModuleOpenPasting.coprojection Λ (pullback.fst a j) N
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
            (pullback.snd a j)).obj E)
          (N.X.obj.map
            (ModuleOpenPasting.sectionArrow a j (pullback.snd a j)
              (pullback.fst a j) (IsPullback.of_hasPullback a j) E).op s) := by
  obtain ⟨β, ⟨hbij, hsec⟩, -, -, -, -, -, hmate⟩ :=
    ModuleOpenPasting.moduleDirectImageOpenPasting_canonical Λ
  have hβ : (β a j (pullback.snd a j) (pullback.fst a j)
      (IsPullback.of_hasPullback a j)).hom = openBaseChangeCanonical Λ j a :=
    hmate a j (pullback.snd a j) (pullback.fst a j) (IsPullback.of_hasPullback a j)
  refine ⟨?_, fun E ↦ hbij j _ E, fun E ↦ hbij (pullback.fst a j) N _, fun E s ↦ ?_⟩
  · rw [← hβ]
    infer_instance
  · rw [← hβ]
    exact hsec a j (pullback.snd a j) (pullback.fst a j) (IsPullback.of_hasPullback a j) N E s

end AlgebraicGeometry.ProEtale.CondensedRing
end
