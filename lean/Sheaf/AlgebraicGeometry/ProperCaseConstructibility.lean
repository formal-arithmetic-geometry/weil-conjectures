/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Constructibility and vanishing in the proper case

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`thm-fin-proper-case.md` (blueprint: thm-fin-proper-case).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- For a proper morphism to a finite-type scheme over a field, higher direct images
of a constructible sheaf with finite allowable coefficients are constructible. If all
geometric fibres have dimension at most `d`, these sheaves vanish in degrees above `2 * d`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-proper-case.md`
(blueprint: thm-fin-proper-case).

Proof:
If S is empty, all the displayed cohomology sheaves vanish. Otherwise the positive
annihilating exponent descends to the ground field. Convert F to the finite-stalk
constructibility convention and use proper constructibility. The compatibility of total
and bounded-below right derived functors converts its cohomology sheaves to the stated
higherDirectImage objects. For vanishing, pull back to each algebraic-closure geometric
point. Proper base change identifies the pulled-back higher direct image with the
cohomology of its geometric fibre; the torsion bound above twice the fibre dimension
makes that object zero. These geometric pullbacks jointly detect zero sheaves.
No geometric fibre or nonempty source is needed in the empty-target case. -/
theorem properCase_constructible_and_vanishing
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsProper f]
    (d : ℕ)
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim ↥(pullback f s) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    (∀ q : ℕ, Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)) ∧
    (∀ q : ℕ, 2 * d < q → IsZero (higherDirectImage Λ f (q : ℤ) F)) := by
  classical
  by_cases hS : IsEmpty S
  · let := hS
    exact ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff _).2
      (Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)),
      fun q hq ↦ Scheme.Etale.isZero_sheaf_of_isEmpty _⟩
  have : Nonempty S := not_isEmpty_iff.mp hS
  have : HasInvertibleExponent Λ S := ⟨N, hcoeff.1, hcoeff.2.2.1, hcoeff.2.2.2⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) :=
    .of_hom_of_nonempty (S ↘ Spec (.of k))
  have : Scheme.IsConstructibleSheaf F := (Scheme.isConstructibleEtaleModuleSheaf_iff F).1 hF
  let A := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff _).2 ?_, fun q hq ↦ ?_⟩
  · have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          ((_root_.DerivedCategory.Plus.ι ⋙
            (f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctor).obj A)) := by
      change Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctor.obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
      exact hasConstructibleDirectImages_of_isProper (S ↘ Spec (.of k)) f F inferInstance q
    exact Scheme.IsConstructibleSheaf.of_iso
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
        ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app A).symm)
  · refine isZero_of_forall_isZero_upperStar_algClosurePoint Λ _ fun t ↦ ?_
    let x := S.algClosurePoint t
    let sq := IsPullback.of_hasPullback f x
    have := isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ
      (fun z ↦ isOfFinAddOrder_of_finite z) sq
    rw [baseChange_eq_derivedBaseChangeMapPlus] at this
    have hvan := isZero_higherDirectImage_of_two_mul_lt
      (fun z : Λ ↦ isOfFinAddOrder_of_finite z) (pullback.snd f x)
      (pullback.snd f x) (𝟙 _) (Category.comp_id _) d (hfib _ x)
      (((pullback.fst f x)^*[ModuleCat.{u + 1} Λ]).obj F) q (by omega)
    refine IsZero.of_iso hvan
      ((((x)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).app
          ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj A) ≪≫
        (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app A)) ≪≫
        (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
          ((pullback.snd f x)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
            ((((pullback.fst f x)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app
              F)))

end AlgebraicGeometry.Etale
