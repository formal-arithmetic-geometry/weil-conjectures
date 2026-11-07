/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import Mathlib.AlgebraicGeometry.Noetherian

import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedFinitePseudoCoherentModel
import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeCompletedModuleRealizationExact
import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerAlgebraicDerivedPresentation
import Submission.WeilConjectures.RingTheory.AdicCompletionNoetherian

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Reconstruction of a lisse normalized tower

Source: Stacks Tags 09BV, 09AV, and bounded finite truncations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem finite_lisse_of_iso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    {F G : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X A))}
    (e : F ≅ G) (h : IsRelativelyFiniteLisseModule g A G) :
    IsRelativelyFiniteLisseModule g A F := by
  obtain ⟨S, hS, hs⟩ := h
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨N, hN, ⟨eN⟩⟩ := hs V f hf
  exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ V).mapIso e ≪≫ eN⟩⟩

private theorem reduction_transition_naturality (X : Scheme.{u})
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    {K K' : DerivedCategory (pbcModules X R)} (f : K ⟶ K') :
    (pbcDerivedExtend φ).map f ≫ pbcReductionTransition φ ψ χ h K' =
      pbcReductionTransition φ ψ χ h K ≫
        (pbcDerivedRestrict ψ).map ((pbcDerivedExtend χ).map f) := by
  unfold pbcReductionTransition
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hu := (pbcDerivedScalarAdjunction χ).unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc]
  congr 1
  exact (pbcDerivedRestrictComp φ ψ χ h).inv.naturality ((pbcDerivedExtend χ).map f)

/-- On an immersed lisse stratum a normalized tower has a single bounded local
completed-coefficient model, with every forward quotient square.

Source: Stacks, proetale.tex, Tag 09BV; more-algebra.tex, Tags 09AV and 066E.
(blueprint: lem-weil-pbc-lisse-normalized-tower-local-models).

Proof: the algebraic derived presentation supplies a covering sieve and on each
member a pseudo-coherent complex E over the completion, with cohomology in [a,b].
Its exact relative completed realization has the given finite reductions, with
finite-lisse cohomology and all the specified transition equations. Truncate a
finite-free model of E above b and below a: Noetherianity makes the cycles at b
finite, and the cokernel at a is finite. Both truncations are quasi-isomorphisms.
Apply exact completed realization termwise to the resulting finite complex P.
The terms vanish in the same interval and are relatively adic lisse. The exact
functor's localization comparison and the isomorphism Q(P)≅E give an isomorphism
from Q(L) to the realized derived object. Apply each derived quotient functor to
this single isomorphism and compose with the algebraic presentation. Homology
and scalar restriction transport finite lissity through these isomorphisms.
Naturality of the reduction adjunct gives the forward semilinear squares after
composition. There is no finite Tor assumption, and no assertion that the first
truncated term is projective. -/
theorem lisseNormalizedTower_local_models
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n))))) :
    ∃ V : Sieve (⊤_ Y.ProEt), V ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
      ∀ (U : Y.ProEt) (f : U ⟶ ⊤_ Y.ProEt), V f →
        ∃ L : CochainComplex (pbcModules U.left
            ((adicTowerInverseImage (U.hom ≫ g)).obj (pbcAdicCompletion X d))) ℤ,
          (∀ q : ℤ, (q < a ∨ b < q) → IsZero (L.X q)) ∧
          (∀ q : ℤ, @IsRelativelyAdicLisseModule _ _ (U.hom ≫ g) A _
            d.noetherian d.ideal
            ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
              (pbcCompletedComparison X d).hom)).obj (L.X q))) ∧
          (∀ (n : ℕ) (q : ℤ),
            IsRelativelyFiniteLisseModule (U.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
              ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                (pbcLevelConstantComparison X d n).hom)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj
                    (adicTowerLocalReduction d (U.hom ≫ g) L n)))) ∧
          ∃ e : ∀ n : ℕ, adicTowerLocalReduction d (U.hom ≫ g) L n ≅
              (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
                (M.level n),
            ∀ (m n : ℕ) (hnm : n ≤ m),
              (e m).hom ≫ adicTowerRestrictedTransition d (U.hom ≫ g) M m n hnm =
                adicTowerLocalTransition d (U.hom ≫ g) L m n hnm ≫
                  (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                    (pbcAdicQuotient X d m n hnm))).map (e n).hom := by
  classical
  let : IsNoetherianRing A := d.noetherian
  let : IsNoetherianRing (AdicCompletion d.ideal A) :=
    AdicCompletion.isNoetherianRing d.ideal
  obtain ⟨V, hV, hpres⟩ :=
    lisse_tower_algebraic_derived_presentation X Y g d M a b hab hbounded hlisse
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨E, hE, hvan, hreal⟩ := hpres U f hf
  obtain ⟨φ, hφ, β, hβ, hc, hlim, hcolim, hterms⟩ :=
    relative_completed_module_realization_exact X U.left (U.hom ≫ g) d
  let c := completedConstantRealization U.left d.ideal φ ⋙ pbcRestrict β ⋙
    pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map (pbcCompletedComparison X d).inv)
  let : c.Additive := hc
  let : PreservesFiniteLimits c := hlim
  let : PreservesFiniteColimits c := hcolim
  obtain ⟨hfinite, e, he⟩ := hreal φ hφ β hβ hc hlim hcolim
  obtain ⟨P, hP, hfin, ⟨eP⟩⟩ := exists_boundedFinite_model E a b hE hvan
  let L := (c.mapHomologicalComplex (.up ℤ)).obj P
  let α : DerivedCategory.Q.obj L ≅ c.mapDerivedCategory.obj E :=
    (c.mapDerivedCategoryFactors.app P).symm ≪≫ c.mapDerivedCategory.mapIso eP
  let ε (n : ℕ) :=
    (pbcDerivedExtend ((adicTowerInverseImage (U.hom ≫ g)).map
      (pbcAdicProjection X d n))).mapIso α
  refine ⟨L, ?_, ?_, ?_, fun n ↦ ε n ≪≫ e n, ?_⟩
  · intro q hq
    exact c.map_isZero (hP q hq)
  · intro q
    exact hterms (P.X q) (hfin q)
  · intro n q
    exact finite_lisse_of_iso (U.hom ≫ g) _
      ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).mapIso
          ((DerivedCategory.homologyFunctor _ q).mapIso (ε n))) (hfinite n q)
  · intro m n hnm
    change ((ε m).hom ≫ (e m).hom) ≫ _ = _ ≫
      (pbcDerivedRestrict _).map ((ε n).hom ≫ (e n).hom)
    rw [Category.assoc, he m n hnm, ← Category.assoc]
    have hn := reduction_transition_naturality U.left
      ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicProjection X d m))
      ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicQuotient X d m n hnm))
      ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicProjection X d n))
      (((adicTowerInverseImage (U.hom ≫ g)).map_comp _ _).symm.trans
        (congrArg (adicTowerInverseImage (U.hom ≫ g)).map
          (pbcAdicProjection_comp X d m n hnm))) α.hom
    change (ε m).hom ≫ _ = _ ≫ (pbcDerivedRestrict _).map (ε n).hom at hn
    rw [hn]
    simp only [adicTowerLocalTransition, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme
