/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarCoherence

/-!
# Section normalization of the etale and pro-etale comparison mates

Source: Stacks Project, Tags 09A5, 09A6, 09AF and 03D3
(blueprint: lem-sp-site-comparison-direct-image-mate-normalization).

We use fixed-scalar module sheaves, the coefficient presentation of the recorded
comparison adjunction. Restriction along an open immersion is the literal restriction
model of inverse image. All maps are the published canonical maps.
-/

@[expose] public section

set_option autoImplicit false
-- Preserve the original finite-ring binders even when a proof needs no finiteness.
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The direct-image identification is the identity on sections over the base change.
Source: Stacks, Tag 09A5 (blueprint: lem-sp-site-comparison-direct-image-mate-normalization).
Proof: both restrictions evaluate at the same chosen fibre product; their restrictions
and scalar actions coincide, and a morphism acts by its component on that product. -/
theorem siteComparison_directImage_sections {Z T : Scheme.{u}} (g : Z ⟶ T)
    (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) (V : T.Etale) :
    ((supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} Λ) g).hom.app G).hom.app
      (op V) = 𝟙 (G.obj.obj
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
          ((Scheme.toProEt T).obj V)))) := by
  change G.obj.map (𝟙 _) = 𝟙 _
  exact G.obj.map_id _

/-- The inverse of the recorded pullback comparison is conjugate to the section identity.
Source: Stacks, Tags 09A5 and 09A6
(blueprint: lem-sp-site-comparison-direct-image-mate-normalization).
Proof: compose the geometric and comparison adjunctions. The Hom bijections for the
commutative square of sites identify precomposition by kappa with postcomposition by
the inverse direct-image identification. Apply the conjugation bijection; its unit
identity fixes both orientation and normalization, without choosing another isomorphism. -/
theorem siteComparison_pullback_conjugate {Z T : Scheme.{u}} (g : Z ⟶ T) :
    conjugateEquiv
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).comp
        (comparisonAdjunction (ModuleCat.{u + 1} Λ) Z))
      ((comparisonAdjunction (ModuleCat.{u + 1} Λ) T).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g))
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) g).inv =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} Λ) g).inv := by
  change (conjugateEquiv _ _) ((conjugateEquiv _ _).symm _) = _
  exact Equiv.apply_symm_apply _ _

/-- The published direct-image comparison is the geometric mate of kappa.
Source: Stacks, Tag 09A6, canonical map
(blueprint: lem-sp-site-comparison-direct-image-mate-normalization).
Proof: expand the mate as q(M epsilon) q(kappa) v. Conjugating kappa gives the identity
on right-image sections by the preceding clause. The two successive mate bijections
then give exactly the published comparison, itself the comparison-adjunction mate of
that same identity. No invertibility of this direct-image mate is asserted. -/
theorem siteComparison_directImage_mate {Z T : Scheme.{u}} (g : Z ⟶ T) :
    lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ) =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
        (TwoSquare.mk _ _ _ _
          (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) g).inv)).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) T)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) Z)
    (TwoSquare.mk _ _ _ _
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) g).inv)
  rw [siteComparison_pullback_conjugate] at h
  have hd : (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} Λ) g).inv =
      (lowerStarCompComparisonLowerStarIso g (ModuleCat.{u + 1} Λ)).inv := by
    rfl
  rw [hd] at h
  apply (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} Λ) Z)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) T)).injective
  simp only [lowerStarComparisonUpperStarBaseChange, Equiv.apply_symm_apply]
  exact h.symm

/-- On an etale object the direct-image mate sends eta of x to eta of x.
Source: Stacks, Tags 09A5 and 09A6
(blueprint: lem-sp-site-comparison-direct-image-mate-normalization).
Proof: evaluate the existing
`unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app` at V and x. The right-image
identification is the identity on sections over V times Z; its scalar action is unchanged.
Naturality in F follows because all morphisms in the identity are natural transformations. -/
theorem siteComparison_directImage_unit_sections {Z T : Scheme.{u}} (g : Z ⟶ T)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : T.Etale)
    (x : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj F).obj.obj (op V)) :
    (((lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ)).app F).hom.app
        (op ((Scheme.toProEt T).obj V)))
      ((((comparisonAdjunction (ModuleCat.{u + 1} Λ) T).unit.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj F)).hom.app (op V)) x) =
      (((comparisonAdjunction (ModuleCat.{u + 1} Λ) Z).unit.app F).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))) x := by
  have h := unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app
    (ModuleCat.{u + 1} Λ) g F
  have hv := congrArg (fun f ↦ f.hom.app (op V)) h
  change
    (((comparisonAdjunction (ModuleCat.{u + 1} Λ) T).unit.app
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj F)).hom.app (op V)) ≫
        (((lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ)).app F).hom.app
          (op ((Scheme.toProEt T).obj V))) =
    (((comparisonAdjunction (ModuleCat.{u + 1} Λ) Z).unit.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))) ≫
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).obj F).obj.map (𝟙 _) at hv
  erw [((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).obj F).obj.map_id,
    Category.comp_id] at hv
  exact congrArg (fun f ↦ f x) hv

/-- Open restriction commutes with comparison by the identity on sections.
Source: Stacks, Tag 09AF (blueprint: lem-sp-site-comparison-direct-image-mate-normalization).
Proof: both composites send V over U to the same scheme V over X, and keep the same
restriction maps and constant scalar action. Their natural identification is the identity. -/
theorem siteComparison_openRestriction_sections {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (V : U.Etale) :
    ((comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} Λ) j).hom.app G).hom.app
      (op V) = 𝟙 (((Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) j).obj
        ((comparisonLowerStar (ModuleCat.{u + 1} Λ) X).obj G)).obj.obj (op V)) := by
  rfl

/-- The canonical extension comparison is conjugate to identity on open restriction.
Source: Stacks, Tag 09AF (blueprint: lem-sp-site-comparison-direct-image-mate-normalization).
Proof: compose each extension adjunction with its comparison adjunction. Both right
adjoints are literal restriction, and the Hom chains identify the left adjoints by Yoneda.
This is the published canonical comparison, with its given orientation. Applying the
conjugation bijection recovers the section identity. -/
theorem siteComparison_openExtension_conjugate {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    conjugateEquiv
      ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (comparisonAdjunction (ModuleCat.{u + 1} Λ) X))
      ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).comp
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j))
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).inv =
      (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} Λ) j).hom := by
  change (conjugateEquiv _ _) ((conjugateEquiv _ _).symm _) = _
  exact Equiv.apply_symm_apply _ _

/-- The extension comparison carries the first composite unit to the second.
Source: Stacks, Tags 09AF and 03D3
(blueprint: lem-sp-site-comparison-direct-image-mate-normalization).
Proof: apply the unit equation for conjugate isomorphisms to the two composite
adjunctions and the identity restriction comparison. Expand their units as I(eta) u
and s(u) eta. The conjugation identity identifies the given extension comparison with
this unit-normalized isomorphism. Every factor is natural in F. -/
theorem siteComparison_openExtension_units {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).unit.app F ≫
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) j).map
        ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F)) ≫
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) j).map
        ((comparisonLowerStar (ModuleCat.{u + 1} Λ) X).map
          ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).hom.app F)) =
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) U).unit.app F ≫
        (comparisonLowerStar (ModuleCat.{u + 1} Λ) U).map
          ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F)) := by
  have h := unit_conjugateEquiv
    ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).comp
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j))
    ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).comp
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X))
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).hom F
  have hc : conjugateEquiv
      ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).comp
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j))
      ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (comparisonAdjunction (ModuleCat.{u + 1} Λ) X))
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).hom =
        (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} Λ) j).inv := by
    change (conjugateEquiv _ _) ((conjugateEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  rw [hc] at h
  dsimp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj, comparisonLowerStarOpenImmersionRestrictionIso, Iso.refl_inv,
    NatTrans.id_app] at h
  erw [Category.comp_id] at h
  simpa only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] using h.symm

/-- The extension comparison sends eta of the etale extension unit to the pro-etale unit
of eta. Source: Stacks, Tag 09AF
(blueprint: lem-sp-site-comparison-direct-image-mate-normalization).
Proof: evaluate the composite-unit identity at V and m. Literal open restriction and
comparison restriction give the displayed element formula. Its naturality follows from
the sheaf-morphism identity; empty opens and zero coefficients require no exception. -/
theorem siteComparison_openExtension_unit_sections {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : U.Etale) (m : F.obj.obj (op V)) :
    (((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).hom.app F).hom.app
      (op ((Scheme.toProEt X).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj V))))
      ((((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F)).hom.app
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj V)))
        ((((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).unit.app F).hom.app
          (op V)) m)) =
      (((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F)).hom.app
          (op ((Scheme.toProEt U).obj V)))
        ((((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).unit.app F).hom.app (op V)) m) := by
  have h := siteComparison_openExtension_units Λ j F
  exact congrArg (fun f ↦ (f.hom.app (op V)) m) h

end AlgebraicGeometry.ProEtale
