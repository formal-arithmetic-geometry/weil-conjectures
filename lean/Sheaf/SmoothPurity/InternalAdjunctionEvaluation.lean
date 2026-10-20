module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-! # Evaluation formula for the canonical internal compact-support adjunction

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-asd-internal-adjunction-evaluation.md (blueprint: lem-asd-internal-adjunction-evaluation).

## Main statements

* `internalAdjunctionEvaluation` states the tensor--Hom transpose formula for the
  canonical compact-support internal adjunction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace CategoryTheory

private theorem conjugate_uncurry
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {C₀ : C} {M : D} (f : C₀ ⟶ R₁.obj M) :
    (a₂.homEquiv _ _).symm (f ≫ (conjugateEquiv a₁ a₂ α).app M) =
      α.app C₀ ≫ (a₁.homEquiv _ _).symm f := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, ← α.naturality_assoc]

private theorem parametrized_conjugate_uncurry
    {C D E : Type*} [Category C] [Category D] [Category E]
    {T₁ T₂ : C ⥤ D ⥤ E} {H₁ H₂ : Cᵒᵖ ⥤ E ⥤ D}
    (a₁ : T₁ ⊣₂ H₁) (a₂ : T₂ ⊣₂ H₂) (π : T₂ ≅ T₁)
    (P : C) (M : E) (C₀ : D) (f : C₀ ⟶ (H₁.obj (op P)).obj M) :
    ((a₂.adj P).homEquiv C₀ M).symm
        (f ≫ ((a₁.conjugateIso a₂ π).hom.app (op P)).app M) =
      (π.hom.app P).app C₀ ≫ ((a₁.adj P).homEquiv C₀ M).symm f := by
  change ((a₂.adj P).homEquiv C₀ M).symm
    (f ≫ (conjugateEquiv (a₁.adj P) (a₂.adj P) (π.hom.app P)).app M) = _
  exact conjugate_uncurry (a₁.adj P) (a₂.adj P) (π.hom.app P) f

private theorem composite_conjugate_uncurry
    {C D : Type*} [Category C] [Category D]
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
    (tS : TS ⊣₂ HS) (tX : TX ⊣₂ HX) (a : L ⊣ R) (b : F ⊣ G)
    (π : F ⋙ TX ≅ TS ⋙ (Functor.whiskeringLeft _ _ _).obj L ⋙
      (Functor.whiskeringRight _ _ _).obj F)
    (P : D) (M C₀ : C) (f : C₀ ⟶ R.obj ((HS.obj (op P)).obj (G.obj M))) :
    ((tX.adj (F.obj P)).homEquiv C₀ M).symm
        (f ≫ (((tS.comp a b).conjugateIso (tX.precomp F) π).hom.app (op P)).app M) =
      (π.hom.app P).app C₀ ≫ F.map
        (((tS.adj P).homEquiv (L.obj C₀) (G.obj M)).symm
          ((a.homEquiv C₀ _).symm f)) ≫ b.counit.app M := by
  have h := parametrized_conjugate_uncurry (tS.comp a b) (tX.precomp F) π P M C₀ f
  simp only [ParametrizedAdjunction.precomp_adj, ParametrizedAdjunction.comp_adj,
    Adjunction.comp_homEquiv, Equiv.symm_trans, Equiv.trans_apply] at h
  change _ = (π.hom.app P).app C₀ ≫
    (b.homEquiv _ _).symm (((tS.adj P).homEquiv _ _).symm
      ((a.homEquiv _ _).symm f)) at h
  simpa only [Functor.comp_obj, Adjunction.homEquiv_counit, Category.assoc] using h

end CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The mate calculation identifying the named internal-adjunction isomorphism with its
projection, tensor, and exceptional-counit representative.
Source: the displayed Hom-bijection calculation in the proof of
`lem-asd-internal-adjunction-evaluation`.
Proof: Expand the parametrized conjugate and apply conjugateEquiv counit naturality to obtain
projection followed by tensor transpose and exceptional counit.
(blueprint: lem-asd-internal-adjunction-evaluation-mate-core).
-/
theorem internalAdjunctionEvaluation_mate_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)))
    (K Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (h : Q ⟶
      (R((f)_*[ModuleCat A])).obj
        (((RHom(X)[ModuleCat A]).obj (op M)).obj
          ((R(f)^![ModuleCat A]).obj K))) :
    ((derivedTensorHomAdjunction (ModuleCat A) ((R(f)_![ModuleCat A]).obj M)).homEquiv
        Q K).symm
      (h ≫ (((derivedHomRightDerivedLowerShriekIsoOfFinite A f).app (op M)).app K).hom) =
      ((projectionMap (ModuleCat A) f).app M).app Q ≫
        (R(f)_![ModuleCat A]).map
          (((derivedTensorHomAdjunction (ModuleCat A) M).homEquiv
              (L((f)^*[ModuleCat A]).obj Q)
              ((R(f)^![ModuleCat A]).obj K)).symm
            (((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv
                Q (((RHom(X)[ModuleCat A]).obj (op M)).obj
                  ((R(f)^![ModuleCat A]).obj K))).symm h)) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat A) f).counit.app K := by
  sorry

/-- The tensor--Hom transpose of the canonical compact-support internal adjunction.
Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-asd-internal-adjunction-evaluation.md (blueprint: lem-asd-internal-adjunction-evaluation).
-/
theorem internalAdjunctionEvaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)))
    (K Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (h : Q ⟶
      (R((f)_*[ModuleCat A])).obj
        (((RHom(X)[ModuleCat A]).obj (op M)).obj
          ((R(f)^![ModuleCat A]).obj K))) :
    ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
        ((R(f)_![ModuleCat A]).obj M) ≫
      ((derivedTensorHomAdjunction (ModuleCat A) ((R(f)_![ModuleCat A]).obj M)).homEquiv
        Q K).symm
      (h ≫ (((derivedHomRightDerivedLowerShriekIsoOfFinite A f).app (op M)).app K).hom) =
      ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
        ((R(f)_![ModuleCat A]).obj M) ≫
        ((projectionMap (ModuleCat A) f).app M).app Q ≫
        (R(f)_![ModuleCat A]).map
          (((derivedTensorHomAdjunction (ModuleCat A) M).homEquiv
              (L((f)^*[ModuleCat A]).obj Q)
              ((R(f)^![ModuleCat A]).obj K)).symm
            (((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv
                Q (((RHom(X)[ModuleCat A]).obj (op M)).obj
                  ((R(f)^![ModuleCat A]).obj K))).symm h)) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat A) f).counit.app K := by
  rw [internalAdjunctionEvaluation_mate_core A f M K Q h]


end AlgebraicGeometry.Etale
