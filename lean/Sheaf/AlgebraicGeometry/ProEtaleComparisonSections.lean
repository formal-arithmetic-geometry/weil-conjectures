/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
import Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos

/-!
# Sections of the etale to pro-etale comparison inverse image

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
Sections of the comparison inverse image (blueprint: lem-weil-pbc-comparison-sections).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The section cocone induced by a map to the restriction of a pro-etale sheaf.
Its legs are the given map at a stage followed by restriction to the limit object.
Source: blueprint, comparison-sections, adjunction paragraph
(blueprint: lem-weil-pbc-comparison-sections). -/
def proEtaleComparisonSectionsCocone {X : Scheme.{u}}
    {A : Type v} [Category.{w} A] {I : Type u} [SmallCategory I]
    (D : I ⥤ X.Etale) (V : X.ProEt)
    (π : (Functor.const I).obj V ⟶ D ⋙ Scheme.toProEt X)
    (F : Sheaf X.smallEtaleTopology A) (G : Sheaf (Scheme.ProEt.topology X) A)
    (η : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous A
      X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G) :
    Cocone (D.op ⋙ F.obj) where
  pt := G.obj.obj (op V)
  ι :=
    { app := fun i ↦ η.hom.app (op (D.obj i.unop)) ≫ G.obj.map (π.app i.unop).op
      naturality := by
        intro i j f
        dsimp
        rw [← Category.assoc, η.hom.naturality]
        change (η.hom.app (op (D.obj i.unop)) ≫
          G.obj.map ((Scheme.toProEt X).map (D.map f.unop)).op) ≫
            G.obj.map (π.app j.unop).op =
          (η.hom.app (op (D.obj i.unop)) ≫ G.obj.map (π.app i.unop).op) ≫ 𝟙 _
        rw [Category.comp_id, Category.assoc, ← G.obj.map_comp, ← op_comp]
        congr 2
        simpa using congrArg Quiver.Hom.op (π.naturality f.unop).symm }

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a section on an etale object back to the terminal object over a basis
scheme, along a specified map to that object. This is the inverse-image unit followed
by restriction along the graph into the scheme fibre product.
Source: blueprint, comparison-sections, scheme inverse-image clause
(blueprint: lem-weil-pbc-comparison-sections). -/
noncomputable def proEtaleBasisPulledBackSection {X : Scheme.{u}}
    {A : Type v} [Category.{w} A] (U : X.AffineProEt) (W : X.Etale)
    (h : (Scheme.AffineProEt.toProEt X).obj U ⟶ (Scheme.toProEt X).obj W)
    (F : Sheaf X.smallEtaleTopology A) (G : Sheaf U.left.smallEtaleTopology A)
    (η : F ⟶ (@Functor.sheafPushforwardContinuous _ _ _ _
      (MorphismProperty.Over.pullback @Etale ⊤ U.hom) A _
      (X.smallGrothendieckTopology @Etale) (U.left.smallGrothendieckTopology @Etale)
      (Etale.isContinuous_overPullback U.hom)).obj G) :
    F.obj.obj (op W) ⟶ G.obj.obj (op (Scheme.Etale.mk (𝟙 U.left))) :=
  η.hom.app (op W) ≫ G.obj.map
    (MorphismProperty.Over.homMk
      (A := Scheme.Etale.mk (𝟙 U.left))
      (B := (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj W)
      (pullback.lift h.left (𝟙 U.left)
        (by
          have hw : h.left ≫ W.hom = U.hom := MorphismProperty.Over.w h
          exact hw.trans (Category.id_comp U.hom).symm)) (by simp) :
        Scheme.Etale.mk (𝟙 U.left) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj W).op

/-- The section formula for module sheaves over any fixed coefficient ring.
The first equality is a natural isomorphism in the sheaf. The second equality says
that the canonical unit-and-restriction cocone for every affine etale
finite-presentation presentation is a colimit, so the identification uses the
restriction transition maps, rather than an unspecified bijection.
Source: blueprint, comparison-sections, statement and both proof paragraphs
(blueprint: lem-weil-pbc-comparison-sections).

Proof:
1. On an affine basis object put P(F)(U) = Gamma(U_et, F|U), where restriction is
   scheme inverse image. Pass to a cofinal upper tail of the presentation. Apply
   lem-weil-pbc-etale-section-continuity (respectively its sets version) to the
   terminal etale object; the inverse-image-restriction lemmas identify its stage
   sections with F(U_i), with their actual restriction maps.
2. By lem-weil-pbc-ind-etale-basis it suffices to check finite basis covers.
   Ind-etale stability presents each covering member by affine etale stages.
   Every tuple of stages still covers, and fibre products commute with these limits.
   Apply continuity to the members and their pairwise fibre products. Move finitely
   many representatives and finitely many equalities to a common stage. The stage
   sheaf equalizer supplies a unique glued section. The empty cover covers only the
   empty scheme, whose section set is a singleton (and whose module is zero).
3. Extend this basis sheaf to the full site. Given F -> nu_*G, compose at every
   stage with restriction G(U_i) -> G(U). Finite presentation factors maps through
   stages; eventual equality makes these maps independent of factorization and of
   presentation, and proves naturality. Conversely restrict a map P(F) -> G to
   affine etale finite-presentation objects. The affine etale site determines the
   sheaf morphism. Constant presentations and stage representatives show that the
   two constructions are inverse. The comparison adjunction identifies P with
   nu^*, naturally in F and in basis objects. In modules all maps respect scalars.
   Its unit yields exactly the displayed colimit cocone. The sets argument uses
   the set-valued continuity and restriction lemmas with the same finite-limit
   calculation. -/
theorem proEtaleComparisonSectionsModules {X : Scheme.{u}} [IsAffine X]
    (U : X.AffineProEt) (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ e :
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
        sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
          (evaluation X.ProEtᵒᵖ (ModuleCat.{u + 1} Λ)).obj
            (op ((Scheme.AffineProEt.toProEt X).obj U)) ≅
      Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom ⋙
        sheafToPresheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
          (evaluation U.left.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj
            (op (Scheme.Etale.mk (𝟙 U.left))),
      ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
        (D : I ⥤ X.Etale) [∀ i, IsAffine (D.obj i).left]
        (π : (Functor.const I).obj ((Scheme.AffineProEt.toProEt X).obj U) ⟶
          D ⋙ Scheme.toProEt X),
        IsLimit (Cone.mk U.left
          (Functor.whiskerRight π (Scheme.ProEt.forget X ⋙ Over.forget X))) →
        ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
          Nonempty (IsColimit (proEtaleComparisonSectionsCocone D
            ((Scheme.AffineProEt.toProEt X).obj U) π F
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F)
            ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F))) ∧
          ∀ i : I,
            (proEtaleComparisonSectionsCocone D
              ((Scheme.AffineProEt.toProEt X).obj U) π F
              ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F)
              ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F)).ι.app (op i) ≫
                e.hom.app F =
              proEtaleBasisPulledBackSection U (D.obj i) (π.app i) F
                ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F)
                ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.hom).unit.app F) := by
  sorry

/-- The section formula for sheaves of sets.
The first equality is a natural isomorphism in the sheaf. The second equality says
that the canonical unit-and-restriction cocone for every affine etale
finite-presentation presentation is a colimit, so the identification uses the
restriction transition maps, rather than an unspecified bijection.
Source: blueprint, comparison-sections, statement and both proof paragraphs
(blueprint: lem-weil-pbc-comparison-sections).

Proof:
1. On an affine basis object put P(F)(U) = Gamma(U_et, F|U), where restriction is
   scheme inverse image. Pass to a cofinal upper tail of the presentation. Apply
   lem-weil-pbc-etale-section-continuity (respectively its sets version) to the
   terminal etale object; the inverse-image-restriction lemmas identify its stage
   sections with F(U_i), with their actual restriction maps.
2. By lem-weil-pbc-ind-etale-basis it suffices to check finite basis covers.
   Ind-etale stability presents each covering member by affine etale stages.
   Every tuple of stages still covers, and fibre products commute with these limits.
   Apply continuity to the members and their pairwise fibre products. Move finitely
   many representatives and finitely many equalities to a common stage. The stage
   sheaf equalizer supplies a unique glued section. The empty cover covers only the
   empty scheme, whose section set is a singleton (and whose module is zero).
3. Extend this basis sheaf to the full site. Given F -> nu_*G, compose at every
   stage with restriction G(U_i) -> G(U). Finite presentation factors maps through
   stages; eventual equality makes these maps independent of factorization and of
   presentation, and proves naturality. Conversely restrict a map P(F) -> G to
   affine etale finite-presentation objects. The affine etale site determines the
   sheaf morphism. Constant presentations and stage representatives show that the
   two constructions are inverse. The comparison adjunction identifies P with
   nu^*, naturally in F and in basis objects. In modules all maps respect scalars.
   Its unit yields exactly the displayed colimit cocone. The sets argument uses
   the set-valued continuity and restriction lemmas with the same finite-limit
   calculation. -/
theorem proEtaleComparisonSectionsSets {X : Scheme.{u}} [IsAffine X]
    (U : X.AffineProEt) :
    ∃ e :
      Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X) ⋙
        sheafToPresheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⋙
          (evaluation X.ProEtᵒᵖ (Type (u + 1))).obj
            (op ((Scheme.AffineProEt.toProEt X).obj U)) ≅
      Scheme.etaleSetPullback U.hom ⋙
        sheafToPresheaf U.left.smallEtaleTopology (Type (u + 1)) ⋙
          (evaluation U.left.Etaleᵒᵖ (Type (u + 1))).obj
            (op (Scheme.Etale.mk (𝟙 U.left))),
      ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
        (D : I ⥤ X.Etale) [∀ i, IsAffine (D.obj i).left]
        (π : (Functor.const I).obj ((Scheme.AffineProEt.toProEt X).obj U) ⟶
          D ⋙ Scheme.toProEt X),
        IsLimit (Cone.mk U.left
          (Functor.whiskerRight π (Scheme.ProEt.forget X ⋙ Over.forget X))) →
        ∀ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
          Nonempty (IsColimit (proEtaleComparisonSectionsCocone D
            ((Scheme.AffineProEt.toProEt X).obj U) π F
            ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F)
            ((Scheme.proEtaleSiteComparison X).unit.app F))) ∧
          ∀ i : I,
            (proEtaleComparisonSectionsCocone D
              ((Scheme.AffineProEt.toProEt X).obj U) π F
              ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F)
              ((Scheme.proEtaleSiteComparison X).unit.app F)).ι.app (op i) ≫
                e.hom.app F =
              proEtaleBasisPulledBackSection U (D.obj i) (π.app i) F
                ((Scheme.etaleSetPullback U.hom).obj F)
                ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
                  (MorphismProperty.Over.pullback @Etale ⊤ U.hom) (Type (u + 1)) _
                  (X.smallGrothendieckTopology @Etale)
                  (U.left.smallGrothendieckTopology @Etale)
                  (Etale.isContinuous_overPullback U.hom) _ _).unit.app F) := by
  sorry

end AlgebraicGeometry
