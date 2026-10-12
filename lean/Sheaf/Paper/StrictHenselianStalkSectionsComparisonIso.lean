module

public import Sheaf.Paper.EtaleObjectCohomologyStalkComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Degree-zero continuity for the specified inverse image -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Degree-zero continuity compares stalk sections with the inverse image specified
by its adjunction to direct image, rather than with an arbitrary functor.
Source: Stacks Project, Tag 03Q6, degree zero and proof steps (1)-(3).
(blueprint: new-strict-henselian-stalk-sections-comparison-iso)

Proof: The forgetful functor in hi_inclusion lands in Over X, not just Scheme.
Its object equalities therefore identify both the underlying schemes and the structural
maps of i(U) with those of the canonical open inclusions U into X. Its arrow equalities
identify the restriction maps. Applying each sheaf yields a natural identification of
the neighbourhood diagram with sections on the canonical open objects. Choose an affine
neighbourhood V of x. Principal affine neighbourhoods of x inside V are cofinal: every
neighbourhood intersects V in an open containing x, hence contains such a principal
open. Their coordinate-ring colimit is the local ring at x. Apply Tag 03Q6 with base V,
which is quasi-compact and quasi-separated, and the sheaf restricted to V. In degree zero,
descent of sections gives surjectivity of the map from the colimit of sections to
local-scheme sections; descent of equality gives injectivity. These maps respect addition
and sheaf morphisms, giving a natural group isomorphism with sections of inverse image
along X.fromSpecStalk x. The standard inverse image and H are left adjoints to the same
displayed direct image, so uniqueness of left adjoints identifies them naturally.
Whiskering with terminal sections gives the conclusion. Small affine presentations
preserve the coefficient universe. Empty X has no x, and no henselian assumption is used. -/
theorem strictHenselian_stalkSections_comparison_iso
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology
      (Spec (X.presheaf.stalk x)).smallEtaleTopology) :
    Nonempty (etaleObjectStalkSections X i x ≅
      H ⋙ (sheafSections (Spec (X.presheaf.stalk x)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 _)))) := by sorry
