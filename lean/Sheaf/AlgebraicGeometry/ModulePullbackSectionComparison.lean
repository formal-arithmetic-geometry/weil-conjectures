/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison

/-! # Forgetting module coefficients in canonical pullback section comparisons

Source: Stacks Project, Sites, Tags 00X6, 00YV, 03CB, and 03CC, and module inverse
image, Tags 03D3 and 03D7.
(blueprint: lem-weil-pbc-module-pullback-section-comparison). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The underlying sections of a module inverse image identify with those of the
set inverse image, compatibly with the canonical unit/composition maps. There is no
scheme limit, directed index, or colimit assertion in this comparison.

Source: Stacks Project, Sites, Tags 00X6, 00YV, 03CB, and 03CC; module inverse image,
Tags 03D3 and 03D7.
(blueprint: lem-weil-pbc-module-pullback-section-comparison)

Proof: Start with the abelian inverse image and its unit-compatible underlying-set
comparison. For a module sheaf G, let λ_r be its scalar-r endomorphism. Give the
abelian inverse image the scalar maps obtained by applying abelian inverse image
to λ_r. Additivity preserves λ_(r+r') = λ_r + λ_r', and functoriality preserves
λ_(rr') = λ_r ≫ λ_r', λ_1 = identity, and λ_0 = zero. Thus these maps give a sheaf
of Λ-modules. Naturality of the abelian unit and counit makes both Λ-linear.
The abelian adjunction restricts to Λ-linear maps: its hom-set bijection takes
precomposition with λ_r to precomposition with its inverse image, and
postcomposition with λ_r to postcomposition with its direct image. Consequently
the transported module inverse image is left adjoint to the recorded module
direct image. Uniqueness of left adjoints identifies it with upperStar of
ModuleCat, compatibly with the unit. Compose this comparison with the abelian-to-set
comparison and evaluate at the base change of U to obtain the equivalences e.
Direct images are precomposition and commute with forgetting on the nose. Their
composition comparisons are restriction along the same fibre-product pasting
isomorphism. The inverse-image composition comparison is the unique mate of that
direct-image comparison, determined by its unit equation. Therefore forgetting
carries it to the set composition comparison chosen in
etaleSetInverseImageCompositionUnits. Naturality in the sheaf and the site object
identifies the unit, the composition comparison, and the restriction along the
pasting isomorphism factor by factor. These are the three factors defining
etaleSetSectionComparison and the displayed module composite, giving the equation.
Transport along hk uses the same equality on both sides.

Edge cases: identities give the same identity/unit comparison. Empty objects and
the zero module sheaf have singleton underlying section sets, so the equation
still holds. No affineness, quasi-compactness, torsion, or finite-generation
assumption is needed. -/
theorem exists_modulePullbackSectionComparison
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : ∀ (Y : Scheme.{u}) (f : Y ⟶ X) (U : X.Etale),
      (((lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)).obj.obj (op U)) ≃
      (((Scheme.etaleSetPullback f).obj
        ((sheafForget X.smallEtaleTopology).obj G)).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))),
      ∀ (Y Z : Scheme.{u}) (h : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X)
        (hk : h ≫ f = k) (U : X.Etale)
        (s : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
          ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)).obj.obj (op U)),
        e Z k U
          ((((lowerStar (ModuleCat.{u + 1} Λ) f).map
            ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
              ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)) ≫
            (lowerStarComp (ModuleCat.{u + 1} Λ) h f k hk.symm).hom.app _ ≫
            (lowerStar (ModuleCat.{u + 1} Λ) k).map
              ((upperStarComp (ModuleCat.{u + 1} Λ) h f k hk.symm).inv.app G)).hom.app
                (op U)) s) =
          etaleSetSectionComparison h f k hk
            ((sheafForget X.smallEtaleTopology).obj G) U (e Y f U s) := by sorry

end AlgebraicGeometry.Etale
