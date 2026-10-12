/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.Paper.EtaleRestrictionPullbackUnit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Canonical sections of inverse images along an inverse system -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Continuity for a cocone whose arrows and legs are the canonical pullback section maps.
The diagram and its coherence are supplied as hypotheses; the conclusion is solely its
universal property, rather than the elementwise clauses of the parent statement.

Source: Stacks Project, Etale Cohomology, Theorem 09YQ (theorem-colimit), degree zero,
as applied in Lemma 09YU (lemma-category-is-colimit), proof, Fully faithful.
(blueprint: lem-weil-pbc-pullback-sections-is-colimit)

Proof: Restrict the scheme diagram to the directed tail i >= i0, which is nonempty
and cofinal, with the same limit. Base change every stage along V0 -> X_i0. The resulting
V_i and V are affine, since the transitions and limit projections are affine and V0 is
affine; base change of the scheme limit identifies V with their inverse limit. Put
w_i : V_i -> X_i0 and F_i = w_i inverse image of G. Their composition comparisons give
transition isomorphisms. On V these sheaves all identify with w inverse image of G;
associativity identifies the transitions with identities. The constant connected diagram
has that sheaf as its colimit. Forget to abelian sheaves, compatibly with inverse-image
units and composition, and apply Theorem 09YQ in degree zero. The natural degree-zero
cohomology/global-section comparison gives a colimit of the section groups. The etale
restriction isomorphisms identify these groups with S_i, and the cartesian-square
restriction/unit equation identifies their arrows and legs with mu and tau. The displayed
e_i and eB therefore transport this colimit cocone to B. Finally module filtered colimits
are created on underlying abelian groups (scalar multiplication is induced stagewise),
so B is a colimit also in ModuleCat. None of the elementwise colimit criterion is used. -/
theorem nonempty_isColimit_pullbackSections
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (Λ : Type (u + 1)) [CommRing Λ] (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V₀ : (D.obj (op i₀)).Etale) [IsAffine V₀.left] :
    let J := {i : I // i₀ ≤ i}
    let S : J → ModuleCat.{u + 1} Λ := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)).obj.obj
          (op V₀)
    let T : ModuleCat.{u + 1} Λ := ((lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj
      ((upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj G)).obj.obj (op V₀)
    let μ : ∀ {i j : J}, (i ⟶ j) → (S i ⟶ S j) := fun {i j} f ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ)
          (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
          (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE j.property).op)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
            (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀)
    let τ : ∀ i : J, S i ⟶ T := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
          (D.map (homOfLE i.property).op) (c.π.app (op i₀))
          (c.w (homOfLE i.property).op).symm).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
            (D.map (homOfLE i.property).op) (c.π.app (op i₀))
            (c.w (homOfLE i.property).op).symm).inv.app G)).hom.app (op V₀)
    ∀ (F : J ⥤ ModuleCat.{u + 1} Λ) (B : Cocone F)
      (e : ∀ i : J, F.obj i ≅ S i) (eB : B.pt ≅ T),
      (∀ (i j : J) (f : i ⟶ j), (e i).inv ≫ F.map f ≫ (e j).hom = μ f) →
      (∀ i : J, (e i).inv ≫ B.ι.app i ≫ eB.hom = τ i) → Nonempty (IsColimit B) := by
  sorry

end AlgebraicGeometry.Etale
