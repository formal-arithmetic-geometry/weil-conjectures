/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleEventualHomLift
import WeilConjectures.AlgebraicGeometry.ConstructibleAffineFreePresentationGeneral
import WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison
import WeilConjectures.Mathlib.CategoryTheory.Functor.FullyFaithful
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Eventual lifting of morphisms out of constructible sheaves along surjective limits

Source: Stacks Project, Lemma 09YU (3), proof, paragraph "Fully faithful".
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Let `D` be a directed inverse system of qcqs schemes with affine transitions, `c` a limit
cone whose projections are surjective, and `Λ` Noetherian. A morphism `π_i^* F ⟶ π_i^* G` on the
limit, with `F` constructible at stage `i`, comes from a morphism `t^* F ⟶ t^* G` at some later
stage `j`, compatibly with the canonical composition isomorphisms.

Source: Stacks Project, Lemma 09YU (3), proof, paragraph "Fully faithful".

Proof: choose an epimorphism onto `F` from a finite sum `A` of extensions by zero of constant
rank-one sheaves on affine etale objects (Tag 095N and the comparison of free etale modules with
extensions by zero). The composite `π_i^* A ⟶ π_i^* F ⟶ π_i^* G` lifts to a later stage by
`exists_affine_free_etaleModule_eventual_hom_lift`. The pullback along the surjective projection
`π_j` is faithful, so the lift kills the pullback of the kernel of `A ⟶ F`, and therefore
descends through the cokernel `t^* A ⟶ t^* F`. -/
theorem exists_constructible_etaleModule_eventual_hom_lift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (hsurj : ∀ i, Function.Surjective (c.π.app i).base)
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (i : I) (F G : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F]
    (φ : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj F ⟶
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj G) :
    ∃ (j : I) (h : i ≤ j)
      (a : (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj F ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G),
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op j))).map a ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
            (D.map (homOfLE h).op) (c.π.app (op i)) (c.w (homOfLE h).op).symm).inv.app G =
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
          (D.map (homOfLE h).op) (c.π.app (op i)) (c.w (homOfLE h).op).symm).inv.app F ≫ φ := by
  classical
  obtain ⟨n, m, U, V, hU, hV, f, g, w, ⟨hg⟩⟩ :=
    exists_affine_free_etale_presentation_general (D.obj (op i)) Λ F
  have : Epi g := epi_of_isColimit_cofork hg
  let e (k : Fin n) := Classical.choice (free_etale_module_shriek_comparison _ Λ (U k))
  let g' := (Sigma.mapIso fun k ↦ (e k).symm).hom ≫ g
  obtain ⟨j, h, a₀, ha₀⟩ := exists_affine_free_etaleModule_eventual_hom_lift D c hc Λ i n U hU G
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).map g' ≫ φ)
  have := Etale.faithful_upperStar_of_surjective Λ (c.π.app (op j)) (hsurj _)
  exact ⟨j, h, Functor.exists_map_comp_inv_app_eq_of_epi _ _ _ _ g' φ a₀ ha₀⟩

end AlgebraicGeometry.Scheme
