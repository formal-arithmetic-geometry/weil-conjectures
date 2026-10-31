/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateLocalLine
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# Local bases of the first condensed Tate twist

Source: Bhatt–Scholze, The pro-étale topology for schemes, Section 6.8, and the
Tate-twist unit of the current blueprint.
(blueprint: lem-poincare-first-twist-pullback-local-line)
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private def freeUnitIso (R : C) [MonObj R] : (free R).obj (𝟙_ C) ≅ regular R :=
  isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ C)).inv ≫ μ[R] ▷ (𝟙_ C)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    rw [Category.assoc, rightUnitor_naturality]
    monoidal)

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

private noncomputable def extendFreeIso : free R ⋙ extendScalars φ ≅ free S :=
  ((freeForgetAdjunction R).comp (extendRestrictAdjunction φ)).leftAdjointUniq
    (freeForgetAdjunction S)

private noncomputable def extendRegularIso : (extendScalars φ).obj (regular R) ≅ regular S :=
  (extendScalars φ).mapIso (freeUnitIso R).symm ≪≫
    (extendFreeIso φ).app (𝟙_ C) ≪≫ freeUnitIso S

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

private noncomputable def pullExtendIso
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    (upperStar Ab.{u + 1} f).mapMod R ⋙
        Mod.extendScalars ((upperStar Ab.{u + 1} f).map a) ≅
      Mod.extendScalars a ⋙ (upperStar Ab.{u + 1} f).mapMod S := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  exact Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} f).map a))
    (Mod.extendRestrictAdjunction a)
    (adj.mapModAdjunction R) (adj.mapModAdjunction S)
    (Mod.comapMapModComapIso (lowerStar Ab.{u + 1} f)
      ((upperStar Ab.{u + 1} f).map a) a
      (adj.unitAlgHom R) (adj.unitAlgHom S) (adj.unit.naturality a))

/-- The first Tate twist, after inverse image, has a pro-étale local basis.

Source: the current blueprint, `sk-def-sp-tate-twist`, integral limit and coefficient
extension; Bhatt–Scholze, Section 6.8.

Proof: take a cover trivializing the pulled-back integral Tate module. Inverse image
commutes with extension of scalars: conjugate the commutative square for restriction of
scalars under the two monoidal pullback adjunctions. Apply this comparison first to `f`
and then to each member of the cover. Extension of scalars sends the regular integral
module to the regular rational module, by uniqueness of the free-module left adjoint.
Compose these isomorphisms with the integral basis isomorphism.
(blueprint: lem-poincare-first-twist-pullback-local-line) -/
theorem tateTwistOne_pullback_locally_trivial
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    {Y : Scheme.{u}} (f : Y ⟶ X) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : 𝒰.I₀,
      Nonempty
        ((((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          ((upperStar Ab.{u + 1} f).obj
            (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))).obj
          (((upperStar Ab.{u + 1} f).mapMod
            (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj
              (tateTwistOne X ℓ))) ≅ 𝟙_ _) := by
  obtain ⟨𝒰, h𝒰⟩ := tateModule_pullback_locally_trivial X ℓ hℓ f
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨e⟩ := h𝒰 i
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X
  let S := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
  let a := coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X
  let F := upperStar Ab.{u + 1} f
  let G := upperStar Ab.{u + 1} (𝒰.f i)
  let E := Mod.extendScalars (G.map (F.map a))
  exact ⟨(G.mapMod (F.obj S)).mapIso ((pullExtendIso f a).symm.app (tateModule X ℓ)) ≪≫
    (pullExtendIso (𝒰.f i) (F.map a)).symm.app ((F.mapMod R).obj (tateModule X ℓ)) ≪≫
    E.mapIso e ≪≫ CategoryTheory.Mod.extendRegularIso (G.map (F.map a))⟩

end AlgebraicGeometry.ProEtale
