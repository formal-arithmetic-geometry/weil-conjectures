module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
@[expose] public section
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
/-!
# Composition of local finite-free refinements

The theorem packages the categorical composition of the original presentation cover
with a chosen refinement over each member.
-/
/-- Compose local finite-free refinements into one pro-etale cover.

Source: Stacks Project, Sites, covering composition; RefactorInstruction.tex, Section 4
(blueprint: lem-weil-pbc-condensed-qbar-cover-composition).
The covering presieve is the indexed composition of the original presieve with each
local presieve; the finite-free isomorphisms are carried along the composite maps. -/
theorem exists_condensedQbar_refinement_of_local
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hC : ∀ (i : 𝒰.I₀), ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (𝒰.X i),
      ∀ (j : C.I₀), ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          (C.f j ≫ 𝒰.f i)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X j)) r)) :
    ∃ 𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒲.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (𝒲.f i)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (𝒲.X i)) r) := by
  sorry
end AlgebraicGeometry.ProEtale
