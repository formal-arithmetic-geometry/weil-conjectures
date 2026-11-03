/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryModel.CoordinateBoundaryGeometricPullbackDefs
import all WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
import all WeilConjectures.CategoryTheory.Derived.DerivedInjectiveBoundary

/-! # Normalized module support boundaries
Source: the injective construction in Milne Theorem 9.4, as formalized in
`exists_support_longExact`. No etale/pro-etale comparison theorem is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A monomorphism in a small site has a snake-normalized module support boundary.
Source: Milne Theorem 9.4; Stacks Tags 0117 and 05TI.
Proof: restriction of an injective module sheaf along a monomorphism is epic,
by the free-module-on-representables argument used in `exists_support_longExact`.
Apply its proved generic injective-boundary construction. The resulting boundary
on the whole derived category has exactly the canonical model normalization;
restrict it along the full subcategory with predicate true.
(blueprint: aux-lem-pur-coordinate-normalized-boundary-exists). -/
theorem coordinate_normalized_boundary_exists
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {V W : C} (j : W ⟶ V) [Mono j] :
    ∃ δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤,
      supportBoundaryNormalization J A j δ := by
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} A)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have he (I : Sheaf J (ModuleCat.{u + 1} A)) [Injective I] :
      Epi (I.obj.map j.op) := supportModule_restriction_epi.{u + 1, u, u + 1} J A I j
  obtain ⟨d, hd⟩ := Sheaf.supportBoundary_exists.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
    J (ModuleCat.{u + 1} A) j he
  refine ⟨fun q ↦ Functor.whiskerLeft
    (⊤ : ObjectProperty (DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A)))).ι (d q), ?_⟩
  intro I hI
  let S := Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j
  let F := sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op V)
  let G := sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)
  let ι := Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j
  let π := (sheafSections J (ModuleCat.{u + 1} A)).map j.op
  let w := Sheaf.supportRow_zero J (ModuleCat.{u + 1} A) j
  let h := Sheaf.supportRow_shortExact J (ModuleCat.{u + 1} A) j he
  let R := Functor.injectiveBoundaryRow S F G ι π w I
  have hR := Functor.injectiveBoundaryRow_shortExact S F G ι π w h I
  refine ⟨R.zero, hR, ?_⟩
  intro q
  convert hd I (DerivedCategory.Plus.Q.obj I) (Iso.refl _) q using 1; rfl

end AlgebraicGeometry
