/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Curve
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Descent of constructibility along a finite direct image

For a finite morphism `f : X ⟶ Y` the counit `f^* f_* F ⟶ F` is an epimorphism
(`AlgebraicGeometry.Etale.epi_counit_app_of_isFinite`): on the stalk at a geometric point `x` of
`X` with algebraically closed residue field it is the projection of
`(f_* F)_{f x} ≅ ∏_{t ↦ f x} F_t` onto the factor `x`. Consequently, if `X` is noetherian and
`f_* F` is constructible, so is `F`, being a quotient of the constructible sheaf `f^* f_* F`
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_isConstructibleSheaf_lowerStar`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

open Scheme Scheme.Hom

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- For a finite morphism `f`, the stalk of the counit `f^* f_* G ⟶ G` at a geometric point of
`X` with algebraically closed residue field is an epimorphism: through the identification of
the stalk of `f^* f_* G` at `s` with `(f_* G)_{s ≫ f}`, it is a component of the isomorphism of
the finite stalk formula, i.e. a product projection. -/
lemma Etale.epi_sheafFiber_map_counit_app_of_isFinite {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (G : Sheaf X.smallEtaleTopology A) :
    Epi ((pointSmallEtale s).sheafFiber.map
      ((Etale.upperStarLowerStarAdjunction A f).counit.app G)) := by
  have h := Etale.stalkRestrict_eq_counit A f s G
  rw [← Iso.app_inv, Iso.eq_inv_comp] at h
  rw [← h]
  have : Etale.stalkRestrict A f (s ≫ f) ⟨s, rfl⟩ G =
      (Etale.stalkIsoPi A f (s ≫ f) G).hom ≫ Pi.π _ ⟨s, rfl⟩ := by
    simp
  rw [this]
  classical
  infer_instance

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- **For a finite morphism `f`, the counit `f^* f_* G ⟶ G` is an epimorphism**: the geometric
points `AlgebraicGeometry.Scheme.algClosurePoint x` of `X` jointly reflect epimorphisms, and the
counit is an epimorphism on the stalk at each of them
(`AlgebraicGeometry.Etale.epi_sheafFiber_map_counit_app_of_isFinite`). -/
instance Etale.epi_counit_app_of_isFinite (G : Sheaf X.smallEtaleTopology A) :
    Epi ((Etale.upperStarLowerStarAdjunction A f).counit.app G) := by
  refine (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale X A).epi_of_epi_map _ ?_
  rintro ⟨-, ⟨x⟩⟩
  have : Epi (((pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber.map
      ((Etale.upperStarLowerStarAdjunction A f).counit.app G)) := by
    rw [← NatIso.naturality_2 ((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso A)
      ((Etale.upperStarLowerStarAdjunction A f).counit.app G)]
    have := Etale.epi_sheafFiber_map_counit_app_of_isFinite A f (X.algClosurePoint x) G
    exact epi_comp _ _
  exact this

namespace Scheme

variable {A} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

/-- **A sheaf whose finite direct image is constructible is constructible.** Let `f : X ⟶ Y` be
a finite morphism with `X` noetherian (for instance a curve over a field,
`AlgebraicGeometry.IsCurve.isNoetherian`), `Λ` a noetherian ring and `F` an étale sheaf of
`Λ`-modules on `X`. If `f_* F` is constructible, so is `F`: the pullback `f^* f_* F` is
constructible (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.upperStar`), the counit
`f^* f_* F ⟶ F` is an epimorphism (`AlgebraicGeometry.Etale.epi_counit_app_of_isFinite`), and a
quotient of a constructible sheaf on a noetherian scheme is constructible, being the cokernel of
the inclusion of a constructible subsheaf
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono`,
`AlgebraicGeometry.Scheme.IsConstructibleSheaf.cokernel`).
(blueprint: `lem-weil-pbc-finite-pushforward-constructible-descent`) -/
theorem IsConstructibleSheaf.of_isConstructibleSheaf_lowerStar
    [TopologicalSpace.NoetherianSpace X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)] :
    IsConstructibleSheaf F := by
  let ε : (Etale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F
      ⟶ F := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F
  have : IsConstructibleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙
      Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) :=
    IsConstructibleSheaf.upperStar f _
  have : IsConstructibleSheaf (kernel ε) := IsConstructibleSheaf.of_mono (kernel.ι ε)
  have := IsConstructibleSheaf.cokernel (kernel.ι ε)
  exact IsConstructibleSheaf.of_iso (F := cokernel (kernel.ι ε))
    ((cokernelIsCokernel _).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel ε)))

end Scheme

/-- **A sheaf on a curve whose finite direct image to a curve is constructible is
constructible.** Let `X` be a curve over a field `k`, `f : X ⟶ Y` a finite morphism and `F` an
étale sheaf of modules over a noetherian ring on `X`. If `f_* F` is constructible, so is `F`.
(blueprint: `lem-weil-pbc-finite-pushforward-constructible-descent`) -/
theorem IsCurve.isConstructibleSheaf_of_isConstructibleSheaf_lowerStar {Λ : Type (u + 1)}
    [CommRing Λ] [IsNoetherianRing Λ] {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [IsCurve p]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)] :
    IsConstructibleSheaf F :=
  have := IsCurve.isNoetherian p
  IsConstructibleSheaf.of_isConstructibleSheaf_lowerStar f F

end AlgebraicGeometry
