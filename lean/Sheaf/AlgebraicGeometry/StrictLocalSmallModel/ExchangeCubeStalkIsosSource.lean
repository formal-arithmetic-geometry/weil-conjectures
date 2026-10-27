/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison

/-! # Invertibility of the canonical strict-local stalk comparisons

Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

set_option linter.unusedVariables false in
/-- The fixed source cube restriction map is invertible on the indicated closed-point
stalk. This says nothing about either exchange map or compatibility with exchange.
Source: Stacks Project, Tag 03Q9, theorem-higher-direct-images, and Tag 03QO,
lemma-cohomology-strictly-henselian.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source).

Proof: compose eA and eB with Spec of the inverse canonical small-to-full colimit
isomorphisms. Their structural-map equations identify the resulting maps into S and T
with the original maps jA and jB. Transport the given point equations and cartesian
squares along these equalities, and apply the adopted full-model source comparison
theorem. The conclusion involves only jA and jB, not the chosen presentations, so the
same equalities give the stated small-model comparison. Proof irrelevance identifies
the commutativity witnesses in the cube map. This includes degree zero, zero sheaves,
empty total spaces and all the specified cartesian models without extra hypotheses. -/
theorem Etale.smallModel_isIso_strictHenselization_exchangeCube_stalkComparisons_source
    {S T X X' : Scheme.{u}} {g : T ⟶ S} {f : X ⟶ S}
    [QuasiCompact f] [QuasiSeparated f] {f' : X' ⟶ T} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    {X₀ X₁ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))
    (p₁ : X₁ ⟶ X₀) (f₁ : X₁ ⟶ Spec (.of B))
    (sq₁ : IsPullback p₁ f₁ f₀ (Spec.map (CommRingCat.ofHom φ)))
    (b : X₁ ⟶ X')
    (sqB : IsPullback b f₁ f'
      (eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ)))
    (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let jA := eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)
    let jB := eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ)
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    let ht : t ≫ jB = τ := by simpa only [t, jB, Category.assoc] using hρB
    let h : jB ≫ g = g₀ ≫ jA := by simpa only [jB, g₀, jA, Category.assoc] using hφ.symm
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
    let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f')_*[AddCommGrpCat.{u + 1}])).obj K
    let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
    let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀
    IsIso (derivedStalkComparison jB t τ ht M₁ N₁
      (exchangeCubeSourceComparison sq₀.toCommSq h G) (q : ℤ)) := by
  let eA' : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ) :=
    eA ≪≫ Scheme.Spec.mapIso (smallStrictHenselizationColimitIso (ν ≫ ι ≫ σ)).symm.op
  let eB' : Spec (.of B) ≅ strictLocalization (ν ≫ τ) :=
    eB ≪≫ Scheme.Spec.mapIso (smallStrictHenselizationColimitIso (ν ≫ τ)).symm.op
  have hA : eA'.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) =
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) := by
    change (eA.hom ≫ Spec.map (smallStrictHenselizationColimitIso _).inv) ≫ _ = _
    rw [Category.assoc, smallStrictHenselizationColimitIso_toBase]
  have hB : eB'.hom ≫ strictLocalizationToBase (ν ≫ τ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) := by
    change (eB.hom ≫ Spec.map (smallStrictHenselizationColimitIso _).inv) ≫ _ = _
    rw [Category.assoc, smallStrictHenselizationColimitIso_toBase]
  have transfer (jA : Spec (.of A) ⟶ S) (jB : Spec (.of B) ⟶ T)
      (hjA : eA'.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = jA)
      (hjB : eB'.hom ≫ strictLocalizationToBase (ν ≫ τ) = jB)
      (hφ : Spec.map (CommRingCat.ofHom φ) ≫ jA = jB ≫ g)
      (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ jA = σ)
      (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ jB = τ)
      (sq₀ : IsPullback p₀ f₀ f jA) (sqB : IsPullback b f₁ f' jB) :
      let g₀ := Spec.map (CommRingCat.ofHom φ)
      let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
      let ht : t ≫ jB = τ := by simpa only [t, Category.assoc] using hρB
      let h : jB ≫ g = g₀ ≫ jA := hφ.symm
      let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
      let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
        (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
      let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
      let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
      IsIso (derivedStalkComparison jB t τ ht M₁ N₁
        (exchangeCubeSourceComparison sq₀.toCommSq h G) (q : ℤ)) := by
    subst jA jB
    exact isIso_strictHenselization_exchangeCube_stalkComparisons_source
      sq σ τ ι hι ν eA' eB' φ ρA ρB (by simpa only [Category.assoc] using hφ)
      hρA hρB hρ p₀ f₀ sq₀ p₁ f₁ sq₁ b sqB hb G q
  exact transfer _ _ hA hB (by simpa only [Category.assoc] using hφ)
    hρA hρB sq₀ sqB

end AlgebraicGeometry
